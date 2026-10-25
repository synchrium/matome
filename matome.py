"""まとめサイトをターミナルで読む TUI。

キー操作は vim 風。画像は sixel / Kitty 対応端末ならインラインで表示する。
サイトは sites.toml に RSS の URL を書くか、サイト一覧で a を押して追加する。
"""

from __future__ import annotations

import argparse
import asyncio
import io
import json
import re
import math
import os
import shlex
import shutil
import subprocess
import sys
import time
import unicodedata
import webbrowser
from collections import OrderedDict
from collections.abc import Callable
from pathlib import Path
from types import SimpleNamespace
from urllib.parse import urlparse

# textual_image は import 時に端末へ問い合わせて描画方式を決める。
# Textual の起動後だと問い合わせられないので、必ず App より先に import する。
from textual_image.widget import Image
from textual_image._terminal import get_cell_size

import httpx
from PIL import Image as PILImage
from rich.cells import cell_len
from rich.control import Control
from rich.segment import ControlType, Segment
from rich.style import Style
from rich.text import Text
from textual import events, work
from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.containers import Grid, ScrollableContainer, Vertical, VerticalScroll
from textual.css.query import NoMatches
from textual.screen import ModalScreen, Screen
from textual.strip import Strip
from textual.widget import MountError, Widget
from textual.widgets import Footer, Header, Input, Label, ListItem, ListView, OptionList, Rule, Static

import feeds

STATE_FILE = feeds.STATE_DIR / "read.json"
MAX_IMAGE_CELLS = 80  # 画像の最大幅（桁数）
MAX_IMAGE_HEIGHT = 0.3  # 画像の最大の高さ（本文の枠の高さに対する割合）。枠ぎりぎりだと窮屈なので少し余らせる

# sixel は 256 色に減色する。textual-image はディザをかけないので肌などのグラデーションに色のムラが出る。
# ディザの設定が無いので、減色の関数を差し替える（内部の関数なので、無くなっていたら何もしない）
try:
    import textual_image._sixel as _sixel

    _plain_quantize = _sixel._quantize_rgb_image
    _QUANTIZE_METHODS = _sixel._QUANTIZE_METHODS
except (ImportError, AttributeError):
    _sixel = None


DITHER_MIN_PIXELS = 300 * 300  # これより小さい画像（画像一覧のタイルなど）はディザをかけない


def _dithered_quantize(image: PILImage.Image, options) -> PILImage.Image:
    # 小さい画像ではムラが目立たないわりに、ディザで sixel が 2 割ほど大きく・遅くなる
    if image.width * image.height <= DITHER_MIN_PIXELS:
        return _plain_quantize(image, options)
    palette = image.quantize(colors=options.colors, method=_QUANTIZE_METHODS[options.quantize])
    return image.quantize(palette=palette, dither=PILImage.Dither.FLOYDSTEINBERG)


def _whole_sixel_image(base: type) -> type:
    """一部しか見えていないときは描かない sixel の画像（枠より大きい画像は一部でも描く）。

    textual-image は見えている部分だけを sixel にするので、画面の端の画像はスクロールの
    たびに作り直して送り直す（1 枚 50〜200ms、SSH ごしだと送るのも重い）。
    sixel 以外（Kitty・文字の近似）や、内部の作りが変わったときは base をそのまま使う。
    """
    try:
        import textual_image.widget.sixel as sixel_widget

        impl = sixel_widget._ImageSixelImpl
        renderable = sixel_widget._NoopRenderable
    except (ImportError, AttributeError):
        return base
    if base is not sixel_widget.Image:
        return base

    class WholeImpl(impl):
        def render_lines(self, crop):
            try:
                visible = self.screen.find_widget(self).visible_region
            except Exception:
                return super().render_lines(crop)
            # 全体が見えることのある大きさか。画面ではなくスクロールする枠（記事の本文など）の高さで比べる。
            # 画面より低くても枠より高い画像は全体が見えることが無く、ずっと描かれなくなる
            box = next((w for w in self.ancestors if isinstance(w, ScrollableContainer)), None)
            box_h = box.scrollable_content_region.height if box is not None else self.screen.size.height
            fits = self.size.height <= min(self.screen.size.height, box_h)
            hold = getattr(self.parent, "hold", False)  # まだ描かない（拡大表示を開いた直後）
            if hold or (visible.size != self.size and fits):
                _, color = self.background_colors
                blank = Strip.blank(crop.width, Style(bgcolor=color.rich_color))
                return [blank] * crop.height
            return super().render_lines(crop)

        def _get_sixel_segments(self, sixel_data: str):
            # textual-image は sixel のあとカーソルを画像の 1 つ下の行（visible_region.bottom）へ
            # 動かすが、sixel は画像の最後の行の中に入っているので、Textual が同じ行の残り
            # （画像より右の枠やスクロールバー）を 1 行下に書いてしまい、スクロールバーが
            # 歯抜けになる。画像の最後の行へ戻す
            visible = self.screen.find_widget(self).visible_region
            return [
                Segment(Control.move_to(visible.x, visible.y).segment.text, style=Style()),
                Segment(sixel_data, style=Style(), control=((ControlType.CURSOR_FORWARD, 0),)),
                Segment(Control.move_to(visible.right, visible.bottom - 1).segment.text, style=Style()),
            ]

    class WholeImage(base, Renderable=renderable):
        def compose(self) -> ComposeResult:
            yield WholeImpl(self.image, self._sixel_options)

    return WholeImage


Image = _whole_sixel_image(Image)


def _fix_cell_size() -> None:
    """1 文字の大きさ（ピクセル）の見積もりを直す。

    textual-image は端末の大きさ（ioctl）から 1 文字のピクセル数を割り出すが、WSL2 の
    Windows Terminal から SSH でつなぐと 640×480 という仮の値が来て 4×8 と見誤り、画像が
    枠の 4 割ほどの大きさで描かれる。明らかに小さすぎる値なら、sixel を 1 文字 10×20 と
    みなす Windows Terminal・VT340 の決まりに合わせる。MATOME_CELL_SIZE=10x20 のように指定もできる。
    """
    try:
        import textual_image._terminal as terminal

        caps = terminal.probe_terminal()
    except Exception:
        return
    m = re.fullmatch(r"(\d+)x(\d+)", os.environ.get("MATOME_CELL_SIZE", ""))
    if m:
        size = terminal.CellSize(int(m.group(1)), int(m.group(2)))
    elif caps.cell_size.width < 6 or caps.cell_size.height < 12:
        size = terminal.CellSize(10, 20)
    else:
        return
    setattr(terminal.probe_terminal, "_result", caps._replace(cell_size=size))


_fix_cell_size()


def set_dither(on: bool) -> bool:
    """sixel の減色にディザをかけるかを切り替える。切り替えられなければ False。"""
    if _sixel is None:
        return False
    _sixel._quantize_rgb_image = _dithered_quantize if on else _plain_quantize
    return True


class ReadState:
    """既読管理。URL の集合をファイルに保存するだけ。"""

    def __init__(self) -> None:
        try:
            self.urls: set[str] = set(json.loads(STATE_FILE.read_text()))
        except (OSError, ValueError):
            self.urls = set()

    def mark(self, url: str) -> None:
        if url in self.urls:
            return
        self.urls.add(url)
        STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
        # 古いものから捨てて肥大化を防ぐ
        STATE_FILE.write_text(json.dumps(sorted(self.urls)[-5000:]))


class Settings:
    """画面の表示設定。次に起動したときも同じ表示にするため保存する。"""

    FILE = feeds.STATE_DIR / "settings.json"

    def __init__(self) -> None:
        try:
            data = json.loads(self.FILE.read_text())
        except (OSError, ValueError):
            data = {}
        self.hide_read: bool = bool(data.get("hide_read", False))
        self.group: int = feeds.to_group(data.get("group", 1))  # サイト一覧で最後に見ていたグループ
        self.dither: bool = bool(data.get("dither", True))  # 画像（sixel）の減色にディザをかける
        self.images: bool = bool(data.get("images", True))  # 記事の画像を出す（出さないときは読み込みもしない）
        self.tile_full: bool = bool(data.get("tile_full", False))  # 画像一覧のタイルの画像を枠いっぱいに描く

    def save(self) -> None:
        self.FILE.parent.mkdir(parents=True, exist_ok=True)
        self.FILE.write_text(json.dumps({
            "hide_read": self.hide_read, "group": self.group, "dither": self.dither, "images": self.images,
            "tile_full": self.tile_full,
        }))


class TimingLog:
    """先読みの効き目を調べるための記録。MATOME_LOG=1 で起動したときだけ書く。

    1 行に 1 つの JSON。あとでまとめて集計する（README の「先読み」を参照）。
    """

    FILE = feeds.STATE_DIR / "timing.log"

    def __init__(self) -> None:
        self.on = os.environ.get("MATOME_LOG") == "1"
        self.prefetch = os.environ.get("MATOME_PREFETCH") != "0"

    def write(self, ev: str, **data) -> None:
        if not self.on:
            return
        line = {"t": time.strftime("%Y-%m-%dT%H:%M:%S"), "ev": ev, "prefetch": self.prefetch, **data}
        try:
            self.FILE.parent.mkdir(parents=True, exist_ok=True)
            with self.FILE.open("a", encoding="utf-8") as f:
                f.write(json.dumps(line, ensure_ascii=False) + "\n")
        except OSError:
            pass


PREFETCH_AHEAD = 2  # カーソルの記事のほかに、下（次）の何件を先読みするか
PREFETCH_IMAGES = 8  # 先読みする 1 記事あたりの画像の数
ARTICLE_TTL = 600  # 取った記事を使い回す秒数（コメントが増えるので長くはしない）


class Articles:
    """記事の本文のキャッシュと先読み。

    記事は URL ごとに 1 つの Task にして、記事画面・画像一覧・先読みで共有する。
    先読みは同時に 2 件まで（相手のサイトに負担をかけない）。MATOME_PREFETCH=0 で先読みを止める。
    """

    def __init__(self, app: "MatomeApp") -> None:
        self.app = app
        self.enabled = app.timing.prefetch
        self.tasks: OrderedDict[str, tuple[float, asyncio.Task]] = OrderedDict()
        self.started: set[str] = set()  # 先読みの順番が来て、取りに行き始めたもの
        self.pages = asyncio.Semaphore(2)
        self.images = asyncio.Semaphore(3)

    def _valid(self, url: str) -> asyncio.Task | None:
        hit = self.tasks.get(url)
        if not hit:
            return None
        made, task = hit
        if time.monotonic() - made > ARTICLE_TTL:
            return None
        if task.done() and (task.cancelled() or task.exception()):
            return None
        return task

    def _start(self, entry: feeds.Entry, prefetch: bool) -> asyncio.Task:
        task = asyncio.create_task(self._fetch(entry, prefetch))
        task.add_done_callback(lambda t: t.cancelled() or t.exception())  # 失敗を警告にしない
        self.tasks[entry.url] = (time.monotonic(), task)
        self.tasks.move_to_end(entry.url)
        while len(self.tasks) > 60:
            self.tasks.popitem(last=False)
        return task

    async def _fetch(self, entry: feeds.Entry, prefetch: bool) -> feeds.Article:
        if prefetch:
            async with self.pages:
                self.started.add(entry.url)
                start = time.perf_counter()
                article = await feeds.fetch_article(self.app.http, entry)
            self.app.timing.write("prefetch", url=entry.url, ms=round((time.perf_counter() - start) * 1000))
            if self.app.settings.images:
                asyncio.create_task(self._fetch_images(article))
        else:
            self.started.add(entry.url)
            article = await feeds.fetch_article(self.app.http, entry)
        return article

    async def _fetch_images(self, article: feeds.Article) -> None:
        srcs = [b.src for b in article.blocks if isinstance(b, feeds.Picture)][:PREFETCH_IMAGES]
        start, done = time.perf_counter(), 0
        async with self.images:
            for src in srcs:
                if feeds.image_path(src).exists():
                    continue
                try:
                    await feeds.fetch_image(self.app.http, src, article.url)
                    done += 1
                except Exception:
                    pass
        if srcs:
            self.app.timing.write(
                "prefetch_images", url=article.url, n=len(srcs), fetched=done,
                ms=round((time.perf_counter() - start) * 1000),
            )

    def is_ready(self, url: str) -> bool:
        task = self._valid(url)
        return task is not None and task.done()

    def prefetch(self, entries: list[feeds.Entry]) -> None:
        if not self.enabled:
            return
        for e in entries:
            if not self._valid(e.url):
                self._start(e, prefetch=True)

    async def get(self, entry: feeds.Entry, kind: str = "article") -> feeds.Article:
        """記事を返す。先読みが済んでいればすぐ、途中なら待つ、無ければ取りに行く。"""
        start = time.perf_counter()
        task = self._valid(entry.url)
        if task is None:
            how = "miss"
        elif task.done():
            how = "ready"
        elif entry.url in self.started:
            how = "inflight"
        else:
            # 先読みの順番待ちのあいだに開かれた。待たずに自分で取りに行く
            task.cancel()
            task, how = None, "queued"
        if task is None:
            task = self._start(entry, prefetch=False)
        try:
            # 画面を閉じて読み込みがキャンセルされても、共有している Task は止めない
            article = await asyncio.shield(task)
        except httpx.HTTPError:
            if how == "miss":
                raise
            how += "_retry"  # 先読みが失敗していたら取り直す
            article = await asyncio.shield(self._start(entry, prefetch=False))
        self.app.timing.write(
            "open", kind=kind, url=entry.url, how=how, wait_ms=round((time.perf_counter() - start) * 1000)
        )
        return article


class Bookmarks:
    """ブックマーク。RSS から消えた記事も開けるよう、記事の情報ごと保存する。"""

    FILE = feeds.STATE_DIR / "bookmarks.json"

    def __init__(self) -> None:
        try:
            self.items: list[dict] = json.loads(self.FILE.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            self.items = []

    def has(self, url: str) -> bool:
        return any(d["url"] == url for d in self.items)

    def toggle(self, e: feeds.Entry) -> bool:
        """付けたら True、外したら False を返す。"""
        if self.has(e.url):
            self.items = [d for d in self.items if d["url"] != e.url]
            added = False
        else:
            self.items.insert(0, {
                "site": e.site.name, "feed": e.site.feed, "preset": e.site.preset,
                "title": e.title, "url": e.url, "timestamp": e.timestamp,
                "category": e.category,
            })
            added = True
        self.FILE.parent.mkdir(parents=True, exist_ok=True)
        self.FILE.write_text(json.dumps(self.items, ensure_ascii=False, indent=1), encoding="utf-8")
        return added

    def entries(self, sites: list[feeds.Site]) -> list[feeds.Entry]:
        by_name = {s.name: s for s in sites}
        out = []
        for d in self.items:
            # サイトを削除していても、保存しておいた情報で開けるようにする
            site = by_name.get(d["site"]) or feeds.Site(d["site"], d["feed"], d.get("preset"))
            out.append(feeds.Entry(site, d["title"], d["url"], d["timestamp"], d["category"]))
        return out


def is_web_url(url: str) -> bool:
    """http・https の URL か。フィードの中の URL はそのまま OS やコマンドに渡すので、
    file:// やネットワーク上のプログラムの場所などは開かない（Windows の os.startfile は、それを動かしてしまう）"""
    return urlparse(url).scheme.lower() in ("http", "https")


def open_in_browser(url: str) -> None:
    if not is_web_url(url):
        return
    if sys.platform == "win32":
        os.startfile(url)
        return
    # WSL では wslview で Windows 側のブラウザを開く
    for cmd in ("wslview", "open" if sys.platform == "darwin" else "xdg-open"):
        if shutil.which(cmd):
            # 出力が TUI に混ざらないよう捨てる
            subprocess.Popen(
                [cmd, url], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
            )
            return
    webbrowser.open(url)


_player: list[str] | None = None

# mpv で開くときの指定。yt-dlp が動画の URL を調べるあいだも窓を出す。端末のキーを読まないよう --no-terminal。
# YouTube は 1080p 以上が多く、そのままだと窓が画面いっぱいになるので 7 割までに収める
MPV = ["mpv", "--force-window=immediate", "--no-terminal", "--autofit-larger=70%x70%"]


def _chosen_player() -> list[str]:
    """MATOME_PLAYER で指定されたプレイヤー（mpv・vlc、または引数つきのコマンド）。無ければ空。"""
    try:
        cmd = shlex.split(os.environ.get("MATOME_PLAYER", ""))
    except ValueError:
        return []
    if not cmd or not shutil.which(cmd[0]):
        return []
    if os.path.basename(cmd[0]) == "mpv":
        return [cmd[0], *MPV[1:], *cmd[1:]]
    return cmd


def video_player() -> list[str]:
    """動画を開くコマンド。MATOME_PLAYER があればそれ、無ければ mp4 の既定のアプリ
    （Mac は IINA など、Linux は xdg-mime の設定）を使い、分からなければ mpv か VLC。どれも無ければ空。"""
    global _player
    if _player is None:
        _player = _chosen_player()
        if _player:
            pass
        elif sys.platform == "darwin":
            app = _mac_default_app("mp4")
            if app:
                _player = ["open", "-a", app]
        elif sys.platform.startswith("linux") and shutil.which("gio"):
            desktop = _linux_default_app("video/mp4")
            if desktop:
                _player = ["gio", "launch", desktop]
        if not _player:
            for cmd in ("mpv", "vlc"):
                if shutil.which(cmd):
                    _player = [cmd]
                    break
    return _player


def _linux_default_app(mime: str) -> str:
    """xdg-mime の既定のアプリの .desktop ファイルのパス。apt・snap・flatpak のどれで入れたものでも探せる。"""
    try:
        r = subprocess.run(
            ["xdg-mime", "query", "default", mime], capture_output=True, text=True, timeout=5,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    name = r.stdout.strip()
    if not name.endswith(".desktop"):
        return ""
    home = os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share")
    dirs = [home, *(os.environ.get("XDG_DATA_DIRS") or "/usr/local/share:/usr/share").split(":")]
    for d in dirs:
        path = os.path.join(d, "applications", name)
        if os.path.isfile(path):
            return path
    return ""


def _mac_default_app(ext: str) -> str:
    # 既定のアプリは実在するファイルでしか引けないので、空のファイルを作って聞く
    probe = feeds.CACHE_DIR / f"probe.{ext}"
    script = """
    function run(argv) {
        ObjC.import("AppKit");
        const u = $.NSWorkspace.sharedWorkspace.URLForApplicationToOpenURL($.NSURL.fileURLWithPath(argv[0]));
        return u.isNil() ? "" : u.path.js;
    }"""
    try:
        probe.parent.mkdir(parents=True, exist_ok=True)
        probe.touch()
        r = subprocess.run(
            ["osascript", "-l", "JavaScript", "-e", script, str(probe)],
            capture_output=True, text=True, timeout=5,
        )
        return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ""


def video_label(src: str) -> str:
    """記事の中の動画の行の文字。YouTube はブラウザで開くので、そう書く（MATOME_PLAYER を指定していればプレイヤー）。"""
    if feeds.is_youtube(src) and not _chosen_player():
        return f"▶ YouTube で開く（クリック / v）  {src}"
    return f"▶ 動画を再生（クリック / v）  {src}"


def open_video(url: str) -> None:
    """動画をプレイヤーで開く。プレイヤーが見つからなければブラウザで開く。
    YouTube はブラウザ（YouTube のプレイヤー）で開く。YouTube の規約は決められた方法以外での読み取りを
    認めていないので、matome から yt-dlp などを使うようには仕向けない。MATOME_PLAYER を指定していればそれに渡す。"""
    if not is_web_url(url):
        return
    cmd = _chosen_player() if feeds.is_youtube(url) else video_player()
    if not cmd:
        open_in_browser(url)
        return
    subprocess.Popen(
        [*cmd, url], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _image_clipboard() -> list[str]:
    """画像そのものをクリップボードに入れるコマンド（PNG を標準入力で渡す）。使えなければ空。

    SSH でつないでいるときは、このマシンのクリップボードに入れても手元では貼れないので空にする。
    """
    if os.environ.get("SSH_CONNECTION"):
        return []
    if sys.platform == "darwin":
        return ["osascript"]
    if os.environ.get("WAYLAND_DISPLAY") and shutil.which("wl-copy"):
        return ["wl-copy", "--type", "image/png"]
    if os.environ.get("DISPLAY") and shutil.which("xclip"):
        return ["xclip", "-selection", "clipboard", "-t", "image/png", "-i"]
    return []


def _png(path: Path) -> bytes:
    img = PILImage.open(path)
    img.seek(0)  # アニメ GIF は 1 枚目だけ
    buf = io.BytesIO()
    img.convert("RGBA").save(buf, "PNG")
    return buf.getvalue()


def _copy_png(cmd: list[str], path: Path) -> None:
    png = _png(path)
    if cmd == ["osascript"]:
        tmp = feeds.CACHE_DIR / "clipboard.png"
        tmp.write_bytes(png)
        script = f'set the clipboard to (read (POSIX file "{tmp}") as «class PNGf»)'
        subprocess.run(["osascript", "-e", script], check=True, timeout=10, capture_output=True)
    else:
        # wl-copy は貼り付けに応えるため裏に残り、出力の口を開いたままにする。
        # 出力を受け取ると終わりを待ち続けてしまうので捨てる
        subprocess.run(
            cmd, input=png, check=True, timeout=10,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )


async def original_image(app: App, pic) -> tuple[Path | None, str]:
    """コピー・保存・拡大に使う画像（キャッシュのパスと URL）。元の画像へのリンクがあればそちらを取る。

    pic は src・full・path・referer を持つもの（画像一覧のタイルや記事の中の画像）。
    元の画像を取れなければ、表示している画像を使う。
    """
    if pic.full and pic.full != pic.src:
        try:
            return await feeds.fetch_image(app.http, pic.full, pic.referer), pic.full
        except Exception as e:
            app.log(e)
    return pic.path, pic.src


def can_show_window() -> bool:
    """このマシンの画面に mpv の窓を出せるか。SSH ごしや画面の無い Linux では、窓を出しても手元に映らない。"""
    if os.environ.get("SSH_CONNECTION") or not shutil.which("mpv"):
        return False
    return sys.platform == "darwin" or bool(os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY"))


def _is_animated(path: Path) -> bool:
    try:
        with PILImage.open(path) as img:
            return getattr(img, "n_frames", 1) > 1
    except Exception:
        return False


async def play_animation(app: App, pic) -> bool:
    """アニメ GIF（など何コマもある画像）なら mpv でくり返し再生して True を返す。
    静止画のときや、mpv の窓を出せないとき（SSH ごしなど）は何もせず False（拡大表示で 1 コマ目を出す）。"""
    if not can_show_window():
        return False
    path, url = await original_image(app, pic)
    if not path or not await asyncio.to_thread(_is_animated, path):
        return False
    subprocess.Popen(
        [*MPV, "--loop-file=inf", f"--title={url}", str(path)],
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True,
    )
    app.notify("アニメ GIF を mpv で再生しています…", timeout=2)
    return True


async def copy_image(app: App, path: Path | None, url: str) -> None:
    """画像をクリップボードに入れる。手元のマシンなら画像そのもの、SSH ごしなどでは画像の URL。

    URL は端末の機能（OSC 52）で手元の端末のクリップボードに入れるので、SSH ごしでも届く。
    """
    cmd = _image_clipboard()
    if cmd and path:
        try:
            await asyncio.to_thread(_copy_png, cmd, path)
            app.notify("画像をコピーしました", timeout=2)
            return
        except Exception as e:  # 画像を読めない・コマンドが失敗したときは URL にする
            app.log(e)
    app.copy_to_clipboard(url)
    app.notify(f"画像の URL をコピーしました: {url}", timeout=3)


def copy_url(app: App, url: str) -> None:
    """記事の URL をクリップボードに入れる。端末の機能（OSC 52）を使うので SSH ごしでも手元に届く。"""
    app.copy_to_clipboard(url)
    app.notify(f"URL をコピーしました: {url}", timeout=3, markup=False)


def url_info(screen: Screen) -> list[tuple[str, str]]:
    """画面のカーソルのところの URL（名前, URL）。先頭が U でコピーするもの。無ければ空。

    画面の url_info() から集める（サイト一覧・記事一覧・記事・画像一覧・拡大表示が持つ）。"""
    info = getattr(screen, "url_info", None)
    return [(name, url) for name, url in info() if url] if info else []


def show_url(app: App, items: list[tuple[str, str]]) -> None:
    """URL を通知に出す（Ctrl+g）。コピーはしない。"""
    if not items:
        app.notify("ここには URL がありません", timeout=2)
        return
    app.notify("\n".join(f"{name}: {url}" for name, url in items), title="URL", timeout=10, markup=False)


def save_image(app: App, path: Path | None, url: str) -> None:
    """画像を ~/Downloads/matome/ に保存する。同じ名前があれば番号を付ける。"""
    if not path:
        app.notify("画像をまだ読み込んでいません", severity="warning", timeout=2)
        return
    downloads = Path.home() / "Downloads"
    folder = (downloads if downloads.is_dir() else Path.home()) / "matome"
    name = re.sub(r"[^\w.-]", "_", Path(urlparse(url).path).name) or "image"
    stem, suffix = Path(name).stem, Path(name).suffix
    if not suffix:
        try:
            fmt = PILImage.open(path).format or "png"
        except Exception:
            fmt = "png"
        suffix = "." + fmt.lower().replace("jpeg", "jpg")
    dest = folder / f"{stem}{suffix}"
    n = 2
    while dest.exists():
        dest = folder / f"{stem}-{n}{suffix}"
        n += 1
    try:
        folder.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
    except OSError as e:
        app.notify(f"保存できませんでした: {e}", severity="error", timeout=5)
        return
    app.notify(f"保存しました: {dest}", timeout=4)


def default_editor() -> list[str]:
    editor = os.environ.get("VISUAL") or os.environ.get("EDITOR")
    if editor:
        return shlex.split(editor)
    return ["notepad"] if sys.platform == "win32" else ["vi"]


class GG:
    """`gg` で先頭へ飛ぶための 2 打鍵判定。"""

    _g_pending = False

    def on_key(self, event: events.Key) -> None:
        if event.key == "g":
            event.stop()
            if self._g_pending:
                self._g_pending = False
                self.action_top()
            else:
                self._g_pending = True
        else:
            self._g_pending = False

    def action_top(self) -> None:  # pragma: no cover - 各画面で実装
        raise NotImplementedError


class VimList(GG, Screen):
    """ListView を 1 つ持つ画面の共通キー操作。"""

    BINDINGS = [
        Binding("j", "down", "下", show=False),
        Binding("k", "up", "上", show=False),
        Binding("G", "bottom", "末尾", show=False),
        Binding("ctrl+d", "half(1)", show=False),
        Binding("ctrl+u", "half(-1)", show=False),
        Binding("l,right", "open", "開く"),
        Binding("enter", "open", "開く", show=False),
    ]

    @property
    def lv(self) -> ListView:
        return self.query_one(ListView)

    def action_down(self) -> None:
        self.lv.action_cursor_down()

    def action_up(self) -> None:
        self.lv.action_cursor_up()

    def action_top(self) -> None:
        if self.lv.children:
            self.lv.index = 0

    def action_bottom(self) -> None:
        if self.lv.children:
            self.lv.index = len(self.lv.children) - 1

    def action_half(self, direction: int) -> None:
        step = max(1, self.lv.size.height // 2)
        n = len(self.lv.children)
        if n:
            self.lv.index = max(0, min(n - 1, (self.lv.index or 0) + direction * step))

    def on_list_view_selected(self, event: ListView.Selected) -> None:
        self.action_open()

    def action_open(self) -> None:  # pragma: no cover - 各画面で実装
        raise NotImplementedError


# ---------------------------------------------------------------- サイト一覧


class WrapListView(ListView):
    """末尾で下へ進むと先頭へ、先頭で上へ戻ると末尾へ回る一覧（サイト一覧で使う）。"""

    def action_cursor_down(self) -> None:
        if self.children and self.index == len(self.children) - 1:
            self.index = 0
        else:
            super().action_cursor_down()

    def action_cursor_up(self) -> None:
        if self.children and self.index == 0:
            self.index = len(self.children) - 1
        else:
            super().action_cursor_up()


class SiteItem(ListItem):
    def __init__(self, site: feeds.Site | None, label: str, kind: str = "site") -> None:
        super().__init__()
        self.site = site
        self.label = label
        self.kind = kind  # site / all / bookmarks / empty

    def compose(self) -> ComposeResult:
        yield Label(self.label, markup=False)


class SiteScreen(VimList):
    BINDINGS = [
        Binding("1", "group(1)", "グループ", key_display="1-9"),
        *(Binding(str(n), f"group({n})", show=False) for n in feeds.GROUPS if n != 1),
        Binding("a", "add", "追加"),
        Binding("d", "delete", "削除"),
        Binding("J", "reorder(1)", show=False),
        Binding("K", "reorder(-1)", show=False),
        Binding("m", "move", show=False),
        Binding("x", "export", show=False),
        Binding("i", "import", show=False),
        Binding("e", "edit", show=False),
        Binding("U", "app.copy_url", "URL", show=False),
        Binding("question_mark", "keys", "キー一覧", key_display="?"),
        Binding("q", "app.quit", "終了"),
    ]
    # ステータスバーに入りきらないキーは ? のキー一覧に出す
    KEYS = [
        ("j / k", "下／上（端では反対の端へ回る）"),
        ("gg / G", "先頭／末尾"),
        ("l / Enter", "開く"),
        ("1-9", "グループ切替"),
        ("a", "サイトを追加（今のグループに入る）"),
        ("d", "サイトを削除"),
        ("J / K", "サイトを 1 つ下／上へ動かす"),
        ("m", "サイトを別のグループへ移す"),
        ("x", "書き出し（OPML）"),
        ("i", "読み込み（OPML）"),
        ("e", "設定ファイルを $EDITOR で編集"),
        ("U", "サイトの URL（RSS）をコピー。ほかの PC や matome でも a で貼れば同じサイトになる"),
        ("Ctrl+g", "サイトの URL（RSS・トップページ）を表示（どの画面でも、コピーはしない）"),
        ("q", "終了"),
    ]

    def compose(self) -> ComposeResult:
        yield Header()
        yield WrapListView(id="sites")
        yield Footer()

    async def on_mount(self) -> None:
        await self.refresh_sites()

    def on_screen_resume(self) -> None:
        self.app.sub_title = self.title_text()
        for item in self.query(SiteItem):
            if item.kind == "bookmarks":
                for label in item.query(Label):
                    label.update(self.bookmark_label())

    def bookmark_label(self) -> str:
        return f"★ ブックマーク（{len(self.app.bookmarks.items)} 件）"

    def title_text(self) -> str:
        """「サイト一覧  [1 まとめ]  2 ニュース」のように、今のグループを括弧で示す。"""
        current = self.app.settings.group
        used = {s.group for s in self.app.sites} | set(self.app.group_names) | {current}
        tabs = [
            f"[{self.app.group_label(n)}]" if n == current else self.app.group_label(n)
            for n in sorted(used)
        ]
        return "サイト一覧  " + "  ".join(tabs)

    async def refresh_sites(self, index: int | None = None) -> None:
        try:
            self.app.sites, self.app.group_names = feeds.load_sites()
        except Exception as e:  # 手で編集した TOML が壊れていても落ちないように
            self.notify(f"{feeds.SITES_FILE} を読めません: {e}", severity="error", timeout=10)
        self.app.sub_title = self.title_text()
        lv = self.lv
        if index is None:
            index = lv.index or 0
        sites = self.app.group_sites()
        items = []
        if len(sites) > 1:
            items.append(SiteItem(None, f"◆ すべて（{len(sites)} サイトの新着順）", "all"))
        items.append(SiteItem(None, self.bookmark_label(), "bookmarks"))
        items.extend(SiteItem(s, s.name) for s in sites)
        if not sites:
            items.append(SiteItem(None, "a でサイトを追加（RSS の URL かサイトのトップページの URL）", "empty"))
        # 古い行が消え終わる前に数えると行数が合わず、カーソルが一覧の外に出るので待つ
        await lv.clear()
        await lv.extend(items)
        lv.index = max(0, min(index, len(items) - 1))
        lv.focus()

    def current(self) -> SiteItem | None:
        item = self.lv.highlighted_child
        return item if isinstance(item, SiteItem) else None

    def url_info(self) -> list[tuple[str, str]]:
        item = self.current()
        site = item.site if item and item.kind == "site" else None
        return [("RSS", site.feed), ("トップ", site.home)] if site else []

    def action_open(self) -> None:
        item = self.current()
        if item and item.kind == "empty":
            self.action_add()
        elif item:
            self.app.push_screen(EntryScreen(item.site, bookmarks=item.kind == "bookmarks"))

    async def action_group(self, n: int) -> None:
        if n == self.app.settings.group:
            return
        self.app.settings.group = n
        self.app.settings.save()
        await self.refresh_sites(index=0)

    def action_move(self) -> None:
        item = self.current()
        if not item or not item.site:
            return
        site = item.site

        async def done(n: int | None) -> None:
            if n and n != site.group:
                site.group = n
                feeds.save_sites(self.app.sites, self.app.group_names)
                await self.refresh_sites()
                self.notify(f"「{site.name}」を {self.app.group_label(n)} に移しました")

        self.app.push_screen(GroupScreen(f"「{site.name}」をどのグループに移しますか？"), done)

    async def action_reorder(self, step: int) -> None:
        """サイトをグループの中で 1 つ動かす。sites.toml の並びも同じように入れ替える。"""
        item = self.current()
        if not item or not item.site:
            return
        sites = self.app.group_sites()
        i = sites.index(item.site)
        if not 0 <= i + step < len(sites):
            return
        a, b = self.app.sites.index(sites[i]), self.app.sites.index(sites[i + step])
        self.app.sites[a], self.app.sites[b] = self.app.sites[b], self.app.sites[a]
        feeds.save_sites(self.app.sites, self.app.group_names)
        await self.refresh_sites(index=self.lv.index + step)

    def action_keys(self) -> None:
        self.app.push_screen(KeysScreen(self.KEYS))

    def action_add(self) -> None:
        async def done(site: feeds.Site | None) -> None:
            if site:
                site.group = self.app.settings.group
                feeds.append_site(site)
                await self.refresh_sites()
                self.lv.index = len(self.lv.children) - 1
                self.notify(f"「{site.name}」を追加しました")

        self.app.push_screen(AddSiteScreen(), done)

    def action_delete(self) -> None:
        item = self.current()
        if not item or not item.site:
            return
        site = item.site

        async def done(ok: bool | None) -> None:
            if ok:
                feeds.save_sites([s for s in self.app.sites if s is not site], self.app.group_names)
                await self.refresh_sites()
                self.notify(f"「{site.name}」を削除しました")

        self.app.push_screen(ConfirmScreen(f"「{site.name}」を削除しますか？"), done)

    def action_export(self) -> None:
        def write(path: Path) -> None:
            try:
                feeds.export_opml(self.app.sites, self.app.group_names, path)
            except OSError as e:
                self.notify(f"書き出せませんでした: {e}", severity="error", timeout=10)
                return
            self.notify(f"{len(self.app.sites)} サイトを書き出しました: {path}", timeout=5)

        def done(text: str | None) -> None:
            if not text:
                return
            path = Path(text).expanduser()
            if path.exists():
                self.app.push_screen(
                    ConfirmScreen(f"{path} はもうあります。上書きしますか？"),
                    lambda ok: write(path) if ok else None,
                )
            else:
                write(path)

        self.app.push_screen(PathScreen("サイト一覧を OPML で書き出す（すべてのグループ）", default_opml_path()), done)

    def action_import(self) -> None:
        async def done(text: str | None) -> None:
            if not text:
                return
            path = Path(text).expanduser()
            try:
                found, names = feeds.import_opml(path, self.app.settings.group)
            except (OSError, feeds.ET.ParseError) as e:
                self.notify(f"読み込めませんでした: {e}", severity="error", timeout=10)
                return
            known = {s.feed for s in self.app.sites}
            added = []
            for s in found:
                if s.feed not in known:
                    known.add(s.feed)
                    added.append(s)
            # 今のグループ名を優先し、名前の無いグループにだけ OPML の名前を使う
            group_names = {**names, **self.app.group_names}
            if added or group_names != self.app.group_names:
                feeds.save_sites(self.app.sites + added, group_names)
            await self.refresh_sites()
            skipped = len(found) - len(added)
            self.notify(
                f"{len(added)} サイトを追加しました" + (f"（登録済みの {skipped} サイトは飛ばしました）" if skipped else ""),
                timeout=5,
            )

        self.app.push_screen(PathScreen("OPML からサイトを読み込む（登録済みのものは飛ばす）", default_opml_path()), done)

    async def action_edit(self) -> None:
        if not feeds.SITES_FILE.exists():
            feeds.save_sites(self.app.sites, self.app.group_names)
        try:
            with self.app.suspend():
                subprocess.call([*default_editor(), str(feeds.SITES_FILE)])
        except Exception as e:
            self.notify(f"エディタを開けません（{e}）。{feeds.SITES_FILE} を直接編集してください", severity="error", timeout=10)
            return
        await self.refresh_sites()


class AddSiteScreen(ModalScreen["feeds.Site | None"]):
    BINDINGS = [Binding("escape", "cancel", "やめる")]

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label("サイトを追加（RSS の URL か、サイトのトップページの URL）")
            yield Input(placeholder="https://...", id="url")
            yield Static("Enter で追加 / Esc でやめる", id="status")

    def on_input_submitted(self, event: Input.Submitted) -> None:
        url = event.value.strip()
        if url:
            if not url.startswith("http"):
                url = "https://" + url
            self.add(url)

    @work(exclusive=True)
    async def add(self, url: str) -> None:
        status = self.query_one("#status", Static)
        status.update("フィードを探しています…")
        try:
            feed_url, name = await feeds.discover(self.app.http, url)
            if any(s.feed == feed_url for s in self.app.sites):
                status.update("そのサイトはもう登録されています")
                return
            site = feeds.Site(name, feed_url)
            status.update(f"「{name}」の記事の形を調べています…")
            site.preset = await feeds.detect_preset(self.app.http, site)
        except (httpx.HTTPError, ValueError) as e:
            status.update(f"追加できませんでした: {e}")
            return
        if not site.preset and not site.aggregator:
            self.notify("本文の場所を自動判定できませんでした。e で設定を編集して body を指定してください", severity="warning", timeout=10)
        self.dismiss(site)

    def action_cancel(self) -> None:
        self.dismiss(None)


def default_opml_path() -> str:
    downloads = Path.home() / "Downloads"
    return str((downloads if downloads.is_dir() else Path.home()) / "matome-sites.opml")


class PathScreen(ModalScreen["str | None"]):
    BINDINGS = [Binding("escape", "cancel", "やめる")]

    def __init__(self, question: str, path: str) -> None:
        super().__init__()
        self.question = question
        self.path = path

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.question, markup=False)
            yield Input(value=self.path, id="path")
            yield Static("Enter で決定 / Esc でやめる", id="status")

    def on_input_submitted(self, event: Input.Submitted) -> None:
        if event.value.strip():
            self.dismiss(event.value.strip())

    def action_cancel(self) -> None:
        self.dismiss(None)


class ConfirmScreen(ModalScreen[bool]):
    BINDINGS = [
        Binding("y", "answer(True)", "はい"),
        Binding("n,escape", "answer(False)", "いいえ"),
    ]

    def __init__(self, question: str) -> None:
        super().__init__()
        self.question = question

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.question, markup=False)
            yield Static("y: はい / n: いいえ")

    def action_answer(self, ok: bool) -> None:
        self.dismiss(ok)


class KeysScreen(ModalScreen[None]):
    BINDINGS = [Binding("escape,q,question_mark", "close", "閉じる")]

    def __init__(self, keys: list[tuple[str, str]]) -> None:
        super().__init__()
        self.keys = keys

    def compose(self) -> ComposeResult:
        width = max(cell_len(k) for k, _ in self.keys)
        lines = "\n".join(f"{k}{' ' * (width - cell_len(k))}   {desc}" for k, desc in self.keys)
        with Vertical(id="dialog"):
            yield Label("キー一覧", id="keys-title")
            yield Static(lines, markup=False)
            yield Static("Esc / ?: 閉じる", id="status")

    def action_close(self) -> None:
        self.dismiss(None)


class GroupScreen(ModalScreen["int | None"]):
    BINDINGS = [
        *(Binding(str(n), f"pick({n})", show=False) for n in feeds.GROUPS),
        Binding("escape,q", "pick(0)", "やめる"),
    ]

    def __init__(self, question: str) -> None:
        super().__init__()
        self.question = question

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.question, markup=False)
            yield Static("1-9: グループ / Esc: やめる")

    def action_pick(self, n: int) -> None:
        self.dismiss(n or None)


# ---------------------------------------------------------------- 記事一覧


SITE_NAME_CELLS = 14  # 「すべて」の一覧で見せるサイト名の幅（全角 7 文字）


def _fit_cells(s: str, width: int) -> str:
    """表示幅を width にそろえる。長ければ末尾を … にして切り、短ければ空白で埋める。"""
    if cell_len(s) > width:
        while cell_len(s) > width - 1:
            s = s[:-1]
        s += "…"
    return s + " " * (width - cell_len(s))


class EntryItem(ListItem):
    def __init__(self, entry: feeds.Entry, read: bool, show_site: bool) -> None:
        super().__init__(classes="read" if read else "")
        self.entry = entry
        self.show_site = show_site

    def text(self) -> Text:
        e = self.entry
        mark = "★ " if self.app.bookmarks.has(e.url) else ""
        category = f"[{e.category}]  " if e.category else ""
        text = Text(f"{mark}{e.date}  ")
        if self.show_site:
            # サイト名の長さでタイトルの書き出しがずれないよう、同じ幅に揃える
            text.append(_fit_cells(e.site.name, SITE_NAME_CELLS) + "  ", style="dim")
        text.append(f"{category}{e.title}")
        return text

    def compose(self) -> ComposeResult:
        yield Label(self.text(), markup=False)

    def update_label(self) -> None:
        # 作られた直後はまだ Label が無い（その場合は compose で最新の表示になる）
        for label in self.query(Label):
            label.update(self.text())


class MoreItem(ListItem):
    """一覧の末尾。ここにカーソルが来たら過去記事を読み込む。"""

    def compose(self) -> ComposeResult:
        yield Label("▼ さらに過去の記事を読み込む", markup=False)

    def set_text(self, text: str) -> None:
        for label in self.query(Label):
            label.update(text)


def _fold(s: str) -> str:
    """検索用の正規化。全角/半角と大文字/小文字の違いを無視する。"""
    return unicodedata.normalize("NFKC", s).casefold()


class SearchInput(Input):
    """`/` で出る検索欄。Esc で閉じる（画面側の Esc=戻る に渡さない）。"""

    BINDINGS = [Binding("escape", "close", show=False)]

    def action_close(self) -> None:
        self.value = ""
        self.remove_class("visible")
        self.screen.query_one(ListView).focus()


class EntryScreen(VimList):
    BINDINGS = [
        Binding("slash", "search", "検索"),
        Binding("n", "search_next(1)", "次を検索", show=False),
        Binding("N", "search_next(-1)", "前を検索", show=False),
        Binding("s", "bookmark", "ブックマーク"),
        Binding("u", "toggle_read", "既読の表示切替"),
        Binding("o", "browser", "ブラウザ"),
        Binding("U", "app.copy_url", "URL"),
        Binding("r", "reload", "再読込"),
        Binding("I", "gallery", "画像一覧"),
        Binding("V", "videos", "動画一覧"),
        Binding("q,h,left,escape", "back", "戻る"),
        Binding("Q", "app.quit", "終了", show=False),
    ]

    def __init__(self, site: feeds.Site | None, bookmarks: bool = False) -> None:
        super().__init__()
        self.site = site  # None は「すべて」かブックマーク
        self.bookmarks = bookmarks
        self.group = 1  # 「すべて」で並べるグループ。on_mount で決める
        self.all_entries: list[feeds.Entry] = []  # 読み込んだ記事すべて
        self.entries: list[feeds.Entry] = []  # 画面に出している記事（既読を隠しているときはその残り）
        self.query_text = ""
        self.next_page: dict[str, int] = {}  # サイト名 → 次に読む一覧ページ
        self.prefetch_timer = None
        self.exhausted: set[str] = set()  # これ以上過去記事が無いサイト

    @property
    def sites(self) -> list[feeds.Site]:
        return [self.site] if self.site else self.app.group_sites(self.group)

    @property
    def hiding_read(self) -> bool:
        # ブックマークは読んだ記事を残しておく場所なので、既読でも隠さない
        return self.app.settings.hide_read and not self.bookmarks

    @property
    def title_text(self) -> str:
        if self.bookmarks:
            return "ブックマーク"
        name = self.site.name if self.site else f"すべて（{self.app.group_label(self.group)}）"
        return f"{name}（未読のみ）" if self.hiding_read else name

    def compose(self) -> ComposeResult:
        yield Header()
        yield ListView(id="entries")
        yield SearchInput(placeholder="タイトルを検索（Enter で移動 / Esc でやめる）", id="search")
        yield Footer()

    def action_search(self) -> None:
        box = self.query_one("#search", SearchInput)
        box.add_class("visible")
        box.focus()

    def on_input_submitted(self, event: Input.Submitted) -> None:
        box = self.query_one("#search", SearchInput)
        self.query_text = event.value.strip()
        box.value = ""
        box.remove_class("visible")
        self.lv.focus()
        if self.query_text:
            self.action_search_next(1, from_current=True)

    def action_search_next(self, direction: int, from_current: bool = False) -> None:
        """vim と同じく、今の位置から次（前）の一致へ移動する。末尾まで行ったら先頭に戻る。"""
        if not self.query_text or not self.entries:
            return
        q = _fold(self.query_text)
        hits = [i for i, e in enumerate(self.entries) if q in _fold(e.title)]
        if not hits:
            self.notify(f"見つかりません: {self.query_text}", severity="warning", timeout=3)
            return
        cur = self.lv.index or 0
        if from_current and cur in hits:
            target = cur
        elif direction > 0:
            target = next((i for i in hits if i > cur), hits[0])
        else:
            target = next((i for i in reversed(hits) if i < cur), hits[-1])
        self.lv.index = target
        self.notify(f"/{self.query_text}  {hits.index(target) + 1}/{len(hits)} 件目", timeout=2)

    def on_mount(self) -> None:
        self.group = self.app.settings.group
        self.action_reload()

    def on_screen_resume(self) -> None:
        self.app.sub_title = self.title_text
        # 記事画面でブックマークを付け外ししたかもしれないので表示を合わせる
        for item in self.lv.query(EntryItem):
            item.update_label()

    @work(exclusive=True, group="list")
    async def action_reload(self) -> None:
        self.next_page.clear()
        self.exhausted.clear()
        if self.bookmarks:
            await self.show(self.app.bookmarks.entries(self.app.sites), self.lv.index or 0)
            return
        self.notify("記事一覧を取得中…", timeout=2)
        results = await asyncio.gather(
            *(feeds.fetch_entries(self.app.http, s) for s in self.sites),
            return_exceptions=True,
        )
        entries: list[feeds.Entry] = []
        for site, result in zip(self.sites, results):
            if isinstance(result, BaseException):
                self.notify(f"{site.name} の取得に失敗しました: {result}", severity="error")
            else:
                entries.extend(result)
        if not self.site:
            entries.sort(key=lambda e: e.timestamp, reverse=True)
        await self.show(entries, self.lv.index or 0)

    async def show(self, entries: list[feeds.Entry], index: int, keep_url: str = "") -> None:
        """記事を並べ直す。keep_url があればその記事にカーソルを合わせる。"""
        self.all_entries = entries
        read = self.app.read.urls
        if self.hiding_read:
            entries = [e for e in entries if e.url not in read]
        self.entries = entries
        self.app.sub_title = self.title_text
        lv = self.lv
        await lv.clear()
        await lv.extend(EntryItem(e, e.url in read, self.site is None) for e in entries)
        if not self.bookmarks:
            await lv.append(MoreItem())
        if entries:
            urls = [e.url for e in entries]
            lv.index = urls.index(keep_url) if keep_url in urls else min(index, len(entries) - 1)
        elif self.hiding_read and self.all_entries:
            self.notify("未読の記事はありません（u ですべて表示）", timeout=3)
        lv.focus()

    async def action_toggle_read(self) -> None:
        if self.bookmarks:
            return
        self.app.settings.hide_read = not self.app.settings.hide_read
        self.app.settings.save()
        item = self.lv.highlighted_child
        keep = item.entry.url if isinstance(item, EntryItem) else ""
        await self.show(self.all_entries, self.lv.index or 0, keep_url=keep)
        self.notify("未読のみ表示" if self.hiding_read else "既読も表示", timeout=2)

    def on_list_view_highlighted(self, event: ListView.Highlighted) -> None:
        if isinstance(event.item, MoreItem):
            self.load_more()
        elif isinstance(event.item, EntryItem):
            # j を押し続けているあいだは先読みしない。止まって 0.3 秒たったら、カーソルの記事と下の数件
            if self.prefetch_timer is not None:
                self.prefetch_timer.stop()
            i = self.lv.index or 0
            ahead = self.entries[i : i + 1 + PREFETCH_AHEAD]
            self.prefetch_timer = self.set_timer(0.3, lambda: self.app.articles.prefetch(ahead))

    @work(exclusive=True, group="more")
    async def load_more(self) -> None:
        more = self.lv.query(MoreItem)
        if not more:
            return
        more.first().set_text("読み込み中…")
        seen = {e.url for e in self.all_entries}

        async def one(site: feeds.Site) -> list[feeds.Entry]:
            # 一覧ページは 1 ページ目から読む（RSS と件数が違うので、重複を飛ばして抜けを防ぐ）
            for _ in range(5):
                page = self.next_page.get(site.name, 1)
                self.next_page[site.name] = page + 1
                got = await feeds.fetch_page(self.app.http, site, page)
                if not got:
                    break
                new = [e for e in got if e.url not in seen]
                if new:
                    return new
            self.exhausted.add(site.name)
            return []

        targets = [s for s in self.sites if s.name not in self.exhausted]
        results = await asyncio.gather(*(one(s) for s in targets), return_exceptions=True)
        new: list[feeds.Entry] = []
        for site, result in zip(targets, results):
            if isinstance(result, BaseException):
                self.notify(f"{site.name} の過去記事を読めません: {result}", severity="error")
            else:
                new.extend(e for e in result if e.url not in seen and not seen.add(e.url))
        if not new:
            more.first().set_text("（これ以上の過去記事はありません）")
            return
        old = len(self.entries)
        entries = self.all_entries + new
        if not self.site:
            entries.sort(key=lambda e: e.timestamp, reverse=True)
        await self.show(entries, old)
        self.notify(f"{len(new)} 件読み込みました", timeout=2)

    def action_bookmark(self) -> None:
        item = self.lv.highlighted_child
        if isinstance(item, EntryItem):
            added = self.app.bookmarks.toggle(item.entry)
            item.update_label()
            self.notify("ブックマークしました" if added else "ブックマークを外しました", timeout=2)

    def action_open(self) -> None:
        if isinstance(self.lv.highlighted_child, EntryItem):
            self.open_article(self.lv.index)

    def open_article(self, index: int, replace: bool = False) -> None:
        self.app.read.mark(self.entries[index].url)
        items = list(self.lv.query(EntryItem))
        if 0 <= index < len(items):
            items[index].add_class("read")
            self.lv.index = index
        screen = ArticleScreen(self, index)
        if replace:
            self.app.switch_screen(screen)
        else:
            self.app.push_screen(screen)

    def action_browser(self) -> None:
        item = self.lv.highlighted_child
        if isinstance(item, EntryItem):
            open_in_browser(item.entry.url)

    def url_info(self) -> list[tuple[str, str]]:
        item = self.lv.highlighted_child
        return [("記事", item.entry.url)] if isinstance(item, EntryItem) else []

    def action_gallery(self) -> None:
        if self.entries:
            self.app.push_screen(GalleryScreen(self))

    def action_videos(self) -> None:
        if self.entries:
            self.app.push_screen(VideoScreen(self))

    def action_back(self) -> None:
        self.app.pop_screen()


# ---------------------------------------------------------------- 記事


class ImageSlot(Static):
    """画像の読み込み待ちプレースホルダ。読めたら Image と差し替える。画像を出さない設定のときはそのまま残る。"""

    def __init__(self, src: str, full: str = "", hidden: bool = False) -> None:
        super().__init__("［画像（i で表示）］" if hidden else "［画像を読み込み中…］", classes="slot")
        self.src = src
        self.full = full
        self.showing = not hidden  # 画像を出す（読み込み中も）。i で非表示・読めなかったときは False（文の中の URL で開けるようにする）


class VideoSlot(Static):
    """動画の行。クリックするか、画面に見えているときに v を押すとプレイヤーで開く。"""

    def __init__(self, src: str) -> None:
        super().__init__(video_label(src), markup=False, classes="video")
        self.src = src

    def on_click(self) -> None:
        self.play()

    def play(self) -> None:
        open_video(self.src)
        self.notify("動画を開いています…", timeout=2)


# 本文・コメントの中の URL。末尾の句読点や閉じかっこは URL に含めない
URL_RE = re.compile(r"https?://[^\s<>\"'（）「」『』【】、。]+")
URL_TRAIL = ".,;:!?)]}'\""


def is_gif(url: str) -> bool:
    return bool(re.search(r"\.gif([?#]|$)", url, re.I))


def url_kind(url: str) -> str:
    """リンクの種類。"picture"（画像）・"video"（動画・YouTube）・"page"（それ以外）。"""
    if re.search(r"\.(jpe?g|png|gif|webp)([?#]|$)", url, re.I):
        return "picture"
    if feeds.is_youtube(url) or re.search(r"\.(mp4|webm|mov)([?#]|$)", url, re.I):
        return "video"
    return "page"


def link_text(text: str, links: list[tuple[int, int, str]] | None = None, shown: frozenset[str] = frozenset()) -> Text:
    """URL とリンク（「ソースはこちら」のように URL が見えていないものも）に下線を引き、
    クリックで開けるよう URL を印（meta）として持たせる。

    shown は記事の中に画像・動画の行があるものの URL。それはその行で開くので下線を引かない。
    妹はVIPPER のように画像の URL を文字で書いただけのものは、ここで下線を引いて拡大表示で開く。"""
    out = Text(text)
    for start, end, url in links or []:
        if url in shown:
            continue
        out.stylize(Style(underline=True, meta={"url": url}), start, end)
    for m in URL_RE.finditer(text):
        url = m.group(0).rstrip(URL_TRAIL)
        if url in shown:
            continue
        out.stylize(Style(underline=True, meta={"url": url}), m.start(), m.start() + len(url))
    return out


def text_browser() -> list[str]:
    """URL を開くターミナルの中のブラウザ。MATOME_TEXT_BROWSER（引数つきでもよい）、無ければ w3m。どちらも無ければ空。"""
    try:
        cmd = shlex.split(os.environ.get("MATOME_TEXT_BROWSER", ""))
    except ValueError:
        cmd = []
    if cmd and shutil.which(os.path.expanduser(cmd[0])):
        return [os.path.expanduser(cmd[0]), *cmd[1:]]
    return ["w3m"] if shutil.which("w3m") else []


class LinkText(Static):
    """本文やコメントの文。中の URL をクリックすると、ターミナルの中のブラウザ（w3m）で開き、閉じると戻る（画像・動画の URL は open_url）。"""

    def __init__(self, text: str, classes: str = "", links: list[tuple[int, int, str]] | None = None,
                 id: str | None = None, shown: frozenset[str] = frozenset()) -> None:
        self.text, self.links = text, links
        self.base = link_text(text, links, shown)
        super().__init__(self.base, classes=classes, id=id)

    def set_shown(self, shown: frozenset[str]) -> bool:
        """画像の行が出た・消えたときに、下線を引く URL を選び直す。変わったら True。"""
        base = link_text(self.text, self.links, shown)
        if base.spans == self.base.spans:
            return False
        self.base = base
        self.update(base)
        return True

    def link_spans(self) -> list[tuple[int, int, str]]:
        """この文の中のリンク（始まり, 終わり, URL）を前から順に。

        見えている URL に <a> のリンク（アフィリエイトの転送先など）が重なっていると、同じ場所に URL が 2 つ付く。
        クリックで開くのは後から付けた見えている URL なので、そちらだけ残す（2 つあると Tab が先へ進めなくなる）。"""
        spans: dict[tuple[int, int], str] = {}
        for sp in self.base.spans:
            if isinstance(sp.style, Style) and sp.style.meta.get("url"):
                spans[sp.start, sp.end] = sp.style.meta["url"]
        return sorted((a, b, url) for (a, b), url in spans.items())

    def mark(self, start: int | None = None, end: int | None = None) -> None:
        """start〜end のリンクを反転して目立たせる（start が None なら元に戻す）。"""
        if start is None:
            self.update(self.base)
            return
        text = self.base.copy()
        text.stylize("reverse", start, end)
        self.update(text)

    def place(self, offset: int) -> tuple[int, int]:
        """offset の文字が、この部品の中で何行目・何桁目に出るか（折り返しを考える。おおよそ）。"""
        width = max(self.content_region.width or self.size.width, 1)
        line = col = 0
        for part in self.base.plain[:offset].split("\n"):
            cells = cell_len(part)
            line += cells // width
            col = cells % width
            line += 1
        return line - 1, col

    def on_click(self, event: events.Click) -> None:
        url = event.style.meta.get("url") if event.style else None
        if url and event.button == 1:
            event.stop()
            open_url(self.app, url)


def open_url(app: App, url: str) -> None:
    """本文のリンクを開く。画像は拡大表示、動画はプレイヤー、それ以外は w3m など。
    中身を JavaScript で組み立てるサイト（imgur など）は w3m では何も出ないので、いつものブラウザで開く。"""
    kind = url_kind(url)
    if kind == "picture" and isinstance(app.screen, ArticleScreen):
        app.run_worker(app.screen.zoom_url(url))
    elif kind == "video":
        open_video(url)
        app.notify("動画を開いています…", timeout=2)
    elif urlparse(url).hostname in feeds.BROWSER_ONLY_HOSTS:
        open_in_browser(url)
        app.notify("ブラウザで開いています", timeout=2)
    else:
        open_link(app, url)


def open_link(app: App, url: str) -> None:
    """URL を w3m などで開く。matome は一時停止して画面を渡し、閉じたら同じ記事の同じ位置に戻る。
    ターミナルの中のブラウザが無ければ、いつものブラウザで開く。"""
    if not is_web_url(url):
        app.notify("http・https 以外の URL は開きません", severity="warning", timeout=3)
        return
    cmd = text_browser()
    if not cmd:
        open_in_browser(url)
        app.notify("ブラウザで開いています（w3m を入れるとターミナルの中で開けます）", timeout=3)
        return
    try:
        with app.suspend():
            subprocess.run([*cmd, url])
    except Exception as e:  # 一時停止できない環境（Textual の web 版など）や、コマンドが動かないとき
        app.log(e)
        open_in_browser(url)
        return
    # 端末の画面は w3m が書き換えたので、画像（sixel）も描き直す
    for widget in app.screen.query(Image):
        for child in widget.children:
            child.refresh()


class ArticleScreen(GG, Screen):
    BINDINGS = [
        Binding("j", "scroll(1)", "下", show=False),
        Binding("k", "scroll(-1)", "上", show=False),
        Binding("down", "scroll(1)", show=False),
        Binding("up", "scroll(-1)", show=False),
        Binding("ctrl+d", "page(0.5)", show=False),
        Binding("ctrl+u", "page(-0.5)", show=False),
        Binding("ctrl+f,space", "page(1)", show=False),
        Binding("ctrl+b,shift+space,b", "page(-1)", show=False),
        Binding("G", "bottom", show=False),
        Binding("c", "comments", "コメント"),
        Binding("n", "next(1)", "次の記事"),
        Binding("p", "next(-1)", "前の記事"),
        Binding("s", "bookmark", "ブックマーク"),
        Binding("o", "browser", "ブラウザ"),
        Binding("U", "app.copy_url", "URL をコピー", show=False),
        Binding("v", "video", "動画"),
        Binding("y", "copy_image", "画像をコピー", show=False),
        Binding("Y", "save_image", "画像を保存", show=False),
        Binding("D", "toggle_dither", "画像のディザ切替", show=False),
        Binding("i", "toggle_images", "画像の表示切替", show=False),
        Binding("I", "gallery", "画像一覧"),
        Binding("tab", "link(1)", "リンク", priority=True),
        Binding("shift+tab", "link(-1)", show=False, priority=True),
        Binding("enter", "open_link", show=False),
        Binding("m", "link_menu", show=False),
        Binding("q,h,left", "back", "戻る"),
        Binding("escape", "escape", show=False),
        Binding("Q", "app.quit", "終了", show=False),
    ]

    def __init__(self, parent: EntryScreen, index: int) -> None:
        super().__init__()
        self.list_screen = parent
        self.index = index
        self.entry = parent.entries[index]
        self.zooming = False  # 拡大の画像を読んでいる最中（クリックを続けても 1 回だけ開く）
        self.link: tuple[LinkText, int, int, str] | None = None  # Tab で選んでいるリンク

    # --- Tab でリンクを選ぶ（w3m と同じ感覚。Enter で開き、m でメニュー）

    def all_links(self) -> list[tuple[Widget, int, int, str]]:
        """Tab で選べるもの（リンクと画像）を上から順に。画像は（画像, -1, -1, 元の画像の URL）。"""
        found = [(w, a, b, url) for w in self.query(LinkText) for a, b, url in w.link_spans()]
        found += [(pic, -1, -1, pic.full or pic.src) for pic in self.body.query(".pic")]
        return sorted(found, key=lambda t: (self.link_y(t[0], t[1]), t[1]))

    def link_y(self, w: Widget, start: int) -> int:
        """リンク・画像の、本文の中での縦の位置（行）。"""
        return w.virtual_region.y + (w.place(start)[0] if isinstance(w, LinkText) else 0)

    def action_link(self, step: int) -> None:
        links = self.all_links()
        if not links:
            self.notify("この記事にリンクはありません", timeout=2)
            return
        keys = [(w, a) for w, a, _, _ in links]
        if self.link and (self.link[0], self.link[1]) in keys:
            i = (keys.index((self.link[0], self.link[1])) + step) % len(links)
        else:
            # 最初は、今画面に見えている一番上（Shift+Tab なら一番下）のリンクから
            top = self.body.scroll_y
            bottom = top + self.body.size.height
            ys = [self.link_y(w, a) for w, a, _, _ in links]
            if step > 0:
                i = next((n for n, y in enumerate(ys) if y >= top), 0)
            else:
                i = next((n for n in range(len(ys) - 1, -1, -1) if ys[n] < bottom), len(links) - 1)
        self.select_link(links[i])

    def select_link(self, link: tuple[Widget, int, int, str]) -> None:
        self.clear_link()
        self.link = link
        w, a, b, _ = link
        if isinstance(w, LinkText):
            w.mark(a, b)
        else:
            w.add_class("picked")  # 画像は反転できないので、すぐ下に印の行を出す
            self.body.mount(Static("▲ 選んでいる画像（Enter で拡大・m でメニュー）", classes="pick-mark"), after=w)
        y = self.link_y(w, a)
        top, height = self.body.scroll_y, self.body.size.height
        if not (top <= y < top + height - 1):  # 画面の外なら、上から 3 分の 1 くらいに来るようスクロール
            self.body.scroll_to(y=max(0, y - height // 3), animate=False)

    def clear_link(self) -> None:
        if self.link:
            w = self.link[0]
            if isinstance(w, LinkText):
                w.mark()
            else:
                w.remove_class("picked")
                for mark in self.body.query(".pick-mark"):
                    mark.remove()
            self.link = None

    async def action_open_link(self) -> None:
        if not self.link:
            return
        if isinstance(self.link[0], LinkText):
            open_url(self.app, self.link[3])
        else:
            await self.zoom_picture(self.link[0])

    def action_link_menu(self) -> None:
        if not self.link:
            self.notify("Tab でリンクを選んでから m を押してください", timeout=2)
            return
        w, a, _, url = self.link
        line, col = w.place(a) if isinstance(w, LinkText) else (0, 2)
        y = self.body.region.y + w.virtual_region.y + line - round(self.body.scroll_y)
        x = self.body.region.x + w.virtual_region.x + col
        items = link_items(self.app, url) if isinstance(w, LinkText) else picture_items(self.app, self, w)
        self.app.show_items(items, x, y + 1)

    def action_escape(self) -> None:
        if self.link:  # リンクを選んでいるときの Esc は、選ぶのをやめるだけ
            self.clear_link()
        else:
            self.action_back()

    def compose(self) -> ComposeResult:
        e = self.entry
        yield Header()
        with VerticalScroll(id="body"):
            yield Static(e.title, markup=False, id="title")
            category = f"[{e.category}]  " if e.category else ""
            yield LinkText(f"{e.date}  {e.site.name}  {category}{e.url}", id="meta")  # 記事の URL もクリックで開ける
            yield Static("読み込み中…", id="loading")
        yield Footer()

    def on_mount(self) -> None:
        self.update_title()
        self.body.focus()
        self.opened = time.perf_counter()
        self.load()

    def update_title(self) -> None:
        self.app.sub_title = f"{self.entry.site.name}  {self.index + 1}/{len(self.list_screen.entries)}"

    def on_screen_resume(self) -> None:
        self.update_title()  # 画像一覧から戻ったとき

    @property
    def body(self) -> VerticalScroll:
        return self.query_one("#body", VerticalScroll)

    @work(exclusive=True)
    async def load(self) -> None:
        try:
            article = await self.app.articles.get(self.entry)
        except httpx.HTTPError as e:
            self.query_one("#loading", Static).update(f"取得に失敗しました: {e}")
            return
        self.page_url = article.url  # アンテナの記事は配信元の URL になる
        await self.query_one("#loading").remove()

        widgets: list[Static] = []
        slots: list[ImageSlot] = []
        rows = (feeds.Picture, feeds.Video) if self.app.settings.images else (feeds.Video,)
        shown = frozenset(u for b in article.blocks if isinstance(b, rows)
                          for u in (b.src, getattr(b, "full", "")) if u)
        for block in article.blocks:
            if isinstance(block, feeds.Picture):
                slot = ImageSlot(block.src, block.full, hidden=not self.app.settings.images)
                slots.append(slot)
                widgets.append(slot)
            elif isinstance(block, feeds.Video):
                widgets.append(VideoSlot(block.src))
            else:
                widgets.append(LinkText(block.text, classes="quote" if block.quote else "text", links=block.links,
                                        shown=shown))
        if not article.blocks:
            widgets.append(Static("本文を取り出せませんでした。o でブラウザで開けます", classes="text"))
        widgets.append(Rule())
        widgets.append(Static(f"コメント（{len(article.comments)}件）", id="comments-head"))
        for c in article.comments:
            widgets.append(Static(c.header, markup=False, classes="c-head"))
            widgets.append(LinkText(c.body, classes="c-body"))
        await self.body.mount_all(widgets)
        timing = self.app.timing
        timing.write("shown", url=self.entry.url, ms=round((time.perf_counter() - self.opened) * 1000))
        # 次に n で進む記事を先読みする
        entries = self.list_screen.entries
        self.app.articles.prefetch(entries[self.index + 1 : self.index + 1 + PREFETCH_AHEAD])
        if self.app.settings.images:
            self.load_images()

    @work(exclusive=True, group="images")
    async def load_images(self) -> None:
        slots = list(self.body.query(ImageSlot))
        start = time.perf_counter()
        sem = asyncio.Semaphore(4)
        on_disk = sum(feeds.image_path(s.src).exists() for s in slots)

        async def fill(slot: ImageSlot) -> None:
            async with sem:
                slot.update("［画像を読み込み中…］")
                await self.load_image(slot)

        for slot in slots:
            slot.showing = True
        self.refresh_links()
        await asyncio.gather(*(fill(s) for s in slots))
        if slots:
            # 記事を開いてから全部の画像が出るまで（i で表示に戻したときはそこから）
            since = self.opened if start - self.opened < 1 else start
            self.app.timing.write(
                "images", url=self.entry.url, n=len(slots), on_disk=on_disk,
                ms=round((time.perf_counter() - since) * 1000),
            )

    async def load_image(self, slot: ImageSlot) -> None:
        try:
            path = await feeds.fetch_image(self.app.http, slot.src, self.page_url)
            img = await asyncio.to_thread(_prepare_image, path)
        except Exception as e:  # 壊れた画像や 404 は本文の邪魔をしない
            slot.update(f"［画像を表示できません: {slot.src}］")
            slot.showing = False
            self.log(e)
            if self.is_attached:
                self.refresh_links()
            return
        if not self.is_attached or not slot.is_attached:
            return  # 読み込んでいるあいだに記事を閉じた（本文の枠がもう無い）か、i で非表示にされた
        cell = get_cell_size()
        cw, ch = max(cell.width, 1), max(cell.height, 1)
        cells = math.ceil(img.width / cw)
        # 縦長の画像は、本文の枠の高さの 3 割に収まる幅まで縮める（枠より高いと全体が一度に見えず、描かれない）
        max_rows = max(math.floor(self.body.scrollable_content_region.height * MAX_IMAGE_HEIGHT), 5)
        fit_cells = math.floor(max_rows * ch / img.height * img.width / cw)
        widget = Image(img, classes="pic")
        # y・Y でコピー・保存、クリックで拡大するとき使う（original_image と PictureScreen が見る）
        widget.src, widget.full, widget.path, widget.referer = slot.src, slot.full, path, self.page_url
        widget.entry = self.entry
        widget.styles.width = max(1, min(cells, fit_cells, MAX_IMAGE_CELLS, max(self.body.size.width - 4, 10)))
        widget.styles.height = "auto"
        if not self.app.settings.images or not slot.is_attached:
            return  # 読み込んでいるあいだに i で非表示にされた
        await self.body.mount(widget, after=slot)
        await slot.remove()

    async def action_toggle_images(self) -> None:
        settings = self.app.settings
        settings.images = not settings.images
        settings.save()
        self.notify(f"画像: {'表示' if settings.images else '非表示'}", timeout=2)
        # 記事の長さが大きく変わるので、画面の一番上に見えている段落が上に残るように戻す
        children = list(self.body.children)
        top = self.body.scroll_y
        anchor = next((i for i, w in enumerate(children) if w.virtual_region.bottom > top), 0)
        offset = top - children[anchor].virtual_region.y if children else 0
        if settings.images:
            self.load_images()
        else:
            self.workers.cancel_group(self, "images")
            for pic in list(self.body.query(".pic")):
                await self.body.mount(ImageSlot(pic.src, pic.full, hidden=True), after=pic)
                await pic.remove()
            for slot in self.body.query(ImageSlot):
                slot.update("［画像（i で表示）］")
                slot.showing = False
            self.refresh_links()
        children = list(self.body.children)
        if children:
            target = children[min(anchor, len(children) - 1)]
            self.call_after_refresh(lambda: self.body.scroll_to(y=target.virtual_region.y + offset, animate=False))

    def refresh_links(self) -> None:
        """本文の文の中の URL の下線を選び直す。画像・動画の行で開けるものはその行で開くので下線を引かず、
        i で非表示にした・読めなかった画像は行で開けないので、文の中の URL をクリック・Tab で選べるようにする。"""
        rows = [*self.body.query(VideoSlot), *self.body.query(".pic"),
                *(s for s in self.body.query(ImageSlot) if s.showing)]
        shown = frozenset(u for w in rows for u in (w.src, getattr(w, "full", "")) if u)
        for w in self.body.query("LinkText.text, LinkText.quote"):
            if self.link and self.link[0] is w:
                w.mark()  # 選んでいた位置がずれるので、選び直してもらう
                self.link = None
            w.set_shown(shown)

    def action_scroll(self, lines: int) -> None:
        self.body.scroll_relative(y=lines, animate=False)

    def action_page(self, ratio: float) -> None:
        self.body.scroll_relative(y=int(self.body.size.height * ratio), animate=False)

    def action_top(self) -> None:
        self.body.scroll_home(animate=False)

    def action_bottom(self) -> None:
        self.body.scroll_end(animate=False)

    def action_comments(self) -> None:
        heads = self.query("#comments-head")
        if heads:
            self.body.scroll_to_widget(heads.first(), top=True, animate=False)

    def action_next(self, step: int) -> None:
        index = self.index + step
        if 0 <= index < len(self.list_screen.entries):
            self.list_screen.open_article(index, replace=True)
        else:
            self.notify("これ以上記事がありません", timeout=2)

    def action_browser(self) -> None:
        open_in_browser(self.link[3] if self.link else self.entry.url)

    def url_info(self) -> list[tuple[str, str]]:
        # アンテナの記事は配信元の URL（読み込み前は一覧の URL）
        page = getattr(self, "page_url", "") or self.entry.url
        if self.link:  # Tab でリンクを選んでいるときは、そのリンクが先
            return [("リンク", self.link[3]), ("記事", page)]
        return [("記事", page)]

    def action_toggle_dither(self) -> None:
        settings = self.app.settings
        if not set_dither(not settings.dither):
            self.notify("この textual-image ではディザを切り替えられません", severity="warning")
            return
        settings.dither = not settings.dither
        settings.save()
        self.notify(f"画像のディザ: {'オン' if settings.dither else 'オフ'}", timeout=2)
        # 画像を描き直すため、同じ記事を開き直す
        self.list_screen.open_article(self.index, replace=True)

    def action_video(self) -> None:
        slots = list(self.query(VideoSlot))
        if not slots:
            self.notify("この記事に動画はありません", timeout=2)
            return
        # 画面に見えている動画のうち一番上のもの。見えていなければ記事の最初の動画
        top = self.body.scroll_y
        bottom = top + self.body.size.height
        visible = [s for s in slots if s.virtual_region.bottom > top and s.virtual_region.y < bottom]
        (visible or slots)[0].play()

    def visible_picture(self) -> Image | None:
        """画面に見えている画像のうち一番上のもの。見えていなければ記事の最初の画像。"""
        pics = list(self.body.query(".pic"))
        if not pics:
            hidden = not self.app.settings.images and self.body.query(ImageSlot)
            self.notify("画像を非表示にしています（i で表示）" if hidden else "この記事に画像はありません", timeout=2)
            return None
        top = self.body.scroll_y
        bottom = top + self.body.size.height
        visible = [p for p in pics if p.virtual_region.bottom > top and p.virtual_region.y < bottom]
        return (visible or pics)[0]

    async def action_copy_image(self) -> None:
        pic = self.visible_picture()
        if pic:
            await copy_image(self.app, *await original_image(self.app, pic))

    async def action_save_image(self) -> None:
        pic = self.visible_picture()
        if pic:
            save_image(self.app, *await original_image(self.app, pic))

    def action_bookmark(self) -> None:
        added = self.app.bookmarks.toggle(self.entry)
        self.notify("ブックマークしました" if added else "ブックマークを外しました", timeout=2)

    def action_gallery(self) -> None:
        self.app.push_screen(GalleryScreen(self.list_screen, article=self))

    async def on_click(self, event: events.Click) -> None:
        # 本文の画像をクリックすると、画像一覧と同じ拡大表示で開く（n / p で記事の中の前後の画像へ）
        node = event.widget
        while node is not None and node is not self and not node.has_class("pic"):
            node = node.parent
        if node is None or node is self or event.button != 1:
            return
        event.stop()
        await self.zoom_picture(node)

    async def zoom_picture(self, node, still: bool = False) -> None:
        """記事の画像を拡大表示で開く。アニメ GIF は mpv で再生する（still なら拡大表示で 1 コマ目）。"""
        if self.zooming:
            return
        self.zooming = True
        try:
            if not still and await play_animation(self.app, node):
                return
            img = await load_picture(self.app, node)
        finally:
            self.zooming = False
        if img is None:
            self.notify("画像を読めませんでした", severity="warning", timeout=2)
        elif self.app.screen is self:
            self.app.push_screen(PictureScreen(self, node, img))

    async def zoom_url(self, url: str, still: bool = False) -> None:
        """本文に文字で書かれた画像の URL を拡大表示で開く。記事の中の画像ではないので n / p では動かない。
        アニメ GIF は mpv で再生する（still なら拡大表示で 1 コマ目）。"""
        if self.zooming:
            return
        self.zooming = True
        referer = getattr(self, "page_url", self.entry.url)
        pic = SimpleNamespace(src=url, full="", path=None, referer=referer, entry=self.entry)
        try:
            pic.path = await feeds.fetch_image(self.app.http, url, referer)
            if not still and await play_animation(self.app, pic):
                return
            img = await load_picture(self.app, pic)
        except Exception as e:
            self.app.log(e)
            img = None
        finally:
            self.zooming = False
        if img is None:
            self.notify("画像を読めませんでした", severity="warning", timeout=2)
        elif self.app.screen is self:
            self.app.push_screen(PictureScreen(self, pic, img))

    # 拡大表示（PictureScreen）から画像一覧と同じように使うためのもの

    @property
    def tiles(self) -> list[Image]:
        return [p for p in self.body.query(".pic") if p.path]

    @property
    def tile_count(self) -> int:
        return len(self.tiles)

    def focus_index(self, index: int) -> None:
        tiles = self.tiles
        if tiles:
            self.body.scroll_to_widget(tiles[max(0, min(index, len(tiles) - 1))], animate=False)

    def action_open(self) -> None:
        pass  # もうこの記事を開いている

    def action_back(self) -> None:
        self.app.pop_screen()


# ---------------------------------------------------------------- 画像一覧

TILE_COLS = 32  # タイル 1 枚の幅（枠を含む桁数）。画面の幅をこれで割って列の数を決める
TILE_IMAGE_ROWS = 12  # タイルの画像部分の高さ（行数）
MIN_PICTURE = (200, 120)  # これより小さい画像（アイコンや区切り線）はタイルにしない
# タイルの画像は枠いっぱいではなく、この割合の大きさで描く。sixel で送る量は画像の面積に比例するので、
# 一覧は軽さを優先する（よく見たいときは Enter で拡大する）
TILE_PICTURE_SCALE = 0.4
# 画面に並べるタイルは画面 TILE_SCREENS 枚ぶん（少なくとも TILE_MIN 枚）まで。残りは手元に置いておき、
# カーソルが最後の行まで来たら次の分を並べる。並べたタイルが多いほど、画像を 1 枚差し込むたびの
# 配置の計算（Textual のレイアウト）とカーソルを動かしたときの描き直しが重くなるため
# （120 枚を全部並べると最初の 1 画面まで約 1.6 秒、j 6 回に約 1.9 秒かかっていた）
TILE_SCREENS = 3
TILE_MIN = 24


class Tile(Vertical):
    """画像一覧の 1 枚。画像の下に記事のタイトルを出す。

    カーソルはフォーカスではなく cursor クラスで示す。フォーカスを移すと外側の部品まで
    描き直され、見えている画像の sixel を全部送り直すため。
    """

    def __init__(self, entry: feeds.Entry, picture: feeds.Picture, referer: str, video: str = "") -> None:
        super().__init__()
        self.entry = entry
        self.video = video  # 動画一覧のタイルのときの動画の URL
        self.src = picture.src  # タイルに出す画像（縮小版のことがある）
        self.full = picture.full  # 元の画像へのリンク。拡大・コピー・保存で使う
        self.referer = referer
        self.path: Path | None = None  # 読み込めたらキャッシュのファイル

    def compose(self) -> ComposeResult:
        with Vertical(classes="tile-box"):
            yield Static("読み込み中…", classes="tile-slot")
        title = self.entry.title
        if self.video:
            title = ("▶ " if feeds.is_youtube(self.video) else "▶ 動画 ") + title
        yield Static(title, markup=False, classes="tile-title")

    async def on_click(self) -> None:
        self.screen.set_cursor(self)
        await self.screen.action_zoom()


class GalleryScreen(GG, Screen):
    """記事一覧に出ている記事の本文の画像を、タイル状に並べる。"""

    LABEL = "画像一覧"
    UNIT = "枚"
    IMAGE_PARALLEL = 6  # 画像を同時に取る数
    EMPTY = "画像のある記事はありませんでした（q で戻る）"

    BINDINGS = [
        Binding("l,right", "move(1, 0)", show=False),
        Binding("h,left", "move(-1, 0)", show=False),
        Binding("j,down", "move(0, 1)", show=False),
        Binding("k,up", "move(0, -1)", show=False),
        Binding("ctrl+d", "page(0.5)", show=False),
        Binding("ctrl+u", "page(-0.5)", show=False),
        Binding("ctrl+f,space", "page(1)", show=False),
        Binding("ctrl+b,shift+space,b", "page(-1)", show=False),
        Binding("G", "bottom", show=False),
        Binding("enter", "zoom", "拡大"),
        Binding("a", "open", "記事を開く"),
        Binding("y", "copy_image", "コピー"),
        Binding("Y", "save_image", "保存"),
        Binding("U", "app.copy_url", "URL をコピー", show=False),
        Binding("o", "browser", "ブラウザ"),
        Binding("z", "tile_size", "大きさ"),
        Binding("q,escape", "back", "戻る"),
        Binding("Q", "app.quit", "終了", show=False),
    ]

    def __init__(self, parent: EntryScreen | None, article: ArticleScreen | None = None) -> None:
        super().__init__()
        self.list_screen = parent  # None はページの画像一覧（matome --gallery URL）
        # 記事画面から開いたときは、その記事の画像だけを並べる
        self.article = article
        self.entries = [article.entry] if article else list(parent.entries) if parent else []
        self.done = 0  # 読み終えた記事の数
        # 画面に入れるのを待っているもの。1 つずつ入れると、そのたびに見えている画像を全部
        # 描き直して sixel を送り直すので、flush でまとめて入れる
        self.new_tiles: list[Tile] = []
        self.ready: list[tuple[Tile, Image]] = []
        self.dropped: list[Tile] = []
        self.held: list[Tile] = []  # まだ画面に並べていないタイル（画像の取得は進めておく）
        self.mount_limit = 0  # 画面に並べるタイルの上限。on_mount で決め、最後の行まで来たら増やす
        self.flushing = False
        self.cursor: Tile | None = None
        self.zooming = False  # 拡大の画像を読んでいる最中
        # 効き目の記録（MATOME_LOG=1）。開いてから最初のタイル・最初の 1 画面・全部がそろうまで
        self.opened = 0.0
        self.first_tile_ms: int | None = None
        self.first_screen_ms: int | None = None
        self.prefetched = 0  # 開いた時点で先読み済みだった記事
        self.images = 0
        self.images_on_disk = 0  # 開いた時点でキャッシュにあった画像
        self.logged = False

    def compose(self) -> ComposeResult:
        yield Header()
        with VerticalScroll(id="gallery", can_focus=False):
            yield Grid(id="tiles")
            yield Static("記事を読み込み中…", id="gallery-status")
        yield Footer()

    def on_mount(self) -> None:
        self.opened = time.perf_counter()
        self.mount_limit = self.screens_of_tiles()
        self.update_title()
        self.flush_timer = self.set_interval(0.4, self.flush)
        self.load()

    def screens_of_tiles(self) -> int:
        """画面 TILE_SCREENS 枚ぶんのタイルの数。開いた直後は部品の大きさがまだ無いので端末の大きさで見積もる。"""
        cols = max(1, (self.app.size.width - 2) // TILE_COLS)
        rows = max(1, (self.app.size.height - 2) // (TILE_IMAGE_ROWS + 3))
        return max(TILE_MIN, cols * rows * TILE_SCREENS)

    def show_more(self) -> bool:
        """手元に置いているタイルを、次の画面 TILE_SCREENS 枚ぶん並べる（次の flush で入る）。"""
        if not self.held:
            return False
        self.mount_limit = len(self.tiles) + self.screens_of_tiles()
        return True

    def elapsed_ms(self) -> int:
        return round((time.perf_counter() - self.opened) * 1000)

    def check_timing(self) -> None:
        """最初のタイルの画像・最初の 1 画面ぶんがそろった時刻を覚える。"""
        tiles = self.tiles
        if self.first_tile_ms is None and self.query(".tile-pic"):
            self.first_tile_ms = self.elapsed_ms()
        if self.first_screen_ms is None:
            rows = max(1, self.query_one("#gallery").size.height // (TILE_IMAGE_ROWS + 3))
            first = tiles[: rows * self.columns]
            all_articles = self.done == len(self.entries)
            if (len(first) == rows * self.columns or all_articles) and not any(t.query(".tile-slot") for t in first):
                self.first_screen_ms = self.elapsed_ms()

    def log_timing(self, finished: bool) -> None:
        if self.logged:
            return
        self.logged = True
        self.app.timing.write(
            "gallery", title=self.list_screen.title_text if self.list_screen else self.entries[0].url, finished=finished,
            articles=len(self.entries), read=self.done, prefetched=self.prefetched,
            tiles=len(self.tiles) if self.is_attached else None,
            images=self.images, on_disk=self.images_on_disk,
            first_tile_ms=self.first_tile_ms, first_screen_ms=self.first_screen_ms,
            done_ms=self.elapsed_ms() if finished else None,
        )

    def on_resize(self) -> None:
        self.query_one("#tiles", Grid).styles.grid_size_columns = self.columns

    def on_unmount(self) -> None:
        self.flush_timer.stop()
        self.log_timing(finished=False)  # 読み終わる前に閉じた

    async def flush(self) -> None:
        """たまったタイルと画像を、1 回の描き直しで画面に入れる。タイルは mount_limit 枚まで。"""
        room = self.mount_limit - len(self.tiles)
        if self.flushing or not (self.new_tiles or self.ready or self.dropped or (self.held and room > 0)):
            return
        if not self.is_attached:  # 画面を閉じたあと（読み込みの処理がまだ残っていることがある）
            return
        self.flushing = True
        # 届いたタイルは手元の列の後ろへ。画像を読めず消すことになったものは、並べる前なら列から外すだけ
        dropped = set(self.dropped)
        self.held = [t for t in self.held + self.new_tiles if t not in dropped]
        self.new_tiles, self.dropped = [], []
        new, self.held = self.held[:max(0, room)], self.held[max(0, room):]
        # 画像は、画面に入っている（入れる）タイルの分だけ。並べていないタイルの分は残しておく
        shown = set(new)
        ready = [(t, w) for t, w in self.ready if t.is_attached or t in shown]
        self.ready = [(t, w) for t, w in self.ready if not (t.is_attached or t in shown)]
        dropped = [t for t in dropped if t.is_attached]
        try:
            with self.app.batch_update():
                if new:
                    await self.query_one("#tiles", Grid).mount_all(new)
                    if self.current() is None:
                        self.set_cursor(new[0], scroll=False)
                for tile, widget in ready:
                    # 入れている途中で画面が閉じられると、タイルの中身が片付けられていく
                    if not (self.is_attached and tile.is_attached):
                        return
                    slot, box = tile.query(".tile-slot"), tile.query(".tile-box")
                    if not (slot and box):
                        continue
                    try:
                        await slot.first().remove()
                        await box.first().mount(widget)
                    except (NoMatches, MountError):  # 後片付けで中身が消えた
                        return
                for tile in dropped:
                    if self.is_attached and tile.is_attached:
                        await self.drop(tile)
        finally:
            self.flushing = False
        self.update_title()
        self.check_timing()

    @property
    def columns(self) -> int:
        return max(1, (self.size.width - 2) // TILE_COLS)

    @property
    def tiles(self) -> list[Tile]:
        return list(self.query(Tile))

    @property
    def tile_count(self) -> int:
        """並べたタイルと、まだ並べていないタイルの合計。"""
        return len(self.tiles) + len(self.held) + len(self.new_tiles)

    def update_title(self) -> None:
        loading = f"  記事 {self.done}/{len(self.entries)} を読み込み中" if self.done < len(self.entries) else ""
        self.app.sub_title = f"{self.LABEL}  {self.tile_count} {self.UNIT}{loading}"

    @work(exclusive=True)
    async def load(self) -> None:
        pages = asyncio.Semaphore(4)
        images = asyncio.Semaphore(self.IMAGE_PARALLEL)

        async def fetch(e: feeds.Entry) -> feeds.Article | None:
            if self.app.articles.is_ready(e.url):
                self.prefetched += 1
            async with pages:
                try:
                    return await self.fetch_article(e)
                except httpx.HTTPError as err:
                    self.log(err)
                    return None

        async def fill(tile: Tile) -> None:
            async with images:
                await self.load_image(tile)

        # 記事は並行して取るが、タイルは一覧の順に並べる
        tasks = [asyncio.create_task(fetch(e)) for e in self.entries]
        loads = []
        for e, task in zip(self.entries, tasks):
            article = await task
            self.done += 1
            if article:
                new = self.make_tiles(e, article)
                self.new_tiles.extend(new)
                loads.extend(asyncio.create_task(fill(t)) for t in new)
        await asyncio.gather(*loads)
        while self.flushing:
            await asyncio.sleep(0.05)
        await self.flush()
        self.flush_timer.stop()
        if not self.is_attached:
            return
        self.check_timing()
        self.log_timing(finished=True)
        status = self.query_one("#gallery-status", Static)
        if self.tiles:
            await status.remove()
        else:
            status.update(self.EMPTY)

    async def fetch_article(self, e: feeds.Entry) -> feeds.Article:
        return await self.app.articles.get(e, kind="gallery" if type(self) is GalleryScreen else "videos")

    def action_tile_size(self) -> None:
        settings = self.app.settings
        settings.tile_full = not settings.tile_full
        settings.save()
        self.notify(f"タイルの画像: {'枠いっぱい' if settings.tile_full else '小さめ（軽い）'}", timeout=2)
        self.redraw_tiles()

    @work(exclusive=True, group="tile-size")
    async def redraw_tiles(self) -> None:
        """読み込んだタイルの画像を、今の大きさの設定で作り直す（画像はキャッシュから読む）。"""
        tiles = [t for t in self.tiles if t.path and t.query(".tile-pic")]
        # まだ並べていないタイルの、作っておいた画像も作り直す
        waiting = [t for t, _ in self.ready if t not in tiles and not t.is_attached and t.path]
        self.ready = [(t, w) for t, w in self.ready if t not in waiting]
        tiles += waiting
        if not tiles:
            return
        timer = self.set_interval(0.4, self.flush)
        sem = asyncio.Semaphore(self.IMAGE_PARALLEL)

        async def redo(tile: Tile) -> None:
            async with sem:
                await self.load_image(tile)

        try:
            with self.app.batch_update():
                for tile in tiles:
                    if not tile.is_attached:
                        continue
                    pics, box = tile.query(".tile-pic"), tile.query(".tile-box")
                    if not (pics and box):
                        continue
                    await pics.first().remove()
                    await box.first().mount(Static("読み込み中…", classes="tile-slot"))
            # 見えているあたり（カーソルの近く）から作り直す
            cur = self.current()
            if cur in tiles:
                i = tiles.index(cur)
                tiles = tiles[i:] + tiles[:i]
            await asyncio.gather(*(redo(t) for t in tiles))
            while self.flushing:
                await asyncio.sleep(0.05)
            await self.flush()
        finally:
            timer.stop()

    def make_tiles(self, e: feeds.Entry, article: feeds.Article) -> list[Tile]:
        pictures = {b.src: b for b in article.blocks if isinstance(b, feeds.Picture)}
        return [Tile(e, pic, article.url) for pic in pictures.values()]

    def no_image(self, tile: Tile) -> None:
        """画像を読めなかった・小さすぎたタイル。画像一覧ではタイルごと消す。"""
        self.dropped.append(tile)

    async def load_image(self, tile: Tile) -> None:
        self.images += 1
        self.images_on_disk += feeds.image_path(tile.src).exists()
        try:
            path = await feeds.fetch_image(self.app.http, tile.src, tile.referer)
            img = await asyncio.to_thread(_prepare_image, path)
        except Exception as e:  # 壊れた画像や 404 はタイルごと消す
            self.log(e)
            img = None
        if img is None or img.width < MIN_PICTURE[0] or img.height < MIN_PICTURE[1]:
            self.no_image(tile)
            return
        # タイルの画像部分に収まる大きさにして、縦横の比は変えない
        cell = get_cell_size()
        cw, ch = max(cell.width, 1), max(cell.height, 1)
        box_w = TILE_COLS - 4  # 列の幅は画面の幅しだいだが、枠と余白を除いてもこれだけは必ずある
        # ふだんは軽さを優先して小さめ。z で枠いっぱいにできる（送る sixel は約 6 倍になる）
        shrink = 1.0 if self.app.settings.tile_full else TILE_PICTURE_SCALE
        scale = min(box_w * cw / img.width, TILE_IMAGE_ROWS * ch / img.height, 1.0) * shrink
        img.thumbnail((max(1, int(img.width * scale)), max(1, int(img.height * scale))))
        widget = Image(img, classes="tile-pic")
        widget.styles.width = max(1, min(box_w, math.ceil(img.width / cw)))
        widget.styles.height = max(1, min(TILE_IMAGE_ROWS, math.ceil(img.height / ch)))
        tile.path = path
        self.ready.append((tile, widget))

    async def drop(self, tile: Tile) -> None:
        if tile is self.cursor:
            tiles = self.tiles
            i = tiles.index(tile)
            rest = tiles[i + 1:] or tiles[:i][-1:]
            self.cursor = None
            if rest:
                self.set_cursor(rest[0], scroll=False)
        await tile.remove()
        self.update_title()

    def current(self) -> Tile | None:
        return self.cursor if self.cursor is not None and self.cursor.is_mounted else None

    PAGE_LABEL = "記事"  # Ctrl+g でタイルの元のページに付ける名前

    def url_info(self) -> list[tuple[str, str]]:
        tile = self.current()
        if not tile:
            return []
        return [(self.PAGE_LABEL, tile.referer), ("動画" if tile.video else "画像", tile.video or tile.full or tile.src)]

    def set_cursor(self, tile: Tile, scroll: bool = True, top: bool = False) -> None:
        if self.cursor is not None:
            self.cursor.remove_class("cursor")
        self.cursor = tile
        tile.add_class("cursor")
        if scroll:
            # スクロールのアニメーションは、途中のコマごとに画像の切り取りが変わって sixel を
            # 作り直すので使わない
            self.query_one("#gallery").scroll_to_widget(tile, animate=False, top=top)
        # 最後の行まで来たら、手元のタイルを次の分だけ並べる
        tiles = self.tiles
        if self.held and tile in tiles and tiles.index(tile) >= len(tiles) - self.columns and self.show_more():
            self.call_after_refresh(self.flush)

    def focus_index(self, index: int, top: bool = False) -> None:
        tiles = self.tiles
        if tiles:
            self.set_cursor(tiles[max(0, min(index, len(tiles) - 1))], top=top)

    def action_move(self, dx: int, dy: int) -> None:
        tile = self.current()
        if not tile:
            self.focus_index(0)
            return
        i = self.tiles.index(tile) + dx + dy * self.columns
        if 0 <= i < len(self.tiles):
            self.focus_index(i)

    def action_page(self, ratio: float) -> None:
        """画面 ratio 枚ぶんの行だけカーソルを動かす（記事画面の Space / b と同じ感覚）。"""
        tile = self.current()
        rows_on_screen = self.query_one("#gallery").size.height // (TILE_IMAGE_ROWS + 3)
        rows = max(1, int(rows_on_screen * abs(ratio)))
        if tile:
            step = rows * self.columns * (1 if ratio > 0 else -1)
            # ページ送りはカーソルの行を画面の上にそろえる（端で切れて描かれないタイルを減らす）
            self.focus_index(self.tiles.index(tile) + step, top=True)

    def action_top(self) -> None:
        self.focus_index(0)

    def action_bottom(self) -> None:
        self.focus_index(len(self.tiles) - 1)

    def action_open(self) -> None:
        tile = self.current()
        if self.article:
            self.app.pop_screen()  # 記事画面に戻る
        elif tile and self.list_screen and tile.entry in self.list_screen.entries:
            self.list_screen.open_article(self.list_screen.entries.index(tile.entry))

    def action_browser(self) -> None:
        tile = self.current()
        if tile:
            open_in_browser(tile.entry.url)

    async def action_copy_image(self) -> None:
        tile = self.current()
        if tile:
            await copy_image(self.app, *await original_image(self.app, tile))

    async def action_save_image(self) -> None:
        tile = self.current()
        if tile:
            save_image(self.app, *await original_image(self.app, tile))

    async def action_zoom(self) -> None:
        tile = self.current()
        if not tile or not tile.path or self.zooming:
            return
        self.zooming = True
        try:
            if await play_animation(self.app, tile):
                return
            img = await load_picture(self.app, tile)
        finally:
            self.zooming = False
        if img is None:
            self.notify("画像を読めませんでした", severity="warning", timeout=2)
        elif self.app.screen is self:  # 読んでいるあいだに別の画面へ移っていなければ
            self.app.push_screen(PictureScreen(self, tile, img))

    def on_screen_resume(self) -> None:
        self.update_title()

    def action_back(self) -> None:
        self.app.pop_screen()



class PageGalleryScreen(GalleryScreen):
    """1 つのページ（URL）の画像を全部並べる。w3m などから matome --gallery URL で開く。q で終わる。"""

    LABEL = "ページの画像"
    PAGE_LABEL = "ページ"
    IMAGE_PARALLEL = 10  # 1 つのサイトから画像だけを取るので、記事一覧の画像一覧より多めに
    EMPTY = "このページに画像はありませんでした（q で終わる）"

    def __init__(self, url: str) -> None:
        super().__init__(None)
        self.url = url
        self.entries = [feeds.Entry(feeds.Site(name="", feed=url), url, url, time.time(), "")]

    async def fetch_article(self, e: feeds.Entry) -> feeds.Article:
        entry, article = await feeds.fetch_page_pictures(self.app.http, e.url)
        e.title, e.url = entry.title, entry.url  # タイルの下に出すページのタイトル
        self.app.title = f"matome  {entry.title}"
        return article

    def action_open(self) -> None:
        self.notify("o でブラウザで開けます", timeout=2)

    def action_back(self) -> None:
        self.app.exit()


class SearchScreen(GalleryScreen):
    """検索の結果をタイルで並べる画面の土台。q で終わる。

    search で first 件目（1 から）からの結果を取り、_tiles_for でタイルにする。hit_key が同じ結果は 2 度並べない。
    いちばん下の行までカーソルを進めると、続きを読む。
    MatomeApp(start=...) に渡せば、matome の外で書いた検索も最初の画面にできる。
    """

    LABEL = "検索"
    PAGE_LABEL = "ページ"
    PAGE = 20  # search 1 回で取る件数（続きの first をこれだけ進める）
    IMAGE_PARALLEL = 10  # サムネイルはたいてい同じ CDN から取る
    EMPTY = "見つかりませんでした（q で終わる）"

    def __init__(self, query: str) -> None:
        super().__init__(None)
        self.query_text = query
        self.entries = [feeds.Entry(feeds.Site(name="", feed=""), query, "", time.time(), "")]
        self.next_first = 1
        self.more = True  # まだ続きがありそうか
        self.loading_more = False
        self.seen: set[str] = set()

    async def search(self, first: int) -> list:
        raise NotImplementedError

    def hit_key(self, hit) -> str:
        raise NotImplementedError

    def _tiles_for(self, hits: list) -> list[Tile]:
        raise NotImplementedError

    def on_mount(self) -> None:
        # GalleryScreen.on_mount は Textual がこのあとに呼ぶ（super() で呼ぶと読み込みが 2 回走る）
        self.app.title = f"matome  {self.LABEL}: {self.query_text}"

    async def fetch_article(self, e: feeds.Entry) -> feeds.Article:
        return feeds.Article(e.url, [])  # 実際の結果は make_tiles で読む（hits）

    async def _search(self) -> list:
        hits = await self.search(self.next_first)
        self.next_first += self.PAGE
        fresh = [h for h in hits if self.hit_key(h) not in self.seen]
        self.seen |= {self.hit_key(h) for h in fresh}
        self.more = bool(fresh)
        return fresh

    @work(exclusive=True)
    async def load(self) -> None:
        hits = await self._search()
        self.done = 1
        await self._add(hits)
        self.flush_timer.stop()
        if not self.is_attached:
            return
        status = self.query_one("#gallery-status", Static)
        if self.tiles:
            await status.remove()
        else:
            status.update(self.EMPTY)

    async def _add(self, hits: list) -> None:
        images = asyncio.Semaphore(self.IMAGE_PARALLEL)

        async def fill(tile: Tile) -> None:
            async with images:
                await self.load_image(tile)

        new = self._tiles_for(hits)
        # 続きの検索結果は、並べている分を使い切ってから読むので、すぐ並べられるように枠を広げる
        self.mount_limit = max(self.mount_limit, len(self.tiles) + self.screens_of_tiles())
        self.new_tiles.extend(new)
        await asyncio.gather(*(fill(t) for t in new))
        while self.flushing:
            await asyncio.sleep(0.05)
        await self.flush()

    @work(group="more")
    async def load_more(self) -> None:
        self.loading_more = True
        self.app.sub_title = f"{self.LABEL}  {self.tile_count} {self.UNIT}  続きを読み込み中…"
        timer = self.set_interval(0.4, self.flush)
        try:
            await self._add(await self._search())
        finally:
            timer.stop()
            self.loading_more = False
            if self.is_attached:
                self.update_title()

    def set_cursor(self, tile: Tile, scroll: bool = True, top: bool = False) -> None:
        super().set_cursor(tile, scroll, top)
        tiles = self.tiles
        if self.more and not self.loading_more and self.done and not self.held and not self.new_tiles \
                and tile in tiles and tiles.index(tile) >= len(tiles) - self.columns:
            self.load_more()

    def log_timing(self, finished: bool) -> None:
        pass  # 記録は記事の画像一覧だけ

    def action_open(self) -> None:
        self.notify("o でブラウザで開けます", timeout=2)

    def action_back(self) -> None:
        self.app.exit()


class VideoScreen(GalleryScreen):
    """記事一覧に出ている記事の本文の動画を、サムネイルのタイルで並べる。Enter で再生する。

    サムネイルは YouTube なら YouTube の画像、それ以外は記事の最初の画像（無ければ文字だけ）。
    """

    LABEL = "動画一覧"
    UNIT = "本"
    EMPTY = "動画のある記事はありませんでした（q で戻る）"
    BINDINGS = [
        Binding("enter", "zoom", "再生"),
        Binding("y,Y", "app.bell", show=False),  # 画像一覧のコピー・保存は使わない
    ]

    def make_tiles(self, e: feeds.Entry, article: feeds.Article) -> list[Tile]:
        first = next((b.src for b in article.blocks if isinstance(b, feeds.Picture)), "")
        tiles = []
        for b in article.blocks:
            if isinstance(b, feeds.Video):
                vid = feeds.youtube_id(b.src)
                thumb = f"https://i.ytimg.com/vi/{vid}/hqdefault.jpg" if vid else first
                tiles.append(Tile(e, feeds.Picture(thumb), article.url, video=b.src))
        return tiles

    def no_image(self, tile: Tile) -> None:
        # 動画は見られるので、タイルは消さずに文字だけにする
        self.ready.append((tile, Static("▶ 画像なし", classes="tile-slot")))

    async def load_image(self, tile: Tile) -> None:
        if tile.src:
            await super().load_image(tile)
        else:
            self.no_image(tile)

    def log_timing(self, finished: bool) -> None:
        pass  # 記録は画像一覧だけ

    async def action_zoom(self) -> None:
        tile = self.current()
        if tile:
            open_video(tile.video)
            self.notify("動画を開いています…", timeout=2)


PICTURE_SETTLE = 0.3  # 拡大表示を開いてから画像を出すまでの秒数
PICTURE_MAX_PIXELS = 4096  # 拡大表示で読む画像の最大の辺。元画像を拡大して見られるよう、記事の中より大きく読む
ZOOM_STEP = 1.25  # + / - 1 回の倍率
ZOOM_MIN, ZOOM_MAX = 0.05, 8.0  # 元のサイズに対する倍率の範囲
PAN_STEP = 0.25  # h/j/k/l 1 回で動く量（見えている幅・高さに対する割合）


async def load_picture(app: App, tile: Tile) -> PILImage.Image | None:
    """拡大表示に使う画像を読む（元の画像へのリンクがあればそちら）。拡大して見るので大きめに読む。"""
    path, _ = await original_image(app, tile)
    if not path:
        return None
    try:
        return await asyncio.to_thread(_prepare_image, path, PICTURE_MAX_PIXELS)
    except Exception as e:
        app.log(e)
        return None


class PictureScreen(Screen[None]):
    """タイルの画像を 1 枚出す。最初は元の大きさ（画面に入りきらなければ画面いっぱいまで縮める）。

    + / -（または Ctrl+ホイール）で拡大・縮小、0 で元のサイズ（画像の 1 ピクセル = 画面の 1 ピクセル）、f で画面に合わせる。
    画面からはみ出しているあいだは h/j/k/l・矢印で見る場所を動かす（収まっているときの h/l は前／次の画像）。
    拡大しても見えている部分だけを切り出して描くので、送る sixel は画面 1 枚ぶんを超えない。

    背景は無地にする。モーダルにして画像一覧を透かしても、後ろの画面の sixel は描かれず
    タイルの枠だけが残って見えるため。

    画像は開く前に読んでおき、compose で一度に組み立てる。開いてから画像を差し込むと、
    大きさの計算が何度もやり直しになり、そのたびに sixel を送り直してちらつくため。
    次の画像へ進むときも、新しい画面に差し替える。
    """

    BINDINGS = [
        Binding("n", "step(1)", "次の画像"),
        Binding("p", "step(-1)", "前の画像"),
        Binding("l,right", "move(1, 0)", show=False),
        Binding("h,left", "move(-1, 0)", show=False),
        Binding("j,down", "move(0, 1)", show=False),
        Binding("k,up", "move(0, -1)", show=False),
        Binding("plus,equals_sign", "zoom(1)", "拡大", key_display="+"),
        Binding("minus", "zoom(-1)", "縮小", key_display="-"),
        Binding("0", "actual_size", "元のサイズ"),
        Binding("f", "fit", "画面に合わせる"),
        Binding("a", "open", "記事を開く", show=False),
        Binding("y", "copy_image", "コピー", show=False),
        Binding("Y", "save_image", "保存", show=False),
        Binding("U", "app.copy_url", "URL をコピー", show=False),
        Binding("q,escape,enter", "close", "閉じる"),
    ]

    def __init__(self, gallery: GalleryScreen | ArticleScreen, tile: Tile | Image, img: PILImage.Image) -> None:
        super().__init__()
        self.gallery = gallery  # 画像一覧か、本文の画像をクリックしたときはその記事
        self.tile = tile
        self.img = img
        self.stepping = False
        self.zoom: float | None = None  # 元のサイズに対する倍率。None は画面に合わせる
        self.cx, self.cy = img.width / 2, img.height / 2  # 見ている場所の中心（画像のピクセル）
        self.rendering = False
        self.pending = False

    def url_info(self) -> list[tuple[str, str]]:
        t = self.tile
        page = getattr(t, "referer", "")
        if isinstance(self.gallery, GalleryScreen):
            page_label = self.gallery.PAGE_LABEL
        else:
            page_label = "記事"
        return [(page_label, page), ("画像", getattr(t, "full", "") or getattr(t, "src", ""))]

    # --- 見えている部分の計算

    def _cell(self) -> tuple[int, int]:
        cell = get_cell_size()
        return max(cell.width, 1), max(cell.height, 1)

    def _view_px(self) -> tuple[int, int]:
        """画像に使える広さ（ピクセル）。タイトルの 1 行と余白を除く。"""
        cw, ch = self._cell()
        return (self.app.size.width - 2) * cw, (self.app.size.height - 2) * ch

    def fit_scale(self) -> float:
        vw, vh = self._view_px()
        return min(vw / self.img.width, vh / self.img.height, 1.0)

    @property
    def scale(self) -> float:
        return self.fit_scale() if self.zoom is None else self.zoom

    def overflows(self) -> tuple[bool, bool]:
        """横・縦に画面からはみ出しているか。"""
        vw, vh = self._view_px()
        s = self.scale
        return self.img.width * s > vw + 1, self.img.height * s > vh + 1

    def _clamp(self) -> None:
        """見る場所が画像の外に出ないようにする。"""
        vw, vh = self._view_px()
        s = self.scale
        half_w, half_h = min(vw / s, self.img.width) / 2, min(vh / s, self.img.height) / 2
        self.cx = min(max(self.cx, half_w), self.img.width - half_w)
        self.cy = min(max(self.cy, half_h), self.img.height - half_h)

    def view(self) -> tuple[PILImage.Image, int, int]:
        """見えている部分を切り出した画像と、その大きさ（桁・行）。"""
        cw, ch = self._cell()
        vw, vh = self._view_px()
        s = self.scale
        self._clamp()
        dw, dh = min(self.img.width * s, vw), min(self.img.height * s, vh)  # 画面に出す大きさ（ピクセル）
        sw, sh = dw / s, dh / s  # 画像から切り出す大きさ
        left, top = self.cx - sw / 2, self.cy - sh / 2
        box = (round(left), round(top), round(left + sw), round(top + sh))
        out = (max(1, round(dw)), max(1, round(dh)))
        if box == (0, 0, self.img.width, self.img.height) and out == self.img.size:
            part = self.img
        else:
            part = self.img.resize(out, PILImage.Resampling.LANCZOS if s < 1 else PILImage.Resampling.BICUBIC, box=box)
        return part, max(1, math.ceil(dw / cw)), max(1, math.ceil(dh / ch))

    def title_text(self) -> str:
        tiles = self.gallery.tiles
        pos = f"{tiles.index(self.tile) + 1}/{self.gallery.tile_count}  " if self.tile in tiles else ""
        mode = "画面に合わせる " if self.zoom is None else ""
        return f"{pos}{mode}{round(self.scale * 100)}%  {self.tile.entry.title}"

    def compose(self) -> ComposeResult:
        part, width, height = self.view()
        widget = Image(part, id="picture-img")
        widget.styles.width, widget.styles.height = width, height
        widget.hold = True  # on_mount の説明を参照
        title = Static(self.title_text(), markup=False, id="picture-title")
        title.styles.width = max(width, 20)
        # 中身に合わせる（auto）と大きさの計算を何度もやり直すので、大きさは決め打ちにする
        with Vertical(id="picture") as box:
            box.styles.width = max(width, 20)
            box.styles.height = height + 1
            yield widget
            yield title

    def on_mount(self) -> None:
        # 画面を開いた直後は Textual が何度か描き直すので、画像はそのあいだ隠しておき、
        # 落ち着いてから 1 回だけ出す（そうしないと sixel を何度も送り直してちらつく）
        self.set_timer(PICTURE_SETTLE, self.reveal)

    def reveal(self) -> None:
        widget = self.query_one("#picture-img")
        widget.hold = False
        for child in widget.children:  # 画像の部分だけを描き直す（大きさは変わらない）
            child.refresh()

    async def redraw(self) -> None:
        """倍率か見る場所が変わったので描き直す。キーを続けて押したときは最後の状態だけ描く。"""
        if self.rendering:
            self.pending = True
            return
        self.rendering = True
        try:
            while True:
                self.pending = False
                part, width, height = await asyncio.to_thread(self.view)
                if not self.is_attached:
                    return
                if self.pending:  # 作っているあいだにまたキーが押された
                    continue
                widget = self.query_one("#picture-img")
                with self.app.batch_update():
                    widget.styles.width, widget.styles.height = width, height
                    box = self.query_one("#picture")
                    box.styles.width = max(width, 20)
                    box.styles.height = height + 1
                    title = self.query_one("#picture-title", Static)
                    title.styles.width = max(width, 20)
                    title.update(self.title_text())
                    widget.image = part
                if not self.pending:
                    return
        finally:
            self.rendering = False

    async def action_zoom(self, direction: int) -> None:
        s = self.scale * (ZOOM_STEP if direction > 0 else 1 / ZOOM_STEP)
        self.zoom = min(max(s, ZOOM_MIN), ZOOM_MAX)
        await self.redraw()

    # Ctrl+ホイールでも拡大・縮小する（ホイールだけのときは何もしない）
    async def on_mouse_scroll_up(self, event: events.MouseScrollUp) -> None:
        if event.ctrl:
            event.stop()
            await self.action_zoom(1)

    async def on_mouse_scroll_down(self, event: events.MouseScrollDown) -> None:
        if event.ctrl:
            event.stop()
            await self.action_zoom(-1)

    async def action_actual_size(self) -> None:
        self.zoom = 1.0
        await self.redraw()

    async def action_fit(self) -> None:
        self.zoom = None
        self.cx, self.cy = self.img.width / 2, self.img.height / 2
        await self.redraw()

    async def action_move(self, dx: int, dy: int) -> None:
        over_x, over_y = self.overflows()
        if dx and not over_x:
            if not over_y:  # 収まっているときの h/l は前／次の画像
                await self.action_step(dx)
            return
        if dy and not over_y:
            return
        vw, vh = self._view_px()
        s = self.scale
        self.cx += dx * vw / s * PAN_STEP
        self.cy += dy * vh / s * PAN_STEP
        await self.redraw()

    async def action_step(self, step: int) -> None:
        if self.stepping:
            return
        tiles = [t for t in self.gallery.tiles if t.path]
        if self.tile not in tiles:
            return
        i = tiles.index(self.tile) + step
        if not 0 <= i < len(tiles):
            return
        self.stepping = True
        tile = tiles[i]
        img = await load_picture(self.app, tile)
        self.stepping = False
        if img is None:
            self.notify("画像を読めませんでした", severity="warning", timeout=2)
            return
        self.gallery.focus_index(self.gallery.tiles.index(tile))
        self.app.switch_screen(PictureScreen(self.gallery, tile, img))

    async def action_copy_image(self) -> None:
        await copy_image(self.app, *await original_image(self.app, self.tile))

    async def action_save_image(self) -> None:
        save_image(self.app, *await original_image(self.app, self.tile))

    def action_open(self) -> None:
        self.dismiss(None)
        self.gallery.action_open()

    def action_close(self) -> None:
        self.dismiss(None)


def _prepare_image(path, limit: int = 1000) -> PILImage.Image:
    img = PILImage.open(path)
    img.seek(0)  # アニメ GIF は 1 枚目だけ
    img = img.convert("RGB")
    img.thumbnail((limit, limit))
    return img


class ContextMenu(ModalScreen["int | None"]):
    """右クリックのメニュー。クリックした場所の近くに出す。外をクリックするか Esc で閉じる。"""

    BINDINGS = [
        Binding("escape,q", "close", "閉じる"),
        Binding("j,n", "move(1)", show=False),
        Binding("k,p", "move(-1)", show=False),
    ]
    DEFAULT_CSS = """
    ContextMenu { background: transparent; }
    ContextMenu OptionList { width: auto; height: auto; max-height: 20; border: round $accent; background: $surface; padding: 0; }
    """

    def __init__(self, labels: list[str], x: int, y: int) -> None:
        super().__init__()
        self.labels = labels
        self.at = (x, y)

    def compose(self) -> ComposeResult:
        yield OptionList(*self.labels)

    def on_mount(self) -> None:
        menu = self.query_one(OptionList)
        width = max(cell_len(label) for label in self.labels) + 4
        height = len(self.labels) + 2
        # 画面からはみ出すときは、クリックした場所の左・上に出す
        x, y = self.at
        if x + width > self.app.size.width:
            x = max(0, x - width)
        if y + height > self.app.size.height:
            y = max(0, y - height)
        menu.styles.offset = (x, y)
        menu.highlighted = 0
        menu.focus()

    def on_option_list_option_selected(self, event: OptionList.OptionSelected) -> None:
        self.dismiss(event.option_index)

    def action_move(self, step: int) -> None:
        menu = self.query_one(OptionList)
        menu.action_cursor_down() if step > 0 else menu.action_cursor_up()

    def on_click(self, event: events.Click) -> None:
        if event.widget is self:  # メニューの外
            self.dismiss(None)

    def action_close(self) -> None:
        self.dismiss(None)


def picture_items(app: App, screen: "ArticleScreen", pic) -> list[tuple[str, object]]:
    async def copy():
        await copy_image(app, *await original_image(app, pic))

    async def save():
        save_image(app, *await original_image(app, pic))

    image_url = getattr(pic, "full", "") or getattr(pic, "src", "")
    items = [("拡大", lambda: screen.zoom_picture(pic)), ("画像をコピー", copy), ("画像を保存", save),
             ("画像の URL を表示", lambda: show_url(app, [("画像", image_url)]))]
    if is_gif(pic.full or pic.src) and can_show_window():  # アニメ GIF は mpv で再生になるので、止まった絵でも見られるように
        items[0] = ("拡大（アニメなら mpv で再生）", items[0][1])
        items.insert(1, ("1 コマ目を拡大", lambda: screen.zoom_picture(pic, still=True)))
    return items


def link_items(app: App, url: str) -> list[tuple[str, object]]:
    kind = url_kind(url)
    screen = app.screen
    if kind == "picture" and isinstance(screen, ArticleScreen):
        items = [("拡大", lambda: screen.zoom_url(url)), ("URL をコピー", lambda: copy_url(app, url)),
                 ("URL を表示", lambda: show_url(app, [("URL", url)])), ("w3m で開く", lambda: open_link(app, url))]
        if is_gif(url) and can_show_window():
            items[0] = ("拡大（アニメなら mpv で再生）", items[0][1])
            items.insert(1, ("1 コマ目を拡大", lambda: screen.zoom_url(url, still=True)))
        return items
    show = ("URL を表示", lambda: show_url(app, [("URL", url)]))
    if kind == "video":
        return [("再生", lambda: open_url(app, url)), ("URL をコピー", lambda: copy_url(app, url)), show]
    return [("w3m で開く", lambda: open_link(app, url)), ("URL をコピー", lambda: copy_url(app, url)), show]


def context_items(app: App, x: int, y: int) -> list[tuple[str, object]]:
    """右クリックした場所に合ったメニューの中身（表示, 呼ぶもの）。呼ぶものは引数なしの関数（async でもよい）。"""
    screen = app.screen
    try:
        widget, _ = screen.get_widget_at(x, y)
        style = screen.get_style_at(x, y)
    except Exception:
        widget, style = None, None
    nodes = list(widget.ancestors_with_self) if widget is not None else []

    def find(kind=None, cls=None):
        return next((n for n in nodes if (kind and isinstance(n, kind)) or (cls and n.has_class(cls))), None)

    url = style.meta.get("url") if style is not None else None
    if url:
        return link_items(app, url)

    pic = find(cls="pic")
    if pic is not None and isinstance(screen, ArticleScreen):
        return picture_items(app, screen, pic)

    tile = find(kind=Tile)
    if tile is not None and isinstance(screen, GalleryScreen):
        screen.set_cursor(tile, scroll=False)
        video = bool(tile.video)
        items = [("再生" if video else "拡大", screen.action_zoom)]
        if not isinstance(screen, (SearchScreen, PageGalleryScreen)):
            items.append(("記事を開く", screen.action_open))
        if not video:
            items += [("画像をコピー", screen.action_copy_image), ("画像を保存", screen.action_save_image)]
        items += [("ブラウザで開く", screen.action_browser),
                  ("URL をコピー", app.action_copy_url), ("URL を表示", app.action_show_url)]
        return items

    entry = find(kind=EntryItem)
    if entry is not None and isinstance(screen, EntryScreen):
        screen.lv.index = list(screen.lv.children).index(entry)
        marked = app.bookmarks.has(entry.entry.url)
        return [
            ("開く", screen.action_open),
            ("ブックマークを外す" if marked else "ブックマーク", screen.action_bookmark),
            ("URL をコピー", app.action_copy_url),
            ("URL を表示", app.action_show_url),
            ("ブラウザで開く", screen.action_browser),
        ]

    site = find(kind=SiteItem)
    if site is not None and isinstance(screen, SiteScreen) and site.kind == "site":
        screen.lv.index = list(screen.lv.children).index(site)
        return [("開く", screen.action_open), ("URL をコピー", app.action_copy_url), ("URL を表示", app.action_show_url)]

    if isinstance(screen, PictureScreen):
        return [("閉じる", screen.action_close), ("記事を開く", screen.action_open),
                ("画像をコピー", screen.action_copy_image), ("画像を保存", screen.action_save_image),
                ("URL をコピー", app.action_copy_url), ("URL を表示", app.action_show_url)]

    # それ以外は「戻る」（最初の画面の q は終了なので出さない）
    items = []
    action = right_click_action(screen)
    if action and len(app.screen_stack) > 2:
        items.append(("戻る", lambda: screen.run_action(action)))
    if url_info(screen):  # 記事の文字のところなど
        items += [("URL をコピー", app.action_copy_url), ("URL を表示", app.action_show_url)]
    if hasattr(screen, "action_keys"):
        items.append(("キー一覧", screen.action_keys))
    return items


def right_click_action(screen: Screen) -> str | None:
    """中クリックで動かす操作。その画面で q に割り当てた操作（親のクラスの割り当ても見る）。"""
    for cls in type(screen).__mro__:
        for binding in cls.__dict__.get("BINDINGS", []):
            if isinstance(binding, Binding) and "q" in binding.key.split(","):
                return binding.action
    return None


class MatomeApp(App):
    TITLE = "matome"
    # どの画面でも：U でカーソルのところの URL をコピー、Ctrl+g で URL を表示（vim の Ctrl-g のように情報を出すだけ）
    BINDINGS = [
        Binding("U", "copy_url", show=False),
        Binding("ctrl+g", "show_url", show=False),
    ]
    CSS = """
    ListView > ListItem.read Label { color: $text-disabled; }
    #body { padding: 0 2; }
    #title { text-style: bold; color: $accent; margin: 1 0 0 0; }
    #meta { color: $text-muted; margin-bottom: 1; }
    .text { margin-bottom: 1; }
    .quote {
        border-left: thick $primary;
        padding-left: 1;
        margin-bottom: 1;
        color: $text-muted;
    }
    .slot { color: $text-muted; margin-bottom: 1; }
    .pic { margin-bottom: 1; }
    /* Tab で選んだ画像：画像の下の余白 1 行を印の行に入れ替える（枠は sixel に上から描かれて見えないため。
       行の数は変わらないので、下の本文や画像はずれず、画像も描き直されない） */
    .pic.picked { margin-bottom: 0; }
    .pick-mark { height: 1; color: $accent; text-style: bold reverse; }
    .video { color: $accent; margin-bottom: 1; }
    .video:hover { text-style: underline; }
    #comments-head { text-style: bold; margin: 1 0; }
    .c-head { color: $success; }
    .c-body { margin-bottom: 1; padding-left: 2; }
    AddSiteScreen, AddShortScreen, ConfirmScreen, GroupScreen, KeysScreen, PathScreen { align: center middle; }
    #keys-title { text-style: bold; margin-bottom: 1; }
    #dialog {
        width: 80%;
        max-width: 90;
        height: auto;
        padding: 1 2;
        border: thick $primary;
        background: $surface;
    }
    #status { color: $text-muted; margin-top: 1; }
    #search { display: none; dock: bottom; margin-bottom: 1; }
    #tiles {
        height: auto;
        grid-size: 3;
        grid-rows: 15;  /* TILE_IMAGE_ROWS + タイトル 1 行 + 枠 2 行 */
        grid-gutter: 0 1;
    }
    Tile {
        height: 100%;
        border: round $panel;
    }
    .tile-box { height: 12; align: center middle; }
    Tile.cursor { border: round $accent; }
    .tile-slot { width: auto; color: $text-muted; }
    .tile-pic { margin-bottom: 0; }
    .tile-title { height: 1; text-wrap: nowrap; text-overflow: ellipsis; color: $text-muted; }
    Tile.cursor .tile-title { color: $text; text-style: bold; }
    #gallery-status { color: $text-muted; margin: 1 2; }
    PictureScreen { align: center middle; }
    #picture { width: auto; height: auto; }
    #picture-title { text-wrap: nowrap; text-overflow: ellipsis; background: $surface; padding: 0 1; }
    #search.visible { display: block; }
    """

    def __init__(self, gallery_url: str = "", start: Callable[[], Screen] | None = None) -> None:
        super().__init__()
        self.gallery_url = gallery_url  # matome --gallery URL: そのページの画像一覧だけを開く
        self.start = start  # 最初に開く画面を作る（matome を import して自分の SearchScreen を開くとき）
        self.sites: list[feeds.Site] = []
        self.group_names: dict[int, str] = {}
        self.read = ReadState()
        self.settings = Settings()
        set_dither(self.settings.dither)
        self.bookmarks = Bookmarks()
        self.http = feeds.client()
        self.timing = TimingLog()
        self.articles = Articles(self)

    def group_sites(self, n: int | None = None) -> list[feeds.Site]:
        n = n or self.settings.group
        return [s for s in self.sites if s.group == n]

    def group_label(self, n: int) -> str:
        name = self.group_names.get(n)
        return f"{n} {name}" if name else str(n)

    async def on_event(self, event: events.Event) -> None:
        # 中クリック（button 2）と右クリック（button 3）は画面へ渡さない（一覧の行やタイルを開かないように）。
        # 中クリックは q と同じ「戻る・閉じる」。最初の画面（スタックの 2 枚目）の q は終了なので何もしない。
        # 右クリックは、その場所に合ったメニューを出す
        if isinstance(event, (events.MouseDown, events.MouseUp)) and event.button in (2, 3) and not event.is_forwarded:
            if isinstance(event, events.MouseUp):
                if isinstance(self.screen, ContextMenu):
                    self.screen.dismiss(None)
                elif event.button == 2:
                    action = right_click_action(self.screen)
                    if action and len(self.screen_stack) > 2:
                        await self.screen.run_action(action)
                else:
                    self.show_menu(event.x, event.y)
            return
        await super().on_event(event)

    def action_copy_url(self) -> None:
        items = url_info(self.screen)
        if items:
            copy_url(self, items[0][1])
        else:
            self.notify("ここには URL がありません", timeout=2)

    def action_show_url(self) -> None:
        show_url(self, url_info(self.screen))

    def show_menu(self, x: int, y: int) -> None:
        self.show_items(context_items(self, x, y), x, y)

    def show_items(self, items: list[tuple[str, object]], x: int, y: int) -> None:
        if not items:
            return

        def chosen(index: int | None) -> None:
            if index is not None:
                self.call_later(items[index][1])

        self.push_screen(ContextMenu([label for label, _ in items], x, y), chosen)

    def on_mount(self) -> None:
        if self.start:
            self.push_screen(self.start())
        elif self.gallery_url:
            self.push_screen(PageGalleryScreen(self.gallery_url))
        else:
            self.push_screen(SiteScreen())

    async def on_unmount(self) -> None:
        await self.http.aclose()


def main() -> None:
    parser = argparse.ArgumentParser(prog="matome", description="まとめサイトをターミナルで読む")
    parser.add_argument("--gallery", metavar="URL", default="", help="そのページの画像を全部、画像一覧で開く（q で終わる）")
    args = parser.parse_args()
    MatomeApp(gallery_url=args.gallery).run()


if __name__ == "__main__":
    main()
