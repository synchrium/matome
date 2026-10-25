"""まとめサイトの取得と解析。画面からは独立させてある。

サイトは設定ファイル（sites.toml）に RSS の URL を書くだけで追加できる。
本文やコメントの場所は PRESETS の型から自動判定し、合わない場合だけ
設定ファイルで CSS セレクタを上書きする。
"""

from __future__ import annotations

import calendar
import functools
import hashlib
import html
import json
import os
import re
import sys
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from urllib.parse import parse_qs, urljoin, urlparse

import feedparser
import httpx
from selectolax.lexbor import LexborHTMLParser, LexborNode, SelectolaxError

if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib

# サイトの運営者が問い合わせ先を分かるよう、名前と URL を名乗る（クローラーの慣習の書き方）
UA = "Mozilla/5.0 (compatible; matome/0.2; +https://github.com/synchrium/matome)"


def _xdg(env: str, default: str) -> Path:
    # Linux / macOS / Windows のどこでも ~/.config などに置く（ターミナル利用者に分かりやすいので）
    return Path(os.environ.get(env) or Path.home() / default) / "matome"


CONFIG_DIR = _xdg("XDG_CONFIG_HOME", ".config")
CACHE_DIR = _xdg("XDG_CACHE_HOME", ".cache")
STATE_DIR = _xdg("XDG_STATE_HOME", ".local/state")
SITES_FILE = CONFIG_DIR / "sites.toml"
DROP_FILE = CONFIG_DIR / "drop.txt"

# サイトの作りの型。上から順に試して、本文が見つかったものを使う。
PRESETS: dict[str, dict[str, list[str]]] = {
    # 今の livedoor ブログ標準テンプレート（ハム速、VIPPERな俺など）
    "livedoor": {
        "body": [".article-body-inner"],
        "comment_item": ["#comments-list li.comment-set"],
        "comment_head": [".comment-author", ".comment-date"],
        "comment_body": [".comment-body"],
    },
    # 古い livedoor ブログテンプレート（痛いニュースなど）。コメントは見出しと本文が交互に並ぶ
    "livedoor-classic": {
        "body": [".main.entry-content", ".mainmore"],
        "comment_item": [],
        "comment_head": ["#commentbody .commentttl"],
        "comment_body": ["#commentbody .commenttext"],
    },
    # .entry / .entrybody 型の livedoor ブログテンプレート（ラビット速報など）
    "livedoor-entry": {
        "body": [".entrybody"],
        "comment_item": ["li.comment-set"],
        "comment_head": [".comment-author", ".comment-date"],
        "comment_body": [".comment-body"],
    },
    # はちま起稿。.article-body-more を持つので livedoor-ently より先に試す
    "hachima": {
        "body": [".article-main .article-body-more"],
        "comment_item": [".comment-lists .comment-list"],
        "comment_head": [".comment-list-name", ".comment-list-date"],
        "comment_body": [".comment-list-body"],
    },
    # オレ的ゲーム速報＠刃
    "jin115": {
        "body": [".article .article_body", ".article .article_bodymore"],
        "comment_item": ["#comment_list li"],
        "comment_head": ["dt span"],
        "comment_body": ["dd"],
    },
    # やらおん！（WordPress）。コメントの名前の後ろの投稿日は地の文なので取れない
    "yaraon": {
        "body": ["div.entry .reduction", "div.entry #extended"],
        "drop": [".widgetarea"],
        "comment_item": [".comment_area ol > li"],
        "comment_head": ["span"],
        "comment_body": ["div"],
    },
    # .ently_text / .article-body-more 型の livedoor ブログテンプレート（ニュー速クオリティなど）
    "livedoor-ently": {
        "body": [".ently_text", ".article-body-more"],
        "comment_item": ["#comment_text"],
        "comment_head": ["#comment_text > span"],
        "comment_body": ["p"],
    },
    # アルファルファモザイク。本文の末尾に関連記事が並ぶので捨てる。
    # 本文は冒頭（.article_body）と続き（.article_bodymore、ブラウザでは「続きを読む」の先）に分かれている。
    # 【PickupNNN】の記事は過去の人気記事の紹介で、本編は最初に並ぶアルファルファ自身の記事なのでそちらを読む
    "alfalfa": {
        "follow": ['.article_body .daily_popular_title a[href*="alfalfalfa.com/articles/"]'],
        "body": [".main_article_contents_inner .article_body", ".main_article_contents_inner .article_bodymore"],
        "drop": ["#related-title", ".manual-related"],
        "comment_item": ["#comments-list li.comment-set"],
        "comment_head": [".comment-author", ".comment-date"],
        "comment_body": [".comment-body"],
    },
    # 不思議.net。本文は冒頭（.kiji_box）と続き（.more_body）に分かれている。コメントは JavaScript で読むので取れない
    "fusigi": {
        "body": [".kiji_box", ".more_body"],
        "drop": [".out_link"],
        "comment_item": [],
        "comment_head": [],
        "comment_body": [],
    },
    # WordPress などその他。コメントは取らない
    "generic": {
        "body": [".entry-content", "article", "main"],
        "comment_item": [],
        "comment_head": [],
        "comment_body": [],
    },
}
SELECTOR_KEYS = ["follow", "body", "drop", "comment_item", "comment_head", "comment_body"]

# 本文から捨てる要素（端末に出せない埋め込みスクリプトなど）。
# 広告は消さない。消したい人は drop.txt に自分で書く（user_drops）
DROP_SELECTORS = [
    "script", "style", "noscript", "ins", "link", "form",
    # アイコンは端末に出せず、<title> の文字だけが本文に残る（BuzzFeed の共有ボタンの「Facebook」など）
    "svg",
    # YouTube の埋め込みだけは動画の行にするので残す
    'iframe:not([src*="/embed/"]):not([data-src*="/embed/"])',
]


@functools.cache
def user_drops() -> list[str]:
    """drop.txt に書いた、全サイトの本文から消すもの。1 行に 1 つの CSS セレクタ。

    「# 」で始まる行はコメント（「#ad」のような ID のセレクタと区別するため、# の後ろに空白が要る）。
    書き間違えたセレクタは飛ばす。最初に記事を開くときに 1 回だけ読む。
    """
    try:
        lines = DROP_FILE.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    probe = LexborHTMLParser("<p></p>")
    drops = []
    for line in lines:
        line = line.strip()
        if not line or line == "#" or line.startswith("# "):
            continue
        try:
            probe.css(line)
        except SelectolaxError:
            continue
        drops.append(line)
    return drops


@dataclass
class Site:
    name: str
    feed: str
    preset: str | None = None
    # 設定ファイルで個別に指定されたセレクタ（PRESETS を上書きする）
    overrides: dict[str, list[str]] = field(default_factory=dict)
    group: int = 1  # サイト一覧で 1〜9 のキーで切り替えるグループ
    # 以下はフィードを読んだときに分かる情報（保存しない）
    home: str = ""
    livedoor: bool = False

    @property
    def aggregator(self) -> bool:
        """アンテナサイトのように、記事ごとに配信元のサイトが違うフィード。本文の型を覚えない。"""
        return urlparse(self.feed).hostname in ANTENNA_HOSTS + LINK_HUB_HOSTS

    def selectors(self, preset: str) -> dict[str, list[str]]:
        sel = {"follow": [], "drop": [], **PRESETS[preset]}
        sel.update(self.overrides)
        return sel


@dataclass
class Entry:
    site: Site
    title: str
    url: str
    timestamp: float  # 並べ替え用（UNIX 時刻）
    category: str

    @property
    def date(self) -> str:
        if not self.timestamp:
            return "--/-- --:--"
        return time.strftime("%m/%d %H:%M", time.localtime(self.timestamp))


@dataclass
class Text:
    text: str
    quote: bool = False
    # 文の中のリンク（<a href>）。（始まり, 終わり, URL）で、text の中の位置。URL が文字として見えていないものも含む
    links: list[tuple[int, int, str]] = field(default_factory=list)


@dataclass
class Picture:
    src: str
    full: str = ""  # 画像がリンクになっているときのリンク先（livedoor ブログなどは src が縮小版で、こちらが元の画像）


@dataclass
class Video:
    src: str  # 動画ファイルか YouTube などのページの URL。プレイヤーに渡す


Block = Text | Picture | Video


@dataclass
class Comment:
    header: str
    body: str


@dataclass
class Article:
    url: str
    blocks: list[Block] = field(default_factory=list)
    comments: list[Comment] = field(default_factory=list)


# ---------------------------------------------------------------- 設定ファイル

CONFIG_HEADER = """\
# matome のサイト一覧
#
# アプリのサイト一覧で a を押すと、ここに追記されます。
# 手で書く場合は name と feed（RSS / Atom の URL）だけで動きます。
# 本文やコメントがうまく取れないときは、CSS セレクタで場所を指定できます:
#
# [[site]]
# name = "例"
# feed = "https://example.com/index.rdf"
# preset = "livedoor"          # livedoor / livedoor-classic / livedoor-entry / livedoor-ently / hachima / jin115 / yaraon / alfalfa / fusigi / generic（省略すると自動判定）
# follow = ["a.more"]           # 紹介だけの記事なら、このリンクの先（本編）を読む
# body = [".entry-content"]     # 本文（複数書くと順につなげる）
# drop = [".ad"]                # 本文から消すもの
# comment_item = [".comment"]   # コメント 1 件のまとまり（無ければ head と body を順に組にする）
# comment_head = [".comment-author"]
# comment_body = [".comment-body"]
# group = 2                     # サイト一覧のグループ 1〜9（省略すると 1）
#
# グループには名前を付けられます（サイト一覧の上に出ます）:
#
# [groups]
# 1 = "まとめ"
# 2 = "ニュース"
"""

# 最初は空で始める（特定のサイトを推さない）。サイト一覧に「a で追加」の案内を出す
DEFAULT_SITES: list[Site] = []
GROUPS = range(1, 10)


def to_group(v) -> int:
    try:
        n = int(v)
    except (TypeError, ValueError):
        return 1
    return n if n in GROUPS else 1


def load_sites() -> tuple[list[Site], dict[int, str]]:
    """サイトの一覧と、グループ番号 → グループ名を返す。"""
    if not SITES_FILE.exists():
        save_sites(DEFAULT_SITES)
    data = tomllib.loads(SITES_FILE.read_text(encoding="utf-8"))
    names = {
        to_group(k): str(v)
        for k, v in data.get("groups", {}).items()
        if str(k).isdigit() and int(k) in GROUPS and v
    }
    sites = []
    for d in data.get("site", []):
        if not d.get("name") or not d.get("feed"):
            continue
        preset = d.get("preset")
        if preset not in PRESETS:
            preset = None
        overrides = {
            k: [d[k]] if isinstance(d[k], str) else list(d[k])
            for k in SELECTOR_KEYS
            if k in d
        }
        sites.append(Site(d["name"], d["feed"], preset, overrides, to_group(d.get("group"))))
    return sites, names


def save_sites(sites: list[Site], group_names: dict[int, str] | None = None) -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    parts = [CONFIG_HEADER]
    if group_names:
        q = lambda v: json.dumps(v, ensure_ascii=False)
        parts.append("\n".join(["[groups]", *(f"{k} = {q(v)}" for k, v in sorted(group_names.items()))]) + "\n")
    for s in sites:
        parts.append(_site_toml(s))
    SITES_FILE.write_text("\n".join(parts), encoding="utf-8")


def append_site(site: Site) -> None:
    """コメントを残すため、追加は末尾への追記で行う。"""
    if not SITES_FILE.exists():
        save_sites([site])
        return
    with SITES_FILE.open("a", encoding="utf-8") as f:
        f.write("\n" + _site_toml(site))


def _site_toml(s: Site) -> str:
    q = lambda v: json.dumps(v, ensure_ascii=False)  # JSON の文字列は TOML でも有効
    lines = ["[[site]]", f"name = {q(s.name)}", f"feed = {q(s.feed)}"]
    if s.preset:
        lines.append(f"preset = {q(s.preset)}")
    for k, v in s.overrides.items():
        lines.append(f"{k} = [{', '.join(q(x) for x in v)}]")
    if s.group != 1:
        lines.append(f"group = {s.group}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- OPML（ほかの RSS リーダーとのやり取り）

def export_opml(sites: list[Site], group_names: dict[int, str], path: Path) -> None:
    """グループごとのフォルダにして書き出す。matome 用の属性（group・preset・selectors）は
    ほかのリーダーでは無視されるだけなので、matome どうしなら設定ごと引き継げる。"""
    root = ET.Element("opml", version="2.0")
    ET.SubElement(ET.SubElement(root, "head"), "title").text = "matome のサイト一覧"
    body = ET.SubElement(root, "body")
    for n in sorted({s.group for s in sites}):
        folder = ET.SubElement(body, "outline", text=group_names.get(n) or f"グループ {n}", group=str(n))
        for s in (s for s in sites if s.group == n):
            attrs = {"type": "rss", "text": s.name, "title": s.name, "xmlUrl": s.feed}
            if s.preset:
                attrs["preset"] = s.preset
            if s.overrides:
                attrs["selectors"] = json.dumps(s.overrides, ensure_ascii=False)
            ET.SubElement(folder, "outline", attrs)
    ET.indent(root)
    path.parent.mkdir(parents=True, exist_ok=True)
    ET.ElementTree(root).write(path, encoding="utf-8", xml_declaration=True)


def import_opml(path: Path, default_group: int) -> tuple[list[Site], dict[int, str]]:
    """OPML のサイトと、matome が書き出したグループ名を返す。
    グループの分からないサイト（ほかのリーダーの OPML）は default_group に入れる。"""
    root = ET.parse(path).getroot()
    sites: list[Site] = []
    names: dict[int, str] = {}

    def walk(node: ET.Element, group: int) -> None:
        for o in node.findall("outline"):
            url = o.get("xmlUrl")
            if url:
                preset = o.get("preset")
                try:
                    overrides = {
                        k: [v] if isinstance(v, str) else list(v)
                        for k, v in json.loads(o.get("selectors") or "{}").items()
                        if k in SELECTOR_KEYS
                    }
                except (ValueError, AttributeError, TypeError):
                    overrides = {}
                name = o.get("title") or o.get("text") or url
                sites.append(Site(name, url, preset if preset in PRESETS else None, overrides, group))
            else:
                sub = group
                if (o.get("group") or "").isdigit() and int(o.get("group")) in GROUPS:
                    sub = int(o.get("group"))
                    if o.get("text") and o.get("text") != f"グループ {sub}":
                        names[sub] = o.get("text")
                walk(o, sub)

    walk(root.find("body") if root.find("body") is not None else root, default_group)
    return sites, names


# ---------------------------------------------------------------- 取得

def client() -> httpx.AsyncClient:
    return httpx.AsyncClient(
        headers={"User-Agent": UA}, follow_redirects=True, timeout=20.0
    )


class BotBlocked(httpx.HTTPError):
    """記事の代わりにボット対策の待合ページが返ってきた。

    httpx.HTTPError の仲間にしておくと、取得失敗を受けているところがそのまま拾える。
    """

    def __init__(self, url: str) -> None:
        host = urlparse(url).netloc
        super().__init__(f"{host} のボット対策で弾かれました（VPN 中なら切ると読めることがあります）")


# 待合ページの <title>。Hostinger などの「One moment, please...」と Cloudflare の「Just a moment...」
BOT_WALL = re.compile(rb"<title>\s*(One moment, please|Just a moment)\.\.\.\s*</title>", re.I)


async def get(c: httpx.AsyncClient, url: str, **kw) -> httpx.Response:
    """GET。圧縮を頼むと 406 を返すサイト（BuzzFeed など）は、圧縮なしで取り直す。

    ボット対策の待合ページが返ってきたら BotBlocked にする（RSS が「0 件」に見えないように）。
    """
    r = await c.get(url, **kw)
    if r.status_code == 406:
        headers = {**kw.pop("headers", {}), "Accept-Encoding": "identity"}
        r = await c.get(url, headers=headers, **kw)
    if "html" in r.headers.get("content-type", "") and BOT_WALL.search(r.content[:4096]):
        raise BotBlocked(str(r.url))
    return r


def decode(r: httpx.Response) -> str:
    """ヘッダー → meta タグ → UTF-8 の順で文字コードを決める（EUC-JP のサイトがある）。"""
    enc = r.charset_encoding
    if not enc:
        m = re.search(rb"""charset=["']?([\w-]+)""", r.content[:4096], re.I)
        enc = m.group(1).decode() if m else "utf-8"
    try:
        return r.content.decode(enc, errors="replace")
    except LookupError:
        return r.content.decode("utf-8", errors="replace")


async def fetch_entries(c: httpx.AsyncClient, site: Site) -> list[Entry]:
    r = await get(c, site.feed)
    r.raise_for_status()
    feed = feedparser.parse(r.content)
    site.home = feed.feed.get("link") or urljoin(site.feed, "./")
    site.livedoor = b"livedoor" in r.content[:3000]
    return _feed_entries(feed, site)


def _feed_entries(feed, site: Site) -> list[Entry]:
    entries = []
    for e in feed.entries:
        t = e.get("published_parsed") or e.get("updated_parsed")
        tags = e.get("tags") or []
        entries.append(
            Entry(
                site=site,
                title=html.unescape(e.get("title", "")).strip(),
                url=e.get("link", ""),
                timestamp=calendar.timegm(t) if t else 0.0,
                category=tags[0].get("term", "") if tags else "",
            )
        )
    return entries


async def fetch_page(c: httpx.AsyncClient, site: Site, page: int) -> list[Entry]:
    """過去記事の一覧（page は 1 から）。RSS には最新の分しか無いのでサイトの一覧ページを読む。

    livedoor ブログは ?p=N、WordPress などは /page/N/ に一覧がある。
    記事は hAtom（.hentry / .entry-title / abbr.updated）で書かれていることが多い。
    一覧ページを読めないサイトでは空のリストを返す（＝これ以上の過去記事なし）。
    """
    if not site.home:
        await fetch_entries(c, site)
    home = site.home.rstrip("/") + "/"
    if site.livedoor:
        url = f"{home}?p={page}"
    else:
        url = home if page == 1 else urljoin(home, f"page/{page}/")
    r = await get(c, url)
    if r.is_success:
        entries = parse_list_page(decode(r), str(r.url), site)
        if entries or site.livedoor:
            return entries
    elif site.livedoor:
        return []
    # 一覧ページが読めないサイトは、WordPress 形式のフィードのページ送りを試す
    sep = "&" if "?" in site.feed else "?"
    r = await get(c, f"{site.feed}{sep}paged={page}")
    if not r.is_success:
        return []
    return _feed_entries(feedparser.parse(r.content), site)


def parse_list_page(html_text: str, base: str, site: Site) -> list[Entry]:
    tree = LexborHTMLParser(html_text)
    entries: list[Entry] = []
    last_ts = 0.0
    # hAtom（.hentry）が基本。無ければ .entry 型テンプレートのまとまりを使う
    for h in tree.css(".hentry") or tree.css(".entry"):
        a = h.css_first(".entry-title a, h2 a, h3 a")
        if not a or not a.attributes.get("href"):
            continue
        ts = last_ts  # 日付が無い記事（同じ日の 2 件目以降など）は直前の記事の時刻で代用
        up = h.css_first("abbr.updated, time[datetime], .published")
        stamp = up and (up.attributes.get("title") or up.attributes.get("datetime"))
        if stamp:
            try:
                ts = datetime.fromisoformat(stamp.replace("Z", "+00:00")).timestamp()
            except ValueError:
                pass
        else:
            # 「2026年10月14日　17:30」のように文章で書かれた日時（サイトの現地時刻とみなす）
            m = re.search(r"(\d{4})年(\d{1,2})月(\d{1,2})日\D{0,6}(\d{1,2}):(\d{2})", h.text()[:500])
            if m:
                ts = time.mktime(tuple(map(int, m.groups())) + (0, 0, 0, -1))
        last_ts = ts
        cat = h.css_first('a[href*="/archives/cat_"], a[rel~="tag"], a[rel~="category"]')
        entries.append(
            Entry(
                site=site,
                title=_squash(a.text()),
                url=urljoin(base, a.attributes["href"]),
                timestamp=ts,
                category=_squash(cat.text()) if cat else "",
            )
        )
    return entries


async def discover(c: httpx.AsyncClient, url: str) -> tuple[str, str]:
    """RSS の URL かサイトのトップ URL を受け取り、(フィード URL, サイト名) を返す。"""
    r = await get(c, url)
    r.raise_for_status()
    feed = feedparser.parse(r.content)
    if feed.entries:
        return str(r.url), feed.feed.get("title", "") or r.url.host
    # HTML ならフィードへのリンクを探す
    tree = LexborHTMLParser(decode(r))
    for link in tree.css('link[rel="alternate"]'):
        typ = link.attributes.get("type") or ""
        href = link.attributes.get("href")
        if href and ("rss" in typ or "atom" in typ):
            return await discover(c, str(r.url.join(href)))
    raise ValueError("RSS / Atom フィードが見つかりませんでした")


async def detect_preset(c: httpx.AsyncClient, site: Site) -> str | None:
    """最初の記事を開いて、本文が取れる型を探す。"""
    if site.aggregator:
        return None  # 記事ごとに判定する
    entries = await fetch_entries(c, site)
    if not entries:
        return None
    r = await get(c, entries[0].url)
    r.raise_for_status()
    return _match_preset(LexborHTMLParser(decode(r)), site)


def _match_preset(tree: LexborHTMLParser, site: Site) -> str | None:
    for name in PRESETS:
        if any(tree.css_first(s) for s in site.selectors(name)["body"]):
            return name
    return None


async def fetch_article(c: httpx.AsyncClient, entry: Entry) -> Article:
    url = await resolve_link(c, entry.url)
    r = await get(c, url)
    r.raise_for_status()
    html_text, url = decode(r), str(r.url)
    # 紹介だけの記事なら、本編へのリンク（型の follow）を 1 回だけたどる。読めなければ紹介の記事のまま
    target = _follow_link(html_text, url, entry.site)
    if target:
        try:
            r = await get(c, target)
            r.raise_for_status()
            html_text, url = decode(r), str(r.url)
        except httpx.HTTPError:
            pass
    return parse_article(html_text, url, entry.site)


def _follow_link(html_text: str, url: str, site: Site) -> str | None:
    """型の follow に当たるリンクがあれば、その URL（本編）。"""
    tree = LexborHTMLParser(html_text)
    preset = site.preset or _match_preset(tree, site) or "generic"
    for s in site.selectors(preset)["follow"]:
        a = tree.css_first(s)
        href = urljoin(url, (a.attributes.get("href") or "").strip()) if a else ""
        if href.startswith("http") and href != url:
            return href
    return None


# アンテナサイト（まとめブログの新着を集めたサイト）。フィードのリンク先はアンテナ内のページで、
# 配信元の URL が ku= に入っているか、他の記事へのリンクが大量に並ぶ中に eid 属性つきで置かれている
ANTENNA_HOSTS = ("2ch-c.net", "newmatosoku.com")
# フィードのリンクがそのまま別々のサイトの記事を指すもの（はてなブックマークの人気エントリーなど）。
# リンクを直す必要はないが、アンテナと同じく本文の型を記事ごとに判定する
LINK_HUB_HOSTS = ("b.hatena.ne.jp",)


async def resolve_link(c: httpx.AsyncClient, url: str) -> str:
    """アンテナの記事リンクを配信元の URL に直す。直せないときは元の URL のまま返す。"""
    if urlparse(url).hostname in ANTENNA_HOSTS:
        return await _resolve_antenna(c, url)
    return url


async def _resolve_antenna(c: httpx.AsyncClient, url: str) -> str:
    query = parse_qs(urlparse(url).query)
    ku = query.get("ku", [""])[0]
    if ku.startswith("http"):
        return ku
    eid = query.get("eid", [""])[0]
    if not eid:
        return url
    r = await get(c, url)
    a = LexborHTMLParser(decode(r)).css_first(f'a[eid="{eid}"][href]')
    href = a.attributes.get("href") if a else None
    return urljoin(str(r.url), href) if href and href.startswith("http") else url


def parse_article(html_text: str, url: str, site: Site) -> Article:
    tree = LexborHTMLParser(html_text)
    preset = site.preset or _match_preset(tree, site) or "generic"
    if not site.aggregator:
        site.preset = site.preset or preset  # 一度判定したら覚えておく
    sel = site.selectors(preset)
    art = Article(url=url)

    drops = DROP_SELECTORS + user_drops() + sel["drop"]
    nodes: list[LexborNode] = []
    for s in sel["body"]:
        found = tree.css(s)
        # 広告の記事などが同じクラスで先に置かれていることがあるので、中身の多いほうを本文にする
        node = max(found, key=lambda n: _content_score(n, drops)) if len(found) > 1 else (found or [None])[0]
        # 先に取った要素の内側にあるものは二重になるので飛ばす
        if node and not any(node.html in n.html for n in nodes):
            nodes.append(node)
        if node and preset == "generic" and "body" not in site.overrides:
            break  # generic の既定の候補は最初に当たったものだけ（設定で書いた body は順につなげる）
    if not nodes and "body" not in site.overrides:
        guess = _guess_body(tree)
        if guess:
            nodes.append(guess)
    for node in nodes:
        _drop(node, drops)
        _absolutize(node, url)
        art.blocks.extend(_blocks(node))
    art.blocks = _inline_pictures(art.blocks)

    art.comments = _comments(tree, sel)
    return art


# 本文に文字で書かれた URL（_inline_pictures で使う）。末尾の句読点や閉じかっこは含めない
_TEXT_URL = re.compile(r"https?://[^\s<>\"'（）「」『』【】、。]+")
_PICTURE_URL = re.compile(r"\.(jpe?g|png|gif|webp)([?#]|$)", re.I)


def _inline_pictures(blocks: list[Block]) -> list[Block]:
    """本文に文字で書かれた画像の URL（妹はVIPPER のように <img> ではなく URL のリンクだけのもの）を、
    その URL の行のすぐ下に画像として出す。文はその行の終わりで分ける。
    すでに画像の行がある画像（元の画像へのリンクを含む）は二重になるので足さない。"""
    shown = {u for b in blocks if isinstance(b, Picture) for u in (b.src, b.full) if u}
    out: list[Block] = []
    for b in blocks:
        if not isinstance(b, Text):
            out.append(b)
            continue
        found = [(end, url) for _, end, url in b.links]
        found += [(m.end(), m.group(0).rstrip(".,;:!?)]}'\"")) for m in _TEXT_URL.finditer(b.text)]
        cuts: dict[int, list[str]] = {}  # 文を分ける位置（URL の行の終わり）→ その下に出す画像
        for end, url in sorted(found):
            if url in shown or "amazon" in url or not _PICTURE_URL.search(url):
                continue
            shown.add(url)
            line_end = b.text.find("\n", end)
            cuts.setdefault(len(b.text) if line_end < 0 else line_end, []).append(url)
        if not cuts:
            out.append(b)
            continue
        start = 0
        for cut in sorted({*cuts, len(b.text)}):
            while start < cut and b.text[start] == "\n":
                start += 1
            if start < cut:
                links = [(s - start, e - start, u) for s, e, u in b.links if start <= s and e <= cut]
                out.append(Text(b.text[start:cut], quote=b.quote, links=links))
            out.extend(Picture(url) for url in cuts.get(cut, []))
            start = cut
    return out


def _absolutize(node: LexborNode, base: str) -> None:
    """画像とリンクの相対パス（/wp-content/... など）を完全な URL にする。_blocks は http で始まるものしか拾わない。"""
    for n in node.css("img, a, source"):
        for attr in ("src", "data-src", "href"):
            v = (n.attributes.get(attr) or "").strip()
            if v and not v.startswith(("http:", "https:", "//", "data:", "#", "mailto:", "javascript:")):
                n.attrs[attr] = urljoin(base, v)


def _drop(node: LexborNode, drops: list[str]) -> None:
    for s in drops:
        for n in node.css(s):
            n.decompose()


def _content_score(node: LexborNode, drops: list[str]) -> int:
    """本文らしさ。広告などを除いた文字数に、画像 1 枚を 200 文字分として足す。"""
    _drop(node, drops)
    blocks = _blocks(node)
    return sum(len(b.text) if isinstance(b, Text) else 200 for b in blocks)


BLOCK_TAGS = {
    "div", "p", "section", "article", "aside", "nav", "header", "footer", "main",
    "ul", "ol", "li", "table", "tr", "td", "th", "blockquote", "form", "h1", "h2", "h3", "h4",
}


def _own_text_len(node: LexborNode) -> int:
    """要素そのものの文字数（中の div や p などのブロックの分は数えない）。"""
    n = 0
    for child in node.iter(include_text=True):
        if child.tag == "-text":
            n += len((child.text_content or "").strip())
        elif child.tag not in BLOCK_TAGS and child.tag not in ("script", "style"):
            n += _own_text_len(child)
    return n


def _guess_body(tree: LexborHTMLParser) -> LexborNode | None:
    """どの型にも当てはまらないページ用。

    段落（<p> や、<br> 区切りの文章を直接持つ <div>）の文字数を親に全部、祖父母に半分足していき、
    一番点数の高い要素を本文とみなす（Readability と同じ考え方）。
    """
    score: dict[int, list] = {}
    for el in tree.css("p, div"):
        n = _own_text_len(el)
        if n < 20:
            continue
        parent = el.parent
        for node, weight in ((parent, 1.0), (parent.parent if parent else None, 0.5)):
            if node is None or node.tag in ("body", "html"):
                continue
            score.setdefault(node.mem_id, [0.0, node])[0] += n * weight
    if not score:
        return None
    total, node = max(score.values(), key=lambda v: v[0])
    return node if total >= 150 else None


def _comments(tree: LexborHTMLParser, sel: dict[str, list[str]]) -> list[Comment]:
    out = []
    items = [n for s in sel["comment_item"] for n in tree.css(s)]
    if items:
        for item in items:
            head = _join_unique(
                _squash(n.text(separator=" "))
                for s in sel["comment_head"]
                for n in item.css(s)
            )
            body = next((item.css_first(s) for s in sel["comment_body"] if item.css_first(s)), None)
            out.append(Comment(head, _tidy(_node_text(body)) if body else ""))
    else:
        heads = [n for s in sel["comment_head"] for n in tree.css(s)]
        bodies = [n for s in sel["comment_body"] for n in tree.css(s)]
        for h, b in zip(heads, bodies):
            out.append(Comment(_squash(h.text(separator=" ")), _tidy(_node_text(b))))
    return out


def _join_unique(texts) -> str:
    # 日付が投稿者欄の中にも外にもあるテンプレートがあるので、重複は捨てる
    joined = ""
    for t in texts:
        if t and t not in joined:
            joined = f"{joined} {t}".strip()
    return joined


def _blocks(root: LexborNode) -> list[Block]:
    """DOM を「テキスト」「画像」「動画」の並びに平らにする。"""
    out: list[Block] = []
    buf: list[str] = []
    videos: set[str] = set()  # <video> とリンクで同じ動画が二度出ることがあるので
    hrefs: list[str] = []  # 文の中のリンク先。buf にはリンクの始まりと終わりの印（LINK_*）だけ入れておく

    def video(src: str) -> None:
        # 再生位置の指定（#t=…）だけ違う同じ動画をまとめる。href の前後に改行が入っているサイトがある
        src = src.strip().split("#")[0]
        if src.startswith("//"):
            src = "https:" + src
        if src.startswith("http") and src not in videos:
            videos.add(src)
            flush()
            out.append(Video(src))

    def flush(quote: bool = False) -> None:
        text, links = _take_links("".join(buf), hrefs)
        buf.clear()
        if text:
            out.append(Text(text, quote, links))

    def walk(node: LexborNode) -> None:
        for child in node.iter(include_text=True):
            tag = child.tag
            if tag == "-text":
                buf.append(child.text_content or "")
            elif tag == "br":
                buf.append("\n")
            elif tag == "img":
                src = (child.attributes.get("data-src") or child.attributes.get("src") or "").strip()
                if src.startswith("//"):
                    src = "https:" + src
                if _is_picture(src):
                    flush()
                    out.append(Picture(src, _linked_picture(child)))
            elif tag == "video":
                source = child.css_first("source[src]")
                video(child.attributes.get("src") or (source.attributes.get("src") if source else "") or "")
            elif tag == "iframe":
                m = YOUTUBE_EMBED_RE.search(child.attributes.get("data-src") or child.attributes.get("src") or "")
                if m:
                    video(f"https://www.youtube.com/watch?v={m.group(1)}")
            elif tag == "lite-youtube" and child.attributes.get("videoid"):
                # クリックするまで iframe を置かない軽量版の埋め込み（リアルサウンドなど）
                video(f"https://www.youtube.com/watch?v={child.attributes['videoid']}")
            elif tag == "a" and _is_video((child.attributes.get("href") or "").strip()):
                walk(child)
                video(child.attributes["href"])
            elif tag == "a" and (child.attributes.get("href") or "").strip().startswith("http"):
                # 文の中のリンク。リンクの文字の前後に印を入れておき、flush で位置にする（_tidy で文字が詰まっても合うように）
                buf.append(f"{LINK_START}{len(hrefs)}{LINK_MID}")
                hrefs.append(child.attributes["href"].strip())
                walk(child)
                buf.append(LINK_END)
            elif tag == "blockquote":
                flush()
                # imgur の埋め込みは JavaScript で画像に置き換わる。画像はよそのページからの直リンクを断るので、
                # imgur のページへのリンクにしてブラウザで見る（BROWSER_ONLY_HOSTS）。アルバム（a/…）は文字のまま
                pid = (child.attributes.get("data-id") or "").strip()
                if "imgur-embed-pub" in (child.attributes.get("class") or "") and re.fullmatch(r"\w+", pid):
                    flush()
                    hrefs.append(f"https://imgur.com/{pid}")
                    buf.append(f"{LINK_START}{len(hrefs) - 1}{LINK_MID}imgur の画像（ブラウザで開く）{LINK_END}")
                    flush()
                    continue
                # ツイート埋め込みなどは引用として別ブロックにする
                walk(child)
                flush(quote=True)
            elif tag in ("div", "p", "li", "h2", "h3", "h4", "hr"):
                buf.append("\n")
                walk(child)
                buf.append("\n")
            else:
                walk(child)

    walk(root)
    flush()
    return out


VIDEO_RE = re.compile(
    r"\.(mp4|m4v|webm|mov|m3u8)([?#]|$)"
    r"|^(https?:)?//((www|m)\.)?(youtube\.com/(watch|shorts/)|youtu\.be/)",
    re.I,
)


YOUTUBE_EMBED_RE = re.compile(r"//(?:www\.)?youtube(?:-nocookie)?\.com/embed/([\w-]{11})")
YOUTUBE_RE = re.compile(r"^https?://((www|m)\.)?(youtube\.com/|youtu\.be/)", re.I)
# 中身を JavaScript で組み立てるので w3m では何も出ず、いつものブラウザで開くサイト
BROWSER_ONLY_HOSTS = ("imgur.com", "www.imgur.com")


def _is_video(href: str) -> bool:
    return bool(VIDEO_RE.search(href))


def is_youtube(url: str) -> bool:
    return bool(YOUTUBE_RE.search(url))


def youtube_id(url: str) -> str:
    """YouTube の動画の ID（11 文字）。YouTube でなければ空。"""
    if not is_youtube(url):
        return ""
    m = re.search(r"(?:[?&]v=|youtu\.be/|shorts/|embed/)([\w-]{11})", url)
    return m.group(1) if m else ""


def _linked_picture(img: LexborNode) -> str:
    """<a href="元の画像"><img src="縮小版"></a> のリンク先。画像へのリンクでなければ空。"""
    node = img.parent
    for _ in range(3):  # <a><span><img> のように間に要素が挟まることがある
        if node is None:
            break
        if node.tag == "a":
            href = (node.attributes.get("href") or "").strip()
            if href.startswith("//"):
                href = "https:" + href
            return href if _is_picture(href) and re.search(r"\.(jpe?g|png|gif|webp)(\?|$)", href, re.I) else ""
        node = node.parent
    return ""


def _is_picture(src: str) -> bool:
    # Amazon の宣伝やトラッキング用の画像は出さない
    if not src.startswith("http") or "amazon" in src:
        return False
    if "blogimg.jp" in src:
        return True
    return bool(re.search(r"\.(jpe?g|png|gif|webp)(\?|$)", src, re.I))


def _node_text(node: LexborNode) -> str:
    parts: list[str] = []
    for child in node.iter(include_text=True):
        if child.tag == "-text":
            parts.append(child.text_content or "")
        elif child.tag == "br":
            parts.append("\n")
        else:
            parts.append(_node_text(child))
    return "".join(parts)


# リンクの始まり・終わりの印（Unicode の私用領域の文字。本文には出てこない）
LINK_START, LINK_MID, LINK_END = "\ue000", "\ue001", "\ue002"
LINK_MARK_RE = re.compile(f"{LINK_START}(\\d+){LINK_MID}|{LINK_END}")


def _take_links(raw: str, hrefs: list[str]) -> tuple[str, list[tuple[int, int, str]]]:
    """印の入った文から、整えた文（_tidy と同じ）とリンクの位置を作る。

    印を取り除いてから空白を整え、そのとき残した文字を数えて、リンクの位置を整えた後の位置に写す。
    リンクの文字が空（画像だけのリンクなど）なら位置にしない。途中で画像などで文が分かれて、
    始まりか終わりの片方しか無い印は捨てる。
    """
    chars: list[str] = []
    spans: list[tuple[int, int, str]] = []
    opened: list[tuple[int, int]] = []  # （hrefs の番号, 始まりの位置）
    last = 0
    for m in LINK_MARK_RE.finditer(raw):
        chars.extend(raw[last:m.start()])
        last = m.end()
        if m.group(1) is not None:
            opened.append((int(m.group(1)), len(chars)))
        elif opened:
            n, begin = opened.pop()
            spans.append((begin, len(chars), hrefs[n]))
    chars.extend(raw[last:])
    text = "".join(chars).replace("\xa0", " ")

    # _tidy と同じ整え方を、残す文字に印を付ける形でやる（行の前後の空白、3 つ以上続く改行、全体の前後）
    keep = [True] * len(text)
    pos = 0
    for line in text.split("\n"):
        body = line.strip()
        lead = len(line) - len(line.lstrip())
        for i in range(pos, pos + len(line)):
            if not (pos + lead <= i < pos + lead + len(body)):
                keep[i] = False
        pos += len(line) + 1
    run = 0
    for i, ch in enumerate(text):
        if not keep[i]:
            continue
        if ch == "\n":
            run += 1
            if run > 2:
                keep[i] = False
        else:
            run = 0
    kept = [i for i in range(len(text)) if keep[i]]
    while kept and text[kept[0]].isspace():
        keep[kept.pop(0)] = False
    while kept and text[kept[-1]].isspace():
        keep[kept.pop()] = False

    where = [0] * (len(text) + 1)  # 元の位置 → 整えた後の位置
    for i in range(len(text)):
        where[i + 1] = where[i] + keep[i]
    clean = "".join(ch for ch, k in zip(text, keep) if k)
    links = []
    for begin, finish, url in spans:
        a, b = where[begin], where[finish]
        while a < b and clean[a].isspace():
            a += 1
        while b > a and clean[b - 1].isspace():
            b -= 1
        if b > a:
            links.append((a, b, url))
    return clean, sorted(links)


def _tidy(s: str) -> str:
    lines = [ln.strip() for ln in s.replace("\xa0", " ").splitlines()]
    s = "\n".join(lines)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def _squash(s: str) -> str:
    return re.sub(r"\s+", " ", s.replace("\xa0", " ")).strip()


# ---------------------------------------------------------------- 任意のページの画像（matome --gallery URL）

LAZY_SRC_ATTRS = ("data-src", "data-original", "data-lazy-src", "data-lazy", "data-url", "src")
NOT_PICTURE_RE = re.compile(r"\.(svg|ico)([?#]|$)", re.I)


SRCSET_ENOUGH_W = 640  # srcset から選ぶ幅。タイルには十分（拡大・保存はリンク先の元画像を使う）


def _pick_srcset(srcset: str) -> str:
    """srcset（"a.jpg 480w, b.jpg 1080w"）から、幅 640 以上でいちばん小さいもの。無ければいちばん大きいもの。

    いちばん大きいものは数 MB の元画像のことがあり、画像が多いページで読み込みが詰まる。
    """
    cands: list[tuple[float, str]] = []
    for part in srcset.split(","):
        bits = part.strip().split()
        if not bits:
            continue
        m = re.fullmatch(r"([\d.]+)([wx])", bits[1]) if len(bits) > 1 else None
        n = float(m.group(1)) if m else 0.0
        if m and m.group(2) == "x":
            n *= 400  # 1x・2x の指定は幅が分からないので、だいたいの見積もり
        cands.append((n, bits[0]))
    if not cands:
        return ""
    enough = [c for c in cands if c[0] >= SRCSET_ENOUGH_W]
    return min(enough)[1] if enough else max(cands)[1]


def page_pictures(html_text: str, url: str) -> tuple[str, list[Picture]]:
    """ページの中の画像を全部拾う（本文に限らない）。（ページのタイトル, 画像）を返す。

    遅延読み込みの data-src など・srcset のほどよい大きさのもの・画像へのリンク・og:image も拾う。
    アイコンなどの小さい画像は、画像一覧の側で大きさを見て落とす。
    """
    tree = LexborHTMLParser(html_text)
    title_node = tree.css_first("title")
    title = _squash(title_node.text()) if title_node else ""
    found: dict[str, Picture] = {}

    def add(src: str, full: str = "") -> None:
        src = html.unescape((src or "").strip())
        if not src or src.startswith("data:"):
            return
        src = urljoin(url, src)
        if not src.startswith("http") or NOT_PICTURE_RE.search(src) or src in found:
            return
        found[src] = Picture(src, full)

    meta = tree.css_first('meta[property="og:image"]')
    for img in tree.css("img, source[srcset]"):
        attrs = img.attributes
        srcset = attrs.get("data-srcset") or attrs.get("srcset") or ""
        src = _pick_srcset(srcset) if srcset else ""
        src = src or next((attrs[a] for a in LAZY_SRC_ATTRS if attrs.get(a)), "")
        add(src, _linked_picture(img) if img.tag == "img" else "")
    for a in tree.css("a[href]"):
        if a.css_first("img"):  # 画像を包むリンクの先は、たいてい元画像のページ（上で full として拾っている）
            continue
        href = (a.attributes.get("href") or "").strip()
        if re.search(r"\.(jpe?g|png|gif|webp)([?#]|$)", href, re.I):
            add(href)
    if meta:
        add(meta.attributes.get("content") or "")
    return title, list(found.values())


async def fetch_page_pictures(c: httpx.AsyncClient, url: str) -> tuple[Entry, Article]:
    """URL のページを取り、画像を全部拾う。画像一覧で 1 記事として扱えるよう Entry と Article にする。"""
    r = await get(c, url)
    r.raise_for_status()
    final = str(r.url)
    title, pictures = page_pictures(decode(r), final)
    host = urlparse(final).hostname or final
    entry = Entry(Site(name=host, feed=final), title or host, final, time.time(), "")
    return entry, Article(final, list(pictures))


def image_path(url: str) -> Path:
    """画像のキャッシュのファイル（まだ無いこともある）。"""
    return CACHE_DIR / "img" / hashlib.sha1(url.encode()).hexdigest()


async def fetch_image(c: httpx.AsyncClient, url: str, referer: str) -> Path:
    """画像をキャッシュに落としてパスを返す。"""
    path = image_path(url)
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        headers = {"Referer": referer}
        async with c.stream("GET", url, headers=headers) as r:
            if r.status_code == 406:  # 圧縮を断るサイト。get が取り直す
                content = None
            else:
                r.raise_for_status()
                # 名前が .jpg でも中身はページのことがある（Wikipedia の「ファイル:〇〇.jpg」）。本文を読む前にやめる
                if r.headers.get("content-type", "").split(";")[0].strip().startswith(("text/", "application/json")):
                    raise ValueError(f"画像ではありません: {url}")
                content = await r.aread()
        if content is None:
            r = await get(c, url, headers=headers)
            r.raise_for_status()
            content = r.content
        tmp = path.with_suffix(".part")
        tmp.write_bytes(content)
        tmp.replace(path)
    return path
