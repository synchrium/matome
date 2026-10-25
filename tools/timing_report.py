"""matome の timing.log を先読みあり／なしで集計する。

    .venv/bin/python tools/timing_report.py            # ~/.local/state/matome/timing.log
    .venv/bin/python tools/timing_report.py ログ ...    # ファイルを指定
"""
import json, math, os, sys, statistics as st
from pathlib import Path
from collections import Counter, defaultdict

def med(xs): return f"{st.median(xs):6.0f}ms" if xs else "     -  "
def p90(xs):
    if not xs:
        return "     -  "
    xs = sorted(xs)
    return f"{xs[min(len(xs) - 1, math.ceil(len(xs) * 0.9) - 1)]:6.0f}ms"

state = Path(os.environ.get("XDG_STATE_HOME") or Path.home() / ".local/state")
files = sys.argv[1:] or [state / "matome" / "timing.log"]
rows = [json.loads(l) for f in files for l in open(f, encoding="utf-8") if l.strip()]
by = defaultdict(list)
for r in rows: by[r["prefetch"]].append(r)
for pf in sorted(by, reverse=True):
    rs = by[pf]
    opens = [r for r in rs if r["ev"] == "open" and r.get("kind") == "article"]
    shown = [r["ms"] for r in rs if r["ev"] == "shown"]
    imgs = [r for r in rs if r["ev"] == "images"]
    gal = [r for r in rs if r["ev"] == "open" and r.get("kind") == "gallery"]
    print(f"== 先読み{'あり' if pf else 'なし'}")
    print(f"  記事を開いた回数 {len(opens)}  内訳 {dict(Counter(r['how'] for r in opens))}")
    print(f"  本文を取る待ち時間   中央値 {med([r['wait_ms'] for r in opens])}  90% {p90([r['wait_ms'] for r in opens])}")
    print(f"  開いて本文が出るまで 中央値 {med(shown)}  90% {p90(shown)}")
    if imgs:
        n = sum(r["n"] for r in imgs); d = sum(r["on_disk"] for r in imgs)
        print(f"  画像が全部出るまで   中央値 {med([r['ms'] for r in imgs])}  （開いた時点でキャッシュ済み {d}/{n} 枚）")
    if gal:
        print(f"  画像一覧の記事 {len(gal)} 件  内訳 {dict(Counter(r['how'] for r in gal))}")
    gs = [r for r in rs if r["ev"] == "gallery"]
    if gs:
        done = [r for r in gs if r["finished"]]
        print(f"  画像一覧を開いた回数 {len(gs)}（読み終わる前に閉じた {len(gs) - len(done)} 回）")
        def col(key, rows=gs): return [r[key] for r in rows if r.get(key) is not None]
        print(f"    最初のタイルが出るまで   中央値 {med(col('first_tile_ms'))}  90% {p90(col('first_tile_ms'))}")
        print(f"    最初の 1 画面がそろうまで 中央値 {med(col('first_screen_ms'))}  90% {p90(col('first_screen_ms'))}")
        print(f"    全部そろうまで           中央値 {med(col('done_ms', done))}  90% {p90(col('done_ms', done))}")
        arts, pre = sum(r["articles"] for r in gs), sum(r["prefetched"] for r in gs)
        imgs, disk = sum(r["images"] for r in gs), sum(r["on_disk"] for r in gs)
        print(f"    開いた時点で先読み済みの記事 {pre}/{arts}  キャッシュ済みの画像 {disk}/{imgs}")
    pre = [r for r in rs if r["ev"] == "prefetch"]
    if pre:
        used = {r["url"] for r in opens if r["how"] in ("ready", "inflight")}
        print(f"  先読みした記事 {len(pre)} 件  そのうち開かれた {len(used & {r['url'] for r in pre})} 件（むだになった通信の目安）")
