"""Draw static attribution grids for the README from docs/coverage.html.

Run from the repository root:  python docs/attribution_grids.py
Writes docs/attribution-n-r.svg (every order n against degree r).
The source of each order is chosen by the same rule as `assess` in coverage.html.
"""
import json
import re
from pathlib import Path

DOCS = Path(__file__).resolve().parent
html = (DOCS / "coverage.html").read_text(encoding="utf-8")
rows = json.loads(re.search(r'class="data">([^<]+)</script>', html)[1])
R, N = len(rows), len(rows[0])

# id: (legend label, short label for direct annotation, fill, text colour on the fill)
SOURCES = {
    "ch": ("Caccetta–Häggkvist 1978", "Caccetta–Häggkvist 1978", "#397aba", "#ffffff"),
    "ham": ("Hamidoune 1987", "Hamidoune 1987", "#cf7034", "#ffffff"),
    "hr": ("Hoàng–Reed 1987", "Hoàng–Reed 1987", "#8158ac", "#ffffff"),
    "shen": ("Shen 2000, n ≥ 2r² − 3r + 1", "Shen", "#278e9d", "#ffffff"),
    "hkn": ("Hladký–Král’–Norin, r ≥ 0.3465n", "HKN", "#c95b8b", "#ffffff"),
    "elem": ("Elementary: r = 1 or n ≤ 2r", "elementary", "#5f6d73", "#ffffff"),
    "ms": ("Josh P., unpublished degree-six manuscript", "Josh P.", "#e0ad43", "#24313a"),
    "cap": ("This project, proved in Lean", "Lean", "#188256", "#ffffff"),
    "none": ("Open: no listed source", "open", "#e4e9eb", "#59686e"),
    "void": ("No such digraph (n ≤ r)", "", "#ffffff", "#59686e"),
}
AUTHORS = ["", "elem", "ch", "ham", "hr", "hr"]
INK, MUTED, GRID = "#1f2b31", "#59686e", "#ffffff"
FONT = 'font-family="-apple-system,BlinkMacSystemFont,Segoe UI,Helvetica,Arial,sans-serif"'


def source(n, r):
    """First applicable source, in the priority order of coverage.html."""
    q = -(-n // r)
    if n <= r:
        return "void"
    hits = []
    if r <= 5:
        hits.append(AUTHORS[r])
    if n <= 2 * r:
        hits.append("elem")
    if n >= 2 * r * r - 3 * r + 1:
        hits.append("shen")
    if q >= 3 and 10000 * r >= 3465 * n:
        hits.append("hkn")
    for d in range(r - 1, 0, -1):  # delete vertices down to a smaller degree
        m = min(n, q * d)
        loss = n - m
        if m <= d or d + loss > r:
            continue
        if d <= 5:
            hits.append(AUTHORS[d])
        if m >= 2 * d * d - 3 * d + 1:
            hits.append("shen")
    if r >= 6:
        m = min(n, 6 * q)
        if r - (n - m) >= 6:
            hits.append("ms")
    if rows[r - 1][n - 1] != "0":
        hits.append("cap")
    return hits[0] if hits else "none"


grid = [[source(n, r) for n in range(1, N + 1)] for r in range(1, R + 1)]
counts = {}
for row in grid:
    for s in row:
        counts[s] = counts.get(s, 0) + 1


def fill(sid):
    return {"ms": "url(#gold)", "void": "url(#void)"}.get(sid, SOURCES[sid][2])


DEFS = """<defs>
<pattern id="gold" width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><rect width="6" height="6" fill="#e0ad43"/><rect width="1.6" height="6" fill="#f6e3b8"/></pattern>
<pattern id="void" width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><rect width="6" height="6" fill="#ffffff"/><rect width="1" height="6" fill="#c3ccd0"/></pattern>
</defs>"""


def text_w(s, size):
    return len(s) * size * 0.56


def legend(y, width, left, used, with_counts):
    out, x, line = [], left, y
    order = ["ch", "ham", "hr", "shen", "hkn", "elem", "ms", "cap", "none", "void"]
    for sid in order:
        if sid not in used:
            continue
        label = SOURCES[sid][0] + (f"  ·  {counts[sid]}" if with_counts and sid != "void" else "")
        w = 20 + text_w(label, 12)
        if x + w > width - 16:
            x, line = left, line + 22
        stroke = ' stroke="#c3ccd0"' if sid in ("none", "void") else ""
        out.append(f'<rect x="{x}" y="{line - 10}" width="13" height="13" rx="2" fill="{fill(sid)}"{stroke}/>'
                   f'<text x="{x + 19}" y="{line + 1}" font-size="12" fill="{INK}">{label}</text>')
        x += w + 16
    return "\n".join(out), line


def page(width, height, body):
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" width="{width}" height="{height}" {FONT}>\n'
            f'{DEFS}\n<rect width="{width}" height="{height}" fill="#ffffff"/>\n{body}\n</svg>\n')


used = set(counts)

# ---------------------------------------------------------------- order n by degree r
W, left, right, top, rowh = 1000, 52, 16, 64, 28
cw = (W - left - right) / N
p = [f'<text x="{left}" y="24" font-size="17" font-weight="600" fill="{INK}">Who closes Caccetta–Häggkvist at each order n and minimum outdegree r</text>',
     f'<text x="{left}" y="44" font-size="12.5" fill="{MUTED}">One cell per pair (n, r). Colour is the first source that forces a directed cycle of length at most ⌈n/r⌉; published results come first.</text>']
for n in range(25, N + 1, 25):
    x = left + n * cw
    p.append(f'<line x1="{x:.1f}" x2="{x:.1f}" y1="{top}" y2="{top + R * rowh - 3}" stroke="{INK}" stroke-opacity=".10"/>')
labelled = set()
for r in range(1, R + 1):
    y = top + (R - r) * rowh
    p.append(f'<text x="{left - 10}" y="{y + rowh / 2 + 1}" font-size="12" text-anchor="end" dominant-baseline="middle" fill="{MUTED}">{r}</text>')
    n = 1
    while n <= N:
        sid, end = grid[r - 1][n - 1], n
        while end < N and grid[r - 1][end] == sid:
            end += 1
        x0, w = left + (n - 1) * cw, (end - n + 1) * cw
        p.append(f'<rect x="{x0:.2f}" y="{y}" width="{w:.2f}" height="{rowh - 3}" fill="{fill(sid)}"/>')
        name = SOURCES[sid][1]
        if r <= 5 and sid == AUTHORS[r] and sid != "elem":
            name = SOURCES[sid][1] + f", r = {r}"
        if name and sid not in ("void",) and (sid != "hr" or r in (4, 5)) and w > text_w(name, 11.5) + 10:
            if sid in ("shen", "cap", "none") or sid not in labelled or r <= 5:
                p.append(f'<text x="{x0 + w / 2:.1f}" y="{y + (rowh - 3) / 2 + 1}" font-size="11.5" text-anchor="middle" dominant-baseline="middle" fill="{SOURCES[sid][3]}">{name}</text>')
                labelled.add(sid)
        n = end + 1
base = top + R * rowh
for n in [1] + list(range(25, N + 1, 25)):
    x = left + (n - 0.5) * cw if n == 1 else left + n * cw
    p.append(f'<text x="{x:.1f}" y="{base + 12}" font-size="12" text-anchor="middle" fill="{MUTED}">{n}</text>')
p.append(f'<text x="{left + (W - left - right) / 2}" y="{base + 32}" font-size="12.5" text-anchor="middle" fill="{INK}">order n (vertices)</text>'
         f'<text x="16" y="{top + R * rowh / 2}" font-size="12.5" text-anchor="middle" fill="{INK}" transform="rotate(-90 16 {top + R * rowh / 2})">minimum outdegree r</text>')
leg, last = legend(base + 62, W, left, used, True)
p.append(leg)
p.append(f'<text x="{left}" y="{last + 24}" font-size="11.5" fill="{MUTED}">Numbers count cells. Published bounds also apply after deleting vertices. Lean cells are certified by docs/CoverageMap.lean.</text>')
(DOCS / "attribution-n-r.svg").write_text(page(W, last + 38, "\n".join(p)), encoding="utf-8")

print("cells by first source:", counts)
