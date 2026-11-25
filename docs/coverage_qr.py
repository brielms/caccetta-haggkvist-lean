"""Draw the coverage map in the coordinates of the rules: cutoff q = ceil(n/r) against degree r.

Each (q, r) square holds the r orders n = (q-1)r+1 .. qr, left to right, coloured by the first
source that closes that order (same priority as coverage.html). Reads the data embedded in
coverage.html; writes coverage-q-r.svg. Static SVG, so it renders in a GitHub README.
"""
import contextlib, io, json, re
from pathlib import Path

here = Path(__file__).resolve().parent
ns = {"__file__": str(here / "attribution_grids.py"), "__name__": "attribution_grids"}
with contextlib.redirect_stdout(io.StringIO()):
    exec(compile((here / "attribution_grids.py").read_text(encoding="utf-8"), "attribution_grids.py", "exec"), ns)
source = ns["source"]
data = json.loads(re.search(r'class="data">([^<]+)</script>', (here / "coverage.html").read_text(encoding="utf-8"))[1])
# Optional extra degrees: lines "ROW r cells" printed by Lean, in coverage-rows-ext.txt.
ext = here / "coverage-rows-ext.txt"
if ext.exists():
    for r, cells in re.findall(r"^ROW (\d+) ([0-9A-Za-z]+)\s*$", ext.read_text(encoding="utf-8-sig"), re.MULTILINE):
        assert int(r) == len(data) + 1
        data.append(cells)
R = len(data)
Q = 2 * R - 4
# Beyond the printed orders every cell is decided by a closed formula before the Lean data is read.
data = [row + "0" * max(0, Q * (i + 1) - len(row)) for i, row in enumerate(data)]
ns["rows"] = data
# id: (legend label, fill)
SRC = {
    "elem": ("Elementary: r = 1 or n ≤ 2r", "#8a8f94"),
    "ch": ("Caccetta–Häggkvist 1978", "#397aba"),
    "ham": ("Hamidoune 1987", "#cf7034"),
    "hr": ("Hoàng–Reed 1987", "#8158ac"),
    "hkn": ("Hladký–Král’–Norin", "#c95b8b"),
    "ms": ("Josh P., unpublished manuscript", "#e0ad43"),
    "shen": ("Shen 2000", "#3fa9b5"),
    "cap": ("briel (Lean)", "#188256"),
    "none": ("Open", None),
}
X0, Y0, W, H = 46, 78, (36 if R <= 12 else 32), (30 if R <= 12 else 28)
width, height = X0 + Q * W + 16, Y0 + R * H + 58
out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" width="{width}" height="{height}" '
       'font-family="-apple-system,BlinkMacSystemFont,Segoe UI,Helvetica,Arial,sans-serif" font-size="12">',
       '<title>Caccetta–Häggkvist: who closes each order, by cutoff and degree</title>',
       '<style>.t{fill:#57606a}.o{fill:none;stroke:#8c959f;stroke-width:.7}'
       '@media (prefers-color-scheme:dark){.t{fill:#9198a1}.o{stroke:#6e7681}}</style>']
# legend, two rows
x, y = X0, 18
for k, (label, fill) in SRC.items():
    wlab = 14 + 6.3 * len(label) + 18
    if x + wlab > width:
        x, y = X0, y + 20
    box = f'<rect x="{x}" y="{y - 10}" width="11" height="11" rx="2" ' + (f'fill="{fill}"/>' if fill else 'class="o"/>')
    out.append(box + f'<text class="t" x="{x + 16}" y="{y}">{label}</text>')
    x += wlab
for r in range(1, R + 1):
    yy = Y0 + (R - r) * H
    out.append(f'<text class="t" x="{X0 - 8}" y="{yy + H / 2 + 4}" text-anchor="end">{r}</text>')
    w = (W - 3) / r
    for q in range(1, Q + 1):
        for i in range(r):
            n = (q - 1) * r + i + 1
            if n > len(data[r - 1]):
                continue
            sid = source(n, r)
            if sid == "void":
                continue
            xx = X0 + (q - 1) * W + i * w
            fill = SRC[sid][1]
            attr = f'fill="{fill}"' if fill else 'class="o"'
            out.append(f'<rect x="{xx:.2f}" y="{yy + 1}" width="{max(w - 0.5, 0.9):.2f}" height="{H - 4}" {attr}>'
                       f'<title>r = {r}, q = {q}, n = {n}: {SRC[sid][0]}</title></rect>')
for q in range(1, Q + 1):
    out.append(f'<text class="t" x="{X0 + (q - 1) * W + (W - 3) / 2}" y="{Y0 + R * H + 14}" text-anchor="middle">{q}</text>')
out.append(f'<text class="t" x="{X0 + Q * W / 2}" y="{Y0 + R * H + 36}" text-anchor="middle">'
           'cutoff q = ⌈n/r⌉ · each square holds the r orders n = (q − 1)r + 1 … qr, left to right</text>')
out.append(f'<text class="t" x="14" y="{Y0 + R * H / 2}" text-anchor="middle" transform="rotate(-90 14 {Y0 + R * H / 2})">degree r</text>')
out.append('</svg>')
(here / "coverage-q-r.svg").write_text("\n".join(out), encoding="utf-8", newline="\n")
opn = sum(1 for r in range(1, R + 1) for n in range(1, len(data[r - 1]) + 1) if source(n, r) == "none")
print("wrote coverage-q-r.svg", width, height, "open cells in data:", opn)
