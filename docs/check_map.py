"""Check that the interactive map embeds the orders printed by CoverageMap.lean."""

import json
import re
import sys
from pathlib import Path

log = Path(sys.argv[1]).read_text(encoding="utf-8-sig")
rows = re.findall(r"^ROW (\d+) ([0-9]{275})\s*$", log, re.MULTILINE)
html = Path(__file__).with_name("coverage.html").read_text(encoding="utf-8")
embedded = json.loads(re.search(r'class="data">([^<]+)</script>', html)[1])
if [int(r) for r, _ in rows] != list(range(1, 13)) or [row for _, row in rows] != embedded:
    raise SystemExit("Coverage map disagrees with Lean.")
print("All 3,300 degree/order classifications match Lean.")
