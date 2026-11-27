"""Compare named open conclusions and their reported bounds with the reference run."""

import json
import sys
from pathlib import Path


def signature(data):
    leaves = [(row["case"], row["missing_implication_conclusion"]) for row in data["leaves"]]
    return (
        sorted(leaves), data["open_leaves"], data["published_bounds"],
        data["independent_obligations"]["separate_obligations"], data.get("native_bank_refinements", {}),
    )


if __name__ == "__main__":
    [live_path] = sys.argv[1:]
    baseline = json.loads(Path(__file__).with_name("frontier.json").read_text(encoding="utf-8"))
    live = json.loads(Path(live_path).read_text(encoding="utf-8"))
    if signature(live) != signature(baseline):
        raise SystemExit("Frontier changed. Inspect the uploaded Lean diagnostic.")
    print(f"Reproduced {live['open_leaves']} open contexts and their reported bounds.")
