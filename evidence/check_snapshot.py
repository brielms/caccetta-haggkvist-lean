"""Reproduce the full saved frontier index from its archived Lean diagnostic."""

import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    evidence = Path(__file__).resolve().parent
    reporter = evidence.parent / "checkpoints/shen_extension/report_family_frontier.py"
    expected = json.loads((evidence / "frontier.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as directory:
        log = Path(directory) / expected["source_log"]
        with gzip.open(evidence / "Capstone.log.gz", "rb") as source, log.open("wb") as output:
            shutil.copyfileobj(source, output)
        if hashlib.sha256(log.read_bytes()).hexdigest() != expected["sha256"]:
            raise SystemExit("The archived Lean log has a different SHA-256 digest.")
        result = subprocess.run([sys.executable, str(reporter), str(log)], check=True, stdout=subprocess.PIPE)
        actual = json.loads(result.stdout)
        actual["source_log"] = Path(actual["source_log"]).name
        # The reporter samples six examples by length from a Python set. Ties
        # can yield different illustrations while the proof contexts are identical.
        for index in (actual, expected):
            for factor in index["independent_obligations"]["factors"]:
                factor.pop("shortest_varying_statements")
        if actual != expected:
            raise SystemExit("The regenerated frontier differs from the saved index.")
    print(f"Verified {actual['open_leaves']} open contexts and "
          f"{actual['independent_obligations']['separate_obligations']} separate obligations.")


if __name__ == "__main__":
    main()
