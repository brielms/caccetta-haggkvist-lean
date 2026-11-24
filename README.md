# Caccetta–Häggkvist in Lean

This repository develops the [full recursive capstone](checkpoints/shen_extension/Capstone.lean). For arbitrary positive order `n` and minimum outdegree `r`, the goal is a directed cycle of length at most ⌈n/r⌉. **The full proof is open.** The [reference replay](evidence/README.md) leaves 48 Lean contexts grouped into 12 obligations.

[![Coverage by minimum outdegree and integer quotient, colored by source](docs/coverage.png)](docs/coverage.html)

[Download the interactive map](https://raw.githubusercontent.com/brielms/caccetta-haggkvist-lean/main/docs/coverage.html) and open it in a browser to inspect exact orders and sources. Green marks coverage from this project beyond the comparison bounds shown. Striped gold marks overlap with [Josh P.’s unpublished degree-six manuscript](https://github.com/joshp123/solve-a-maths-problem-dont-care-which-make-no-mistakes/blob/main/paper/manuscript.md). The [Lean map theorem](docs/CoverageMap.lean) certifies the project exclusions.

With [Elan](https://github.com/leanprover/elan), Python 3 and Bash installed, run:

```bash
lake exe cache get
bash checkpoints/shen_extension/check_capstone.sh --build-only
bash checkpoints/shen_extension/check_regressions.sh
bash checkpoints/shen_extension/check_capstone.sh --replay
```

The last command currently exits with Lean’s open-goal diagnostic. [GitHub Actions](.github/workflows/replay.yml) checks that the live replay reproduces the named open conclusions and published bounds. See the [worklist guide](checkpoints/shen_extension/RecursiveFamilyWorklist.md) for the rule engine and the [upstream notice](checkpoints/shen_extension/vendor/seymour/README.md) for the vendored Apache-2.0 proof.
