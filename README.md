# Caccetta–Häggkvist in Lean

This repository develops the [full recursive capstone](checkpoints/shen_extension/Capstone.lean). For arbitrary positive order `n` and minimum outdegree `r`, the goal is a directed cycle of length at most ⌈n/r⌉. **The full proof is open.** The [reference replay](evidence/README.md) leaves 48 Lean contexts grouped into 12 obligations.

## Results

**All orders at degrees 6, 7 and 8.** Together with the classical cases through degree 5, Lean proves that for every positive order n and minimum outdegree r with 1 ≤ r ≤ 8, there is a directed cycle of length at most ⌈n/r⌉. [All-orders degree bound](checkpoints/shen_extension/QuotaProjectionReplay.lean#L54)

**Selected orders at degree 9.** At both 34 and 35 vertices, minimum outdegree 9 guarantees a directed cycle of length at most **4**. At these same orders, Liang and Xu’s density bounds guarantee a cycle of length at most **5** at degree 9. Their four-cycle bound of 0.28724n requires degree 10 at order 34 and degree 11 at order 35. [Shared-head bound](checkpoints/shen_extension/SharedHeadSuppliers.lean#L585) · [Ball equality](LeanCH/BR/BRTwoBallEquality.lean#L53) · [Second-neighbour witness](checkpoints/shen_extension/PowerReceiverBudget.lean#L9) · [Liang–Xu five-cycle bound](https://www.scirp.org/journal/paperinformation?paperid=20013) · [Liang–Xu four-cycle bound](https://doi.org/10.12386/A2013sxxb0049)

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
