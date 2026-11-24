# Caccetta–Häggkvist in Lean

Goal: every loopless digraph on n vertices with minimum outdegree r has a directed cycle of length at most ⌈n/r⌉. **Open.** The [capstone](checkpoints/shen_extension/Capstone.lean) replay leaves [48 Lean contexts](evidence/README.md).

## Results ([Lean](checkpoints/shen_extension/PublicResults.lean))

Each line names a theorem in that file, proved with the standard axioms only.

- **Beyond Shen's range at every degree** (`beyond_shen`). [Shen](https://www.sciencedirect.com/science/article/pii/S0012365X99003234) proved the bound for n ≥ 2r² − 3r + 1. Lean proves it for n ≥ 2r² − G·r + 1 with
  - G = 6 at every degree r,
  - G = 7 for r ≥ 12, G = 8 for r ≥ 59, G = 9 for r ≥ 8192,
  - every G with r ≥ 35840·G².
- **Most of each strip below that** (`strip_window`): at cutoff ⌈n/r⌉ = 2r − g with 3g ≤ r, every n ≤ ⌈n/r⌉·r − 3g².
- **All orders n for 1 ≤ r ≤ 8** (`degree_one_to_eight`).
- **r = 9**: every n except 36, 44, 45, 54, 59–63, 67–72, 77–81, 89, 90, 98, 99 and 108 (`degree_nine_except`).
- n = 34 or 35 with r = 9: a cycle of length at most 4 (`degree_nine_at_34_or_35`). [Liang–Xu](https://content.scirp.org/pdf/AM20120700013_11769404.pdf) give 5.
- Every (n, r) with a nonzero cell in the coverage map (`of_covered_cell`).

![Who closes each order n and degree r](docs/attribution-n-r.svg)

Sources: [Caccetta–Häggkvist](https://www.sciencedirect.com/science/article/pii/0095895687900098) · Hamidoune · [Hoàng–Reed](https://www.sciencedirect.com/science/article/pii/0012365X87901221) · [Shen](https://www.sciencedirect.com/science/article/pii/S0012365X99003234) · [Hladký–Král’–Norin](https://arxiv.org/abs/0908.2791) · [Josh P. (unpublished)](https://github.com/joshp123/solve-a-maths-problem-dont-care-which-make-no-mistakes/blob/main/paper/manuscript.md). Each cell is credited to the first of these that covers it, and to Lean only when none does, so Lean also proves many cells shown under an earlier name. The comparison is with these sources only. Lean cells are certified by [CoverageMap.lean](docs/CoverageMap.lean); [interactive map](docs/coverage.html).

## Check

```bash
lake exe cache get
bash checkpoints/shen_extension/check_capstone.sh --build-only
lake env lean checkpoints/shen_extension/PublicResults.lean
bash checkpoints/shen_extension/check_capstone.sh --replay   # exits 1: the open goals
```

Vendored Apache-2.0 proof: [notice](checkpoints/shen_extension/vendor/seymour/README.md).
