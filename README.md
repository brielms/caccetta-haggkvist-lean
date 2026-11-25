# Caccetta–Häggkvist in Lean

Goal: every loopless digraph on n vertices with minimum outdegree r has a directed cycle of length at most ⌈n/r⌉. **Open.** The [capstone](checkpoints/shen_extension/Capstone.lean) replay leaves [48 Lean contexts](evidence/README.md).

## Results ([Lean](checkpoints/shen_extension/PublicResults.lean))

- CH is proved for all orders n for 1 ≤ r ≤ 8 (`degree_one_to_eight`).
- CH holds for r = 9 and n ∈ {34, 35}: every loopless digraph on n vertices with minimum outdegree 9 has a directed cycle of length at most 4 = ⌈n/9⌉ (`degree_nine_at_34_or_35`). This improves the bound of 5 that follows from [Liang–Xu](https://content.scirp.org/pdf/AM20120700013_11769404.pdf), who prove a directed cycle of length at most 5 whenever r ≥ 0.24817n.
- Extension of the [Shen](https://www.sciencedirect.com/science/article/pii/S0012365X99003234) bound (`beyond_shen`):

| | Degrees | CH holds for |
|---|---|---|
| Shen | every r | n ≥ 2r² − 3r + 1 |
| Lean | every r | n ≥ 2r² − 7r + 1 |
| Lean | r ≥ 13 | n ≥ 2r² − 8r + 1 |
| Lean | r ≥ 6276 | n ≥ 2r² − 9r + 1 |
| Lean | r ≥ 424·G² | n ≥ 2r² − G·r + 1 |

Also proved (every theorem named here uses the standard axioms only):

- Strip windows. Write q = 2r − g. A loopless digraph with minimum outdegree r and 1 ≤ n ≤ the bound in this table has a directed cycle of length at most q (fractions rounded down):

  | Theorem | Condition on g | Largest order n covered |
  |---|---|---|
  | `strip_window` | 1 ≤ g, 3g ≤ 2r | q·r − (g − 1)²/2 |
  | `strip_window_eighth` | 2g + 2 ≤ r, g² ≤ 8r | q·r − ((g + 2)² + 1)/8 |
  | `strip_window_tight` | 1 ≤ g, 3g ≤ 2r | q·r − g(g − 3)/2 for g ≥ 3, q·r for g ≤ 2; for even g ≥ 4 also q·r + 1 − (g − 2)²/2 |
  | `strip_window_eighth_tight` | 2g + 2 ≤ r, g² ≤ 8r | q·r − (g(g + 4) − 7)/8 |

- Degree one above the cutoff. A loopless digraph with minimum outdegree q + 1 and 1 ≤ n ≤ `CollarRule.collarBound q` has a directed cycle of length at most q (`collar_row`).
- Degree equal to the cutoff. A loopless digraph with minimum outdegree q and 1 ≤ n ≤ `FlatRule.flatBound q` has a directed cycle of length at most q (`flat_row`).
- Degree two above the cutoff. A loopless digraph with minimum outdegree q + 2 and 1 ≤ n ≤ `TightRule2.tightBound2 q` has a directed cycle of length at most q (`tight_row`).
- Thin roots. A loopless digraph with minimum outdegree r and 1 ≤ n ≤ `ThinRule.thinBound q r` has a directed cycle of length at most q (`thin_row`).
- Degree nine. CH holds for r = 9 at every n except 63 (`degree_nine_except`).
- The coverage map. CH holds at every (n, r) whose cell in the map is nonzero (`of_covered_cell`).

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
