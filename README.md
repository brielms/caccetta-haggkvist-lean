# Caccetta–Häggkvist in Lean

Goal: every loopless digraph on n vertices with minimum outdegree r has a directed cycle of length at most ⌈n/r⌉. **Open.** The [capstone](checkpoints/shen_extension/Capstone.lean) replay leaves [48 Lean contexts](evidence/README.md).

## Results ([Lean](checkpoints/shen_extension/PublicResults.lean))

- CH is proved for all orders n for 1 ≤ r ≤ 8 (`degree_one_to_eight`).
- CH holds for r = 9 and n ∈ {34, 35}: every loopless digraph on n vertices with minimum outdegree 9 has a directed cycle of length at most 4 = ⌈n/9⌉ (`degree_nine_at_34_or_35`). This improves the bound of 5 that follows from [Liang–Xu](https://content.scirp.org/pdf/AM20120700013_11769404.pdf), who prove a directed cycle of length at most 5 whenever r ≥ 0.24817n.
- Extension of the [Shen](https://www.sciencedirect.com/science/article/pii/S0012365X99003234) bound (`beyond_shen`):

| | Degrees | CH holds for |
|---|---|---|
| Shen | every r | n ≥ 2r² − 3r + 1 |
| Lean | every r | n ≥ 2r² − 6r + 1 |
| Lean | r ≥ 12 | n ≥ 2r² − 7r + 1 |
| Lean | r ≥ 59 | n ≥ 2r² − 8r + 1 |
| Lean | r ≥ 8192 | n ≥ 2r² − 9r + 1 |
| Lean | r ≥ 35840·G² | n ≥ 2r² − G·r + 1 |

Also proved: at cutoff ⌈n/r⌉ = 2r − g with 3g ≤ r, every n ≤ ⌈n/r⌉·r − 3g² (`strip_window`); r = 9 for every n except 36, 44, 45, 54, 59–63, 67–72, 77–81, 89, 90, 98, 99 and 108 (`degree_nine_except`); every (n, r) with a nonzero cell in the coverage map (`of_covered_cell`). Every theorem named here uses the standard axioms only.

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
