# Caccetta–Häggkvist in Lean

Goal: every loopless digraph on n vertices with minimum outdegree r has a directed cycle of length at most ⌈n/r⌉. **Open.** The [capstone](checkpoints/shen_extension/Capstone.lean) replay leaves [48 Lean contexts](evidence/README.md).

## Results ([Lean](checkpoints/shen_extension/PublicResults.lean))

- All orders n for 1 ≤ r ≤ 8 (`degree_one_to_eight`).
- n = 34 or 35 with r = 9: a cycle of length at most 4 (`degree_nine_at_34_or_35`). [Liang–Xu](https://content.scirp.org/pdf/AM20120700013_11769404.pdf) give 5.

![Who closes each order n and degree r](docs/attribution-n-r.svg)

Sources: [Caccetta–Häggkvist](https://www.sciencedirect.com/science/article/pii/0095895687900098) · Hamidoune · [Hoàng–Reed](https://www.sciencedirect.com/science/article/pii/0012365X87901221) · [Shen](https://www.sciencedirect.com/science/article/pii/S0012365X99003234) · [Hladký–Král’–Norin](https://arxiv.org/abs/0908.2791) · [Josh P. (unpublished)](https://github.com/joshp123/solve-a-maths-problem-dont-care-which-make-no-mistakes/blob/main/paper/manuscript.md). Lean cells are certified by [CoverageMap.lean](docs/CoverageMap.lean); [interactive map](docs/coverage.html).

## Check

```bash
lake exe cache get
bash checkpoints/shen_extension/check_capstone.sh --build-only
lake env lean checkpoints/shen_extension/PublicResults.lean
bash checkpoints/shen_extension/check_capstone.sh --replay   # exits 1: the open goals
```

Vendored Apache-2.0 proof: [notice](checkpoints/shen_extension/vendor/seymour/README.md).
