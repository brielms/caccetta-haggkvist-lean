# Saved full replay

The 27 Nov 2026 replay of [Capstone.lean](../checkpoints/shen_extension/Capstone.lean) ended with 16 open Lean contexts and one unsolved-goals diagnostic at the root. The reporter groups the alternatives into factors of 4, 2 and 2, giving 8 separate obligations by its counting convention. Full CH remains open.

The capstone now chooses a deletion bank with two surviving short rows. The 16 lone-bank contexts in the previous replay close. Eight open contexts retain the shared-parent alternative with $2^{q-1}<s$. The other eight retain the missed-parent alternative with $q(s-1)+3\le n$. The shared-parent contexts also carry the bound $2^{2^{\lfloor q/2\rfloor}+1}\le q(s-1)+3$. The domination bound $(2^{\lfloor q/2\rfloor}+2)2^{2^{\lfloor q/2\rfloor}-1}\le q(s-1)+3$ also holds in those eight shared-parent contexts. At $q=4$ it forces $s\ge 13$ for this alternative. The frontier index records all four bounds.

All 16 contexts now carry $s\ge 10$ and the exclusion of `DeletionWindow` on the surviving input. The replay derives both facts on the original input too. On the reduced leaves the deletion-window exclusion follows from the recorded bank bounds and the degree floor.

The eight shared-parent contexts carry `AtTriangle q (SharedTriangleBank source)` and the eight missed-parent contexts carry `AtTriangle q (MissedTriangleBank source)`. The cutoff stays symbolic in the full replay. The focused Lean checks in [BankRefinementReplayTest.lean](../checkpoints/shen_extension/BankRefinementReplayTest.lean) supply $q=3$ and exercise the matching labelled refinements. The frontier comparison checks the surviving-input facts and matching native guard separately for each named case.

Each shared-parent context additionally contains a native `CommonBank` with a maximal common-head pair, its `ForkLaw`, an actual assignment on that pair and a minimal repair obstruction. The same assignment witnesses a full row with arcs to two contested payers and a binary branching property through $q-1$ layers of original return arcs. At least $2^{q-1}$ distinct walk words start at the assigned head of the recorded short row. Distinct words may share vertices. All eight shared-parent contexts contain the matching assignment, branching property and word count. The eight missed-parent contexts carry no common-head-bank refinement. The frontier comparison checks these facts by named case and checks that the pair, assignment and root in the relevant hypotheses agree. The focused checks in [CommonHeadCutReplayTest.lean](../checkpoints/shen_extension/CommonHeadCutReplayTest.lean) exercise the symbolic shared and missed cases, two assignments and an unrelated-bank control.

[common_head_controls.py](../checkpoints/shen_extension/common_head_controls.py) checks the branching and word counts on directed cycle powers and a 116-vertex pair-dominating example, all above the critical order.

All eight shared-parent contexts also carry a cyclic layer count on the same native bank and assignment. The count uses one function of chosen rows for both layer membership and the bound. It charges the number of outside vertices, $q^2$, and $q$ times the number of distinct exterior heads against the backward arcs and the exterior heads counted with multiplicity. The comparator checks those row witnesses by named case. [CyclicLayerReplayTest.lean](../checkpoints/shen_extension/CyclicLayerReplayTest.lean) tests symbolic shared and missed cases, repeated replay and two assignments. [layer_count_controls.py](../checkpoints/shen_extension/layer_count_controls.py) checks the layer statistics on examples above the critical order.

This archive comes from a Windows replay with Lean 4.35.0 using prebuilt imports. GitHub Actions builds the proof dependencies and compares the live frontier with this snapshot.

- [frontier.json](frontier.json) lists every open case, its conclusion and its line numbers in the decompressed Lean log.
- [Capstone.log.gz](Capstone.log.gz) contains the entire Lean output, including the hypotheses of each case.
- [catalog.trace.gz](catalog.trace.gz) contains the rule engine's trace from the same run.

To check the archive against the project's reporter, run the following command from the repository root with Python 3.

```sh
python evidence/check_snapshot.py
```

This reindexes the saved Lean output in a temporary directory and checks its SHA-256 digest. It compares every case, conclusion, line reference, published bound and obligation count. The reporter can select different illustrative statements tied for length. The saved index uses a relative path for the log. To run Lean itself, follow the build and replay instructions in the [main README](../README.md).
