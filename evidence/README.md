# Saved full replay

The 27 Nov 2026 replay of [Capstone.lean](../checkpoints/shen_extension/Capstone.lean) ended with 16 open Lean contexts and one unsolved-goals diagnostic at the root. The reporter groups the alternatives into factors of 4, 2 and 2, giving 8 separate obligations by its counting convention. Full CH remains open.

The capstone now chooses a deletion bank with two surviving short rows. The 16 lone-bank contexts in the previous replay close. Eight open contexts retain the shared-parent alternative with $2^{q-1}<s$. The other eight retain the missed-parent alternative with $q(s-1)+3\le n$. The shared-parent contexts also carry the bound $2^{2^{\lfloor q/2\rfloor}+1}\le q(s-1)+3$. All three bounds are recorded in the frontier index.

This archive comes from a Windows replay with Lean 4.35.0 using prebuilt imports. GitHub Actions builds the proof dependencies and compares the live frontier with this snapshot.

- [frontier.json](frontier.json) lists every open case, its conclusion and its line numbers in the decompressed Lean log.
- [Capstone.log.gz](Capstone.log.gz) contains the entire Lean output, including the hypotheses of each case.
- [catalog.trace.gz](catalog.trace.gz) contains the rule engine's trace from the same run.

To check the archive against the project's reporter, run the following command from the repository root with Python 3.

```sh
python evidence/check_snapshot.py
```

This reindexes the saved Lean output in a temporary directory and checks its SHA-256 digest. It compares every case, conclusion, line reference, published bound and obligation count. The reporter can select different illustrative statements tied for length. The saved index uses a relative path for the log. To run Lean itself, follow the build and replay instructions in the [main README](../README.md).
