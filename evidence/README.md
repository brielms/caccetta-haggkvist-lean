# Saved full replay

The [26 Nov 2026 replay](https://github.com/brielms/caccetta-haggkvist-lean/commit/8b99e5c7b0c9ed59f5899d8a5cd7f4ec6a05cf20) of `checkpoints/shen_extension/Capstone.lean` ended with 32 open Lean contexts and one unsolved-goals diagnostic at the root. The reporter groups the alternatives into factors of 4, 4 and 2, giving 10 separate obligations by its counting convention. Full CH remains open.

This archive comes from a Windows replay of the byte-identical capstone using prebuilt imports. GitHub Actions builds the proof dependencies and compares the live frontier with this snapshot.

- [frontier.json](frontier.json) lists every open case, its conclusion and its line numbers in the decompressed Lean log.
- [Capstone.log.gz](Capstone.log.gz) contains the entire Lean output, including the hypotheses of each case.
- [catalog.trace.gz](catalog.trace.gz) contains the rule engine's trace from the same run.

To check the archive against the project's reporter, run the following command from the repository root with Python 3.

```sh
python evidence/check_snapshot.py
```

This reindexes the saved Lean output in a temporary directory and checks its SHA-256 digest. It compares every case, conclusion, line reference, published bound and obligation count. The reporter can select different illustrative statements tied for length. The saved index uses a relative path for the log. To run Lean itself, follow the build and replay instructions in the [main README](../README.md).
