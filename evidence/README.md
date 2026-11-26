# Saved full replay

The canonical replay of `checkpoints/shen_extension/Capstone.lean` ended with 48 open Lean contexts. The reporter groups their alternatives into factors of 6, 4 and 2, giving 12 separate obligations by its counting convention. The root has an unsolved-goals diagnostic. The source and receipt therefore document an incomplete proof of full CH.

The stored snapshot predates the import of `FlatTwoWitnesses` into the capstone. With that import, the replay of 26 Nov 2026 ends with 32 open contexts (factors of 4, 4 and 2, giving 10 separate obligations) and the same single unsolved-goals diagnostic at the root.

- [frontier.json](frontier.json) lists every open case, its conclusion and its line numbers in the decompressed Lean log.
- [Capstone.log.gz](Capstone.log.gz) contains the entire Lean output, including the hypotheses of each case.
- [catalog.trace.gz](catalog.trace.gz) contains the rule engine's trace from the same run.

To check the archive against the project's reporter, run the following command from the repository root with Python 3.

```sh
python evidence/check_snapshot.py
```

This reindexes the saved Lean output in a temporary directory and checks its SHA-256 digest. It compares every case, conclusion, line reference, published bound and obligation count. The reporter can select different illustrative statements tied for length. The saved index uses a relative path for the log. To run Lean itself, follow the build and replay instructions in the [main README](../README.md).
