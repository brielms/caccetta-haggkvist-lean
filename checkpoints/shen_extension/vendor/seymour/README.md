# Seymour's second-neighborhood theorem

The 43 files under `OAI/Combinatorics/SecondNeighborhood` come from the OpenAI mathematics release, commit `4eaee87548250b2682affda7d05d947c05554bae`. The import that provides the proof is `OAI.Combinatorics.SecondNeighborhood.Main`. The release also provides a separate comparator statement. [Upstream proof](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Combinatorics/SecondNeighborhood/Main.lean)

The sources were copied from the local `CH_Seymour_Pinned_Verification_20261104` corpus archive and checked against its SHA-256 source manifest before copying. The archive used Lean 4.34.1. The Shen project builds the sources using its own pinned Lean and Mathlib. The upstream license is included in `LICENSE.openai-math`.

From the LeanCH root, build the proof with `lake build OAI.Combinatorics.SecondNeighborhood.Main`. The Shen adapter lives in `checkpoints/shen_extension/SeymourTransition.lean`.
