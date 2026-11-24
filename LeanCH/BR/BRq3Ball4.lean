import LeanCH.BR.BRq3Layer

/-!
# `Ball(4,3)` and `BR(4,3)`, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq2_attempt_subagent.md`, §6.3 (Lemma 6.3, Corollary 6.3′), audited in
`BRq2_audit_subagent.md` §3.

* `ball43` (Lemma 6.3): a 4-free digraph with out-degree exactly three on `W` has `|B_3(u)| ≥ 10`.
  Cases: `n_2 = 3` (`n3_of_three`); `n_2 ∈ {4,5}` with `n_3 ≤ 1` contradicts Corollary B (`corB_layer`);
  otherwise `n_2 + n_3 ≥ 6` directly.
* `br_four_three` (Corollary 6.3′): `BoundaryRegular 4 3`, by Lemma 6.1 (`br_of_ball`).
* `ch_three_four`: every loopless digraph on `n ≤ 12` labels with min out `≥ 3` has a directed cycle of length `≤ 4`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2 Compose.Boundary

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

/-- **Lemma 6.3 (`Ball(4,3)`).** -/
theorem ball43 (hfree : QFree D W 4) (hout : OutEq 3 D W) (hu : u ∈ W) : 10 ≤ (ball D W u 3).card := by
  have h1 := card_ball_one (hfree.mono_bound (by omega)) hout hu
  have h12 : ball D W u 1 ⊆ ball D W u 2 := ball_mono_radius (by omega)
  have h23 : ball D W u 2 ⊆ ball D W u 3 := ball_mono_radius (by omega)
  have e2 := Finset.card_sdiff_add_card_eq_card h12
  have e3 := Finset.card_sdiff_add_card_eq_card h23
  have h62 := six_two (hfree.mono_bound (by omega)) hout hu
  by_cases hc : (ball D W u 2 \ ball D W u 1).card = 3
  · have := n3_of_three hfree hout hu hc
    omega
  · by_cases hc2 : (ball D W u 3).card ≤ (ball D W u 2).card + 1
    · have := corB_layer (q := 4) (k := 2) (by omega) (by omega) hfree hout hu hc2
      omega
    · omega

/-- **`BR(4,3)`** (Corollary 6.3′). Every loopless digraph on 13 labels with minimum out-degree `3` and no directed
cycle of length at most `4` has every in-degree exactly `3`. -/
theorem br_four_three : BoundaryRegular 4 3 :=
  br_of_ball (by omega) (fun _ _ hfree hout _ hu => ball43 hfree hout hu)

/-- CH at degree three below the `q = 4` boundary: on `n ≤ 12` labels, min out `≥ 3` forces a cycle of
length `≤ 4`. -/
theorem ch_three_four {n : ℕ} (hn : 0 < n) (hn12 : n ≤ 12) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n 3) : CH.HasDirectedCycleAtMost G n 4 :=
  ch_of_boundaryRegular (by omega) br_four_three hn (by omega) loopless deg

end LeanCH.BR.BRq3
