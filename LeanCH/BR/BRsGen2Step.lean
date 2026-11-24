import LeanCH.BR.BRsGen2Cor

/-!
# General `s`: the count and the `e = 2` case of the inductive step (Lean 4.35.0)

Paper: `BallQ5_attempt_subagent.md` §3 (Theorem Q5 and the count `(s+1-c)|P| ≤ 2s+1+e-c`) and §6 (Proposition T).
The `s = 4` version is `BRq4Step.lean` (`thm16_core`, `thm16`). No existing file is changed.

Level `k = j + 3`, `c = |K|`, `P = |P|`.

* `count_two` (`e = 2`, `4 ≤ s`): `P·(s-c-1) + P ≤ n_{k-1} + n_k`, `P·(s-c) + P ≤ n_{k-1} + n_k` if `c ≥ 2`,
  and `2P ≥ k+3`. This is `(s+1-c-[c=1])·P ≤ n_{k-1} + n_k`.
* `upper_two`: `b_{k-2} ≥ s(k-2)+1` gives `n_{k-1} + n_k + c ≤ 2s+3` (= `2s+1+e`, `e = 2`).
* `thm_e2_core_s` (**Theorem Q5 for every `s ≥ 5`**): `GSet s 2` with `b_{k-1} ≥ s(k-1)+1` and
  `b_{k-2} ≥ s(k-2)+1` is contradictory when `k ≥ 4`, or `k = 3` and `s ≥ 7`. Counting alone; no CH input.
* `step_e2_s` (**conditional step**): `BallSmall(k,s)` (`Diam_k`), `Ball(k+1,s)`, the `b_{k-1}` and `b_{k-2}`
  bounds, and the excess `e ≥ 3` cases as an explicit hypothesis give `Ball(k+2,s)`.
* `step_e2_ball`: the same with `Ball(k,s)` in place of `BallSmall(k,s)` and the `b_{k-1}` bound.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRq4

variable {D : CH.Digraph} {W : Finset ℕ} {u j s : ℕ}

/-- **The count at `e = 2`.** -/
theorem count_two (hs : 4 ≤ s) (H : GSet D W u j s 2) (hbk1 : s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card) :
    (PP D W u j).card * (s - (KK D W u j).card - 1) + (PP D W u j).card ≤
        (ball D W u (j + 2) \ ball D W u (j + 1)).card + (ball D W u (j + 3) \ ball D W u (j + 2)).card ∧
      (2 ≤ (KK D W u j).card → (PP D W u j).card * (s - (KK D W u j).card) + (PP D W u j).card ≤
        (ball D W u (j + 2) \ ball D W u (j + 1)).card + (ball D W u (j + 3) \ ball D W u (j + 2)).card) ∧
      j + 6 ≤ 2 * (PP D W u j).card := by
  classical
  have C := c15_two hs H hbk1
  have hsum := sum_Zp_g C
  have hPN : (PP D W u j).card ≤ (ball D W u (j + 3) \ ball D W u (j + 2)).card := Finset.card_le_card PP_sub
  refine ⟨?_, fun hK2 => ?_, P_ge_s hs C⟩
  · have h1 : ∑ _p ∈ PP D W u j, (s - (KK D W u j).card - 1) ≤ ∑ p ∈ PP D W u j, (Zp D W u j p).card :=
      Finset.sum_le_sum (fun p hp => (Zp_bound_s C hp).1)
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h1
    omega
  · have h2 : ∑ _p ∈ PP D W u j, (s - (KK D W u j).card) ≤ ∑ p ∈ PP D W u j, (Zp D W u j p).card :=
      Finset.sum_le_sum (fun p hp => (Zp_bound_s C hp).2 hK2)
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h2
    omega

/-- `n_{k-1} + n_k + |K| ≤ 2s + 3` at `e = 2`, from `b_{k-2} ≥ s(k-2)+1`. -/
theorem upper_two (H : GSet D W u j s 2) (hbk2 : s * (j + 1) + 1 ≤ (ball D W u (j + 1)).card) :
    (ball D W u (j + 2) \ ball D W u (j + 1)).card + (ball D W u (j + 3) \ ball D W u (j + 2)).card +
      (KK D W u j).card ≤ 2 * s + 3 := by
  have e3 : (ball D W u (j + 3) \ ball D W u (j + 2)).card + (ball D W u (j + 2)).card =
      (ball D W u (j + 3)).card := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have e2 : (ball D W u (j + 2) \ ball D W u (j + 1)).card + (ball D W u (j + 1)).card =
      (ball D W u (j + 2)).card := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have eK : (KK D W u j).card + (ball D W u (j + 3)).card = (ball D W u (j + 4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hsj : s * (j + 3) = s * (j + 1) + s + s := by
    rw [show j + 3 = (j + 1) + 1 + 1 by omega, Nat.mul_add_one, Nat.mul_add_one]
  have := H.hb
  omega

/-- **Theorem Q5, every `s ≥ 5`.** At excess `e = 2` the setting is contradictory for `k ≥ 4`, and for `k = 3` once
`s ≥ 7`. -/
theorem thm_e2_core_s (hs : 5 ≤ s) (hj : 1 ≤ j ∨ 7 ≤ s) (H : GSet D W u j s 2)
    (hbk1 : s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card) (hbk2 : s * (j + 1) + 1 ≤ (ball D W u (j + 1)).card) :
    False := by
  obtain ⟨c1, c2, hP⟩ := count_two (by omega) H hbk1
  have hup := upper_two H hbk2
  have hK := H.hK
  have hP3 : 3 ≤ (PP D W u j).card := by omega
  have a3 := Nat.mul_le_mul_right (s - (KK D W u j).card - 1) hP3
  have b3 := Nat.mul_le_mul_right (s - (KK D W u j).card) hP3
  by_cases hj1 : 1 ≤ j
  · have hP4 : 4 ≤ (PP D W u j).card := by omega
    have a4 := Nat.mul_le_mul_right (s - (KK D W u j).card - 1) hP4
    have b4 := Nat.mul_le_mul_right (s - (KK D W u j).card) hP4
    by_cases hK2 : 2 ≤ (KK D W u j).card
    · have := c2 hK2; omega
    · omega
  · have hs7 : 7 ≤ s := by omega
    by_cases hK2 : 2 ≤ (KK D W u j).card
    · have := c2 hK2; omega
    · omega

/-- **Conditional step, `e = 2` for every `s ≥ 5`.** Level `k = j + 3` with `k ≥ 4`, or `k = 3` and `s ≥ 7`.
Hypotheses: `(Diam_k)` as `BallSmall(k,s)`; `Ball(k+1,s)`; the lower bounds `b_{k-1} ≥ s(k-1)+1` and
`b_{k-2} ≥ s(k-2)+1` on `(k+2)`-free out-`s` digraphs; and `hE3`, the unproved excess `e ≥ 3` cases
(`b_{k+1} ≥ sk+5` already gives `Ball(k+2,s)`). Conclusion: `Ball(k+2,s)`. -/
theorem step_e2_s (hs : 5 ≤ s) (hj : 1 ≤ j ∨ 7 ≤ s) (hS : BallSmall (j + 3) s) (hb4 : Ball (j + 4) s)
    (hbk1 : ∀ (D : CH.Digraph) (W : Finset ℕ) (u : ℕ), QFree D W (j + 5) → OutEq s D W → u ∈ W →
      s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card)
    (hbk2 : ∀ (D : CH.Digraph) (W : Finset ℕ) (u : ℕ), QFree D W (j + 5) → OutEq s D W → u ∈ W →
      s * (j + 1) + 1 ≤ (ball D W u (j + 1)).card)
    (hE3 : ∀ (D : CH.Digraph) (W : Finset ℕ) (u : ℕ), QFree D W (j + 5) → OutEq s D W → u ∈ W →
      s * (j + 3) + 5 ≤ (ball D W u (j + 4)).card → s * (j + 4) + 1 ≤ (ball D W u (j + 4)).card) :
    Ball (j + 5) s := by
  intro D W hfree hout u hu
  rw [show j + 5 - 1 = j + 4 by omega]
  have h1 := hbk1 D W u hfree hout hu
  have h6 := thm6_s (by omega) hS hb4 hfree hout hu h1
  by_cases h5 : s * (j + 3) + 5 ≤ (ball D W u (j + 4)).card
  · exact hE3 D W u hfree hout hu h5
  exfalso
  have hbk := bk_of_ball_s hb4 hfree hout hu
  have hb3 : (ball D W u (j + 3)).card ≤ s * (j + 3) + 3 := by
    by_contra h
    exact closed_case_s (by omega) hb4 hfree hout hu (by omega) (by omega)
  exact thm_e2_core_s hs hj ⟨hS, hfree, hout, hu, by omega, hbk, by omega⟩ h1 (hbk2 D W u hfree hout hu)

/-- `step_e2_s` with `Ball(k,s)` in place of `BallSmall(k,s)` and the `b_{k-1}` bound. -/
theorem step_e2_ball (hs : 5 ≤ s) (hj : 1 ≤ j ∨ 7 ≤ s) (hBk : Ball (j + 3) s) (hb4 : Ball (j + 4) s)
    (hbk2 : ∀ (D : CH.Digraph) (W : Finset ℕ) (u : ℕ), QFree D W (j + 5) → OutEq s D W → u ∈ W →
      s * (j + 1) + 1 ≤ (ball D W u (j + 1)).card)
    (hE3 : ∀ (D : CH.Digraph) (W : Finset ℕ) (u : ℕ), QFree D W (j + 5) → OutEq s D W → u ∈ W →
      s * (j + 3) + 5 ≤ (ball D W u (j + 4)).card → s * (j + 4) + 1 ≤ (ball D W u (j + 4)).card) :
    Ball (j + 5) s :=
  step_e2_s hs hj (ballSmall_of_ball hBk) hb4
    (fun D W u hfree hout hu => by
      have := hBk D W (hfree.mono_bound (by omega)) hout u hu
      rwa [show j + 3 - 1 = j + 2 by omega] at this)
    hbk2 hE3

end LeanCH.BR.BRsGen
