import LeanCH.BR.BRq4Reach

/-!
# Ball(q,4) route: Theorem 16, the step for every level `k ≥ 4` (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §3 (Theorem 16). Level `k = j + 3`.

* `tight_arc`: if `⇒` (the `R2` detour digraph on `P`) is `q`-free with `2q ≤ k+2` and `|P| ≤ q+1`, then a vertex
  `z ∈ N_{k-1}` with an in-neighbour in `P` has at most one out-neighbour in `P` (`unique_succ`).
* `low_out`: vertices of `B_{k-2}` have no arc into `N_k`.
* `thm16_core`: `(S_k)` with `k ≥ 4`, `b_{k-1} ≥ 4k-3` and `b_{k-2} ≥ 4k-7` is contradictory.
* `thm16` (**Theorem 16**): `k ≥ 4`, `Ball(k,4)`, `Ball(k+1,4)` and `b_{k-2} ≥ 4k-7` give `Ball(k+2,4)`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

variable {D : CH.Digraph} {W : Finset ℕ} {u j : ℕ}

theorem tight_arc (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) {q : ℕ}
    (hq : 1 ≤ q) (h2q : 2 * q ≤ j + 5) (hPq : (PP D W u j).card ≤ q + 1) {p z w w' : ℕ}
    (hp : p ∈ PP D W u j) (hz : z ∈ ball D W u (j + 2) \ ball D W u (j + 1)) (hpz : D p z = true)
    (hw : w ∈ PP D W u j) (hw' : w' ∈ PP D W u j) (hzw : D z w = true) (hzw' : D z w' = true) : w = w' := by
  have hNW : ball D W u (j + 2) \ ball D W u (j + 1) ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hE : QFree (two D (ball D W u (j + 2) \ ball D W u (j + 1))) (PP D W u j) q :=
    two_qfree hNW PP_W H.hfree h2q
  refine unique_succ hq hE hPq (fun t ht => ?_) hp hw hw' (two_iff.mpr ⟨z, hz, hpz, hzw⟩)
    (two_iff.mpr ⟨z, hz, hpz, hzw'⟩)
  obtain ⟨z, hz, htz, w, hwP, hzw⟩ := Emin H hnk ht
  exact ⟨w, hwP, two_iff.mpr ⟨z, hz, htz, hzw⟩⟩

/-- Out-neighbours of `v ∈ B_i` lie in `(B_i ∖ {u}) ∪ N_{i+1}` (no arc back to `u`). -/
theorem out_layer (H : Setting D W u j) {i v : ℕ} (hi : i + 1 ≤ j + 5) (hv : v ∈ ball D W u i) :
    ∀ b ∈ W, D v b = true → b ∈ (ball D W u i).erase u ∨ b ∈ ball D W u (i + 1) \ ball D W u i := by
  intro b hbW hvb
  by_cases hb : b ∈ ball D W u i
  · refine Or.inl (Finset.mem_erase.mpr ⟨?_, hb⟩)
    rintro rfl; exact no_back_arc H.hfree H.hu hv hi hvb
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨ball_step hv hbW hvb, hb⟩)

/-- A vertex of `B_{i-1}` has no arc into `N_{i+1}`. -/
theorem low_out {i v : ℕ} (hv : v ∈ ball D W u i) : outN D (ball D W u (i + 2) \ ball D W u (i + 1)) v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hb
  obtain ⟨hbN, hvb⟩ := mem_outN.mp hb
  exact (Finset.mem_sdiff.mp hbN).2 (ball_step hv (ball_subset (Finset.mem_sdiff.mp hbN).1) hvb)

theorem thm16_core (H : Setting D W u j) (hj : 1 ≤ j) (hbk1 : 4 * (j + 2) + 1 ≤ (ball D W u (j + 2)).card)
    (hbk2 : 4 * (j + 1) + 1 ≤ (ball D W u (j + 1)).card) : False := by
  classical
  have e3 : (ball D W u (j + 3) \ ball D W u (j + 2)).card + (ball D W u (j + 2)).card = (ball D W u (j + 3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have e2 : (ball D W u (j + 2) \ ball D W u (j + 1)).card + (ball D W u (j + 1)).card = (ball D W u (j + 2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have eK : (KK D W u j).card + (ball D W u (j + 3)).card = (ball D W u (j + 4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hb := H.hb
  have hbk := H.hbk
  have hb3 := H.hb3
  have hK := H.hK
  have hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5 := by omega
  have hP := P_ge H hnk
  have hPN : (PP D W u j).card ≤ (ball D W u (j + 3) \ ball D W u (j + 2)).card := Finset.card_le_card PP_sub
  have hsum := sum_Zp H hnk
  by_cases hK2 : (KK D W u j).card ≤ 2
  · -- `|K| ≤ 2`: `n_{k-1} + n_k ≥ 3|P| ≥ 12 > 11 - |K|`
    have h2 : ∑ _p ∈ PP D W u j, 2 ≤ ∑ p ∈ PP D W u j, (Zp D W u j p).card :=
      Finset.sum_le_sum (fun p hp => (Zp_bound H hnk hp).2 hK2)
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h2
    omega
  · -- `|K| = 3`: everything is tight
    have h1 : ∑ _p ∈ PP D W u j, 1 ≤ ∑ p ∈ PP D W u j, (Zp D W u j p).card :=
      Finset.sum_le_sum (fun p hp => (Zp_bound H hnk hp).1)
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h1
    have hPeq : PP D W u j = ball D W u (j + 3) \ ball D W u (j + 2) :=
      Finset.eq_of_subset_of_card_le PP_sub (by omega)
    have hj2 : j ≤ 2 := by omega
    -- every `z ∈ N_{k-1}` is a detour of some `p ∈ P`
    have hdisj : ((PP D W u j : Finset ℕ) : Set ℕ).PairwiseDisjoint (Zp D W u j) := by
      intro p hp p' hp' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨hzN, hpz⟩ := mem_outN.mp hz
      obtain ⟨-, hp'z⟩ := mem_outN.mp hz'
      have hzK : z ∉ KK D W u j := fun h =>
        (Finset.mem_sdiff.mp h).2 (ball_mono_radius (by omega) (Finset.mem_sdiff.mp hzN).1)
      exact hne (disj_target H hnk (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hp')
        (ball_subset (Finset.mem_sdiff.mp hzN).1) hzK hpz hp'z)
    have hcov : (PP D W u j).biUnion (Zp D W u j) = ball D W u (j + 2) \ ball D W u (j + 1) := by
      refine Finset.eq_of_subset_of_card_le (Finset.biUnion_subset.mpr (fun p _ => outN_subset)) ?_
      rw [Finset.card_biUnion hdisj]
      omega
    have harc : ∀ z ∈ ball D W u (j + 2) \ ball D W u (j + 1),
        (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) z).card ≤ 1 := by
      intro z hz
      rw [← hcov] at hz
      obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hzN, hpz⟩ := mem_outN.mp hzp
      rw [← hPeq]
      refine Finset.card_le_one.mpr (fun w hw w' hw' => ?_)
      exact tight_arc H hnk (q := 3) (by omega) (by omega) (by omega) hp hzN hpz (mem_outN.mp hw).1
        (mem_outN.mp hw').1 (mem_outN.mp hw).2 (mem_outN.mp hw').2
    -- `D[B_{k-1} ∖ {u}]` has min out `≥ 3`; CH(3) at `q = k+2`
    have hUW : (ball D W u (j + 2)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hmin : ∀ v ∈ (ball D W u (j + 2)).erase u, 3 ≤ (outN D ((ball D W u (j + 2)).erase u) v).card := by
      intro v hv
      have hv2 := Finset.mem_of_mem_erase hv
      have hs := out_split (S := ball D W u (j + 3) \ ball D W u (j + 2)) (out_layer H (by omega) hv2)
      rw [H.hout v (hUW hv)] at hs
      have : (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) v).card ≤ 1 := by
        by_cases hv1 : v ∈ ball D W u (j + 1)
        · rw [low_out hv1]; simp
        · exact harc v (Finset.mem_sdiff.mpr ⟨hv2, hv1⟩)
      omega
    have hU := ch3_set (q := j + 5) (by omega) (H.hfree.mono_set hUW) hmin
      (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (self_mem_ball H.hu)]; omega))
    rw [Finset.card_erase_of_mem (self_mem_ball H.hu)] at hU
    omega

/-- **Theorem 16.** For `k = j + 3 ≥ 4`: `Ball(k,4)`, `Ball(k+1,4)` and `b_{k-2} ≥ 4k-7` (in `(k+2)`-free out-4
digraphs) give `Ball(k+2,4)`. -/
theorem thm16 (hj : 1 ≤ j) (hBk : Ball (j + 3) 4) (hb4 : Ball (j + 4) 4)
    (hbk2 : ∀ (D : CH.Digraph) (W : Finset ℕ) (u : ℕ), QFree D W (j + 5) → OutEq 4 D W → u ∈ W →
      4 * (j + 1) + 1 ≤ (ball D W u (j + 1)).card) : Ball (j + 5) 4 := by
  intro D W hfree hout u hu
  rw [show j + 5 - 1 = j + 4 by omega]
  by_contra hlt
  have hS := ballSmall_of_ball hBk
  have hbk1 : 4 * (j + 2) + 1 ≤ (ball D W u (j + 2)).card := by
    have := hBk D W (hfree.mono_bound (by omega)) hout u hu
    rwa [show j + 3 - 1 = j + 2 by omega] at this
  have h6 := thm6 hS hb4 hfree hout hu hbk1
  have hbk := bk_of_ball hb4 hfree hout hu
  have hb3 : (ball D W u (j + 3)).card ≤ 4 * (j + 3) + 3 := by
    by_contra h
    exact closed_case hb4 hfree hout hu (by omega) (by omega)
  exact thm16_core ⟨hS, hfree, hout, hu, by omega, hbk, hb3⟩ hj hbk1 (hbk2 D W u hfree hout hu)

end LeanCH.BR.BRq4
