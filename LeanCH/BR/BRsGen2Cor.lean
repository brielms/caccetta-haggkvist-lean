import LeanCH.BR.BRsGen2Reach

/-!
# General `s`, excess `e = 2`: (Good_2), and Corollary 15 (4)–(6) (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §2 (Corollary 15), `BallQ5_attempt_subagent.md` §3 (Q4) and §6 ("(Good_2) is
proved for every `s`, with `x_2 = [c = 1]`"). The `s = 4` versions are in `BRq4Reach.lean`. No existing file is
changed.

* `allGood_two` (**(Good_2)**, any `s`): at `e = 2` every π-target not heading `K` is `GoodT` (Lemma 8 via `tri_s`).
* `c15_two`: `GSet s 2`, `4 ≤ s` and `b_{k-1} ≥ s(k-1)+1` give the Corollary 15 hypotheses `C15 s 2`. The `P_0` bound
  holds because `n_k ≤ s+3-|K|`: if `s ≥ |K|+3` the tournament count applies, otherwise `s ≤ 5` and `n_k ≤ 5 ≤ k+2`.
* `nonR0_s`, `Zp_bound_s` (**Corollary 15 (4), (6)**): `|Z_p| ≥ s-|K|-1`, and `≥ s-|K|` if `|K| ≥ 2`
  (exceptions `x_2 = [|K| = 1]`, from Lemma 9's corollary and Lemma 10).
* `Emin_s`, `P_ge_s` (**Corollary 15 (5)**, `4 ≤ s`): `2|P| ≥ k+3`.
* `sum_Zp_g` (**Corollary 15 (6)**, any `s`, any `e`): `Σ_{p ∈ P} |Z_p| ≤ n_{k-1}`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRq4

variable {D : CH.Digraph} {W : Finset ℕ} {u j s e : ℕ}

theorem GSet.hV2 (H : GSet D W u j s 2) : (VV D W u j).card = s * (j + 3) + 3 := by
  have := H.hV; omega

/-- **(Good_2)**, any `s`. -/
theorem allGood_two (H : GSet D W u j s 2) : AllGood D W u j := by
  intro p hp z hzW hpz hzK hzP
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  rcases tri_s H.hS H.hfree H.hout H.hu H.hV2 hp3 hp2 hpz hzW hzK with h | ⟨y, hy, -, hall, -⟩ | ⟨hM, -⟩
  · exact absurd h hzP
  · intro x hx hxB hxp; exact ball_step hy (VV_sub hx) (hall x hx hxB hxp)
  · intro x hx hxB hxp
    rcases (hM x hx).mp hxB with rfl | h'
    · exact absurd rfl hxp
    · exact h'.1

/-- `n_k + |K| ≤ s + 3` at `e = 2`, from `b_{k-1} ≥ s(k-1)+1`. -/
theorem nk_two (H : GSet D W u j s 2) (hbk1 : s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card) :
    (ball D W u (j + 3) \ ball D W u (j + 2)).card + (KK D W u j).card ≤ s + 3 := by
  have e3 : (ball D W u (j + 3) \ ball D W u (j + 2)).card + (ball D W u (j + 2)).card =
      (ball D W u (j + 3)).card := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have eK : (KK D W u j).card + (ball D W u (j + 3)).card = (ball D W u (j + 4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hsj : s * (j + 3) = s * (j + 2) + s := by rw [show j + 3 = (j + 2) + 1 by omega, Nat.mul_add_one]
  have := H.hb
  omega

/-- The Corollary 15 hypotheses at `e = 2`, `4 ≤ s`. -/
theorem c15_two (hs : 4 ≤ s) (H : GSet D W u j s 2) (hbk1 : s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card) :
    C15 D W u j s 2 := by
  have hK := H.hK
  have hn := nk_two H hbk1
  refine ⟨H, allGood_two H, by omega, ?_⟩
  by_cases h : (KK D W u j).card + 3 ≤ s
  · right; omega
  · left; omega

/-- Every π-target of a `P`-vertex that is not `R0` is `R2` (`e = 2`). -/
theorem R2_of_not_R0_s (C : C15 D W u j s 2) {p z : ℕ} (hp : p ∈ PP D W u j) (hpz : D p z = true) (hzW : z ∈ W)
    (hzK : z ∉ KK D W u j) (h0 : ¬ R0 D W u j p z) : R2 D W u j p z := by
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  have H := C.set
  rcases tri_s H.hS H.hfree H.hout H.hu H.hV2 hp3 hp2 hpz hzW hzK with h | h | h
  · exact absurd h (no_target_P_g C hp hpz hzW hzK)
  · exact h
  · exact absurd h h0

/-- **Corollary 15 (4)** (`e = 2`): non-`R0` π-targets, at least `s-|K|-1`, and at least `s-|K|` if `|K| ≥ 2`. -/
theorem nonR0_s (H : GSet D W u j s 2) {p : ℕ} (hp : p ∈ PP D W u j) :
    ∃ S ⊆ outN D W p \ KK D W u j, (∀ z ∈ S, ¬ R0 D W u j p z) ∧ s - (KK D W u j).card - 1 ≤ S.card ∧
      (2 ≤ (KK D W u j).card → s - (KK D W u j).card ≤ S.card) := by
  classical
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  have hpW : p ∈ W := ball_subset hp3
  have hT := Finset.le_card_sdiff (KK D W u j) (outN D W p)
  rw [H.hout p hpW] at hT
  have hK := H.hK
  have hzT : ∀ z ∈ outN D W p \ KK D W u j, z ∈ W ∧ D p z = true :=
    fun z hz => mem_outN.mp (Finset.mem_sdiff.mp hz).1
  have hBc : ∀ z, R0 D W u j p z → (BB D W u j z).card ≤ s * (j + 3) + 1 :=
    fun z hR => r0_card_s H.hu H.hV2 hp3 hp2 hR.1
  by_cases hK2 : 2 ≤ (KK D W u j).card
  · refine ⟨_, subset_rfl, fun z hz h0 => ?_, by omega, fun _ => by omega⟩
    have := r0_K_s H.hS H.hfree H.hout H.hu hp3 hp2 (hzT z hz).2 (hzT z hz).1 h0 (hBc z h0)
    omega
  · by_cases h0 : ∃ z0 ∈ outN D W p \ KK D W u j, R0 D W u j p z0
    · obtain ⟨z0, hz0, hR0⟩ := h0
      refine ⟨(outN D W p \ KK D W u j).erase z0, Finset.erase_subset _ _, fun z hz hR => ?_, ?_, fun h => absurd h hK2⟩
      · obtain ⟨hzz0, hz⟩ := Finset.mem_erase.mp hz
        exact two_R0_s H.hS H.hfree H.hout H.hu hp3 hp2 (hzT z hz).2 (hzT z hz).1 (hzT z0 hz0).2
          (hzT z0 hz0).1 hzz0 hR hR0 (hBc z hR)
      · rw [Finset.card_erase_of_mem hz0]; omega
    · push Not at h0
      exact ⟨_, subset_rfl, h0, by omega, fun h => absurd h hK2⟩

/-- **Corollary 15 (6), per vertex** (`e = 2`). -/
theorem Zp_bound_s (C : C15 D W u j s 2) {p : ℕ} (hp : p ∈ PP D W u j) :
    s - (KK D W u j).card - 1 ≤ (Zp D W u j p).card ∧
      (2 ≤ (KK D W u j).card → s - (KK D W u j).card ≤ (Zp D W u j p).card) := by
  obtain ⟨S, hS, h0, h1, h2⟩ := nonR0_s C.set hp
  have hsub : S ⊆ Zp D W u j p := by
    intro z hz
    obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp (hS hz)
    obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
    exact mem_outN.mpr ⟨(R2_facts hzW (R2_of_not_R0_s C hp hpz hzW hzK (h0 z hz))).1, hpz⟩
  have := Finset.card_le_card hsub
  exact ⟨by omega, fun h => by have := h2 h; omega⟩

/-- **Corollary 15 (4), successors** (`e = 2`, `4 ≤ s`). -/
theorem Emin_s (hs : 4 ≤ s) (C : C15 D W u j s 2) {p : ℕ} (hp : p ∈ PP D W u j) :
    ∃ z ∈ ball D W u (j + 2) \ ball D W u (j + 1), D p z = true ∧ ∃ w ∈ PP D W u j, D z w = true := by
  obtain ⟨S, hS, h0, h1, h2⟩ := nonR0_s C.set hp
  have hK := C.set.hK
  obtain ⟨z, hz⟩ : S.Nonempty := by
    rw [← Finset.card_pos]
    by_cases hK2 : 2 ≤ (KK D W u j).card
    · have := h2 hK2; omega
    · omega
  obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp (hS hz)
  obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
  obtain ⟨hzN, w, hwP, hzw⟩ := R2_facts hzW (R2_of_not_R0_s C hp hpz hzW hzK (h0 z hz))
  exact ⟨z, hzN, hpz, w, hwP, hzw⟩

theorem PP_ne_g (H : GSet D W u j s e) : (PP D W u j).Nonempty := by
  obtain ⟨c, hc⟩ : (KK D W u j).Nonempty := by rw [← Finset.card_pos]; have := H.hK; omega
  obtain ⟨hc4, hc3⟩ := Finset.mem_sdiff.mp hc
  obtain ⟨p, hp, hpc⟩ := ball_succ_pred H.hu hc4 hc3
  have hp1 : p ∉ ball D W u (j + 2) := fun h => hc3 (ball_step h (ball_subset hc4) hpc)
  exact ⟨p, mem_PP.mpr ⟨hp, hp1, c, hc, hpc⟩⟩

/-- **Corollary 15 (5)** (`e = 2`, `4 ≤ s`). `|P| ≥ ⌈(k+3)/2⌉`, i.e. `2|P| ≥ k+3`. -/
theorem P_ge_s (hs : 4 ≤ s) (C : C15 D W u j s 2) : j + 6 ≤ 2 * (PP D W u j).card := by
  classical
  have hNW : ball D W u (j + 2) \ ball D W u (j + 1) ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hE : QFree (two D (ball D W u (j + 2) \ ball D W u (j + 1))) (PP D W u j) ((j + 5) / 2) :=
    two_qfree hNW PP_W C.set.hfree (by omega)
  by_contra hlt
  obtain ⟨t, ht, hsink⟩ := exists_sink hE (PP_ne_g C.set) (by omega)
  obtain ⟨z, hz, htz, w, hwP, hzw⟩ := Emin_s hs C ht
  exact hsink w hwP (two_iff.mpr ⟨z, hz, htz, hzw⟩)

/-- **Corollary 15 (6)**, any `s` and `e`. `Σ_{p ∈ P} |Z_p| ≤ n_{k-1}`. -/
theorem sum_Zp_g (C : C15 D W u j s e) :
    ∑ p ∈ PP D W u j, (Zp D W u j p).card ≤ (ball D W u (j + 2) \ ball D W u (j + 1)).card := by
  classical
  have hdisj : ((PP D W u j : Finset ℕ) : Set ℕ).PairwiseDisjoint (Zp D W u j) := by
    intro p hp p' hp' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨hzN, hpz⟩ := mem_outN.mp hz
    obtain ⟨-, hp'z⟩ := mem_outN.mp hz'
    have hzK : z ∉ KK D W u j := fun h =>
      (Finset.mem_sdiff.mp h).2 (ball_mono_radius (by omega) (Finset.mem_sdiff.mp hzN).1)
    exact hne (disj_target_g C (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hp')
      (ball_subset (Finset.mem_sdiff.mp hzN).1) hzK hpz hp'z)
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun p _ => outN_subset))

end LeanCH.BR.BRsGen
