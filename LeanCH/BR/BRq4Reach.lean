import LeanCH.BR.BRq4Twin

/-!
# Ball(q,4) route: Lemma 14 (π-target reach) and Corollary 15 (structure of `P`) (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §2 (Claim 0, Lemma 14, Corollary 15). Level `k = j + 3`.

* `Setting D W u j` (the paper's `(S_k)` with `(Diam_k)`): `BallSmall k 4`, `D` `(k+2)`-free and out-4,
  `b_{k+1} = 4k+4`, `4k+1 ≤ b_k ≤ 4k+3` (so `1 ≤ |K| ≤ 3`).
* `reach` (**Lemma 14 (c), (d)**, via (a), (b) and Claim 0): for a π-target `z ∉ P` of `p`, no vertex of
  `N_k ∪ K` points to `p`, and `p` is the only in-neighbour of `z` in `N_k ∪ K`.
* `no_inP`, `no_target_P`, `disj_target` (**Corollary 15 (1)–(3)**, under `n_k ≤ k+2`).
* `nonR0`, `Zp_bound`, `Emin`, `allR2`, `P_ge`, `sum_Zp` (**Corollary 15 (4)–(6)**).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

/-- The setting `(S_k)`, level `k = j + 3`. -/
structure Setting (D : CH.Digraph) (W : Finset ℕ) (u j : ℕ) : Prop where
  hS : BallSmall (j + 3) 4
  hfree : QFree D W (j + 5)
  hout : OutEq 4 D W
  hu : u ∈ W
  hb : (ball D W u (j + 4)).card = 4 * (j + 3) + 4
  hbk : 4 * (j + 3) + 1 ≤ (ball D W u (j + 3)).card
  hb3 : (ball D W u (j + 3)).card ≤ 4 * (j + 3) + 3

/-- `P = {p ∈ N_k : p → K}`. -/
noncomputable def PP (D : CH.Digraph) (W : Finset ℕ) (u j : ℕ) : Finset ℕ :=
  (ball D W u (j + 3) \ ball D W u (j + 2)).filter (fun p => (outN D (KK D W u j) p).Nonempty)

/-- `Z_p`: the out-neighbours of `p` in `N_{k-1}`. -/
noncomputable def Zp (D : CH.Digraph) (W : Finset ℕ) (u j p : ℕ) : Finset ℕ :=
  outN D (ball D W u (j + 2) \ ball D W u (j + 1)) p

variable {D : CH.Digraph} {W : Finset ℕ} {u j : ℕ}

namespace Setting

variable (H : Setting D W u j)
include H

theorem hV : (VV D W u j).card = 4 * (j + 3) + 3 := by
  rw [Finset.card_erase_of_mem (self_mem_ball H.hu), H.hb]; omega

theorem hK : 1 ≤ (KK D W u j).card ∧ (KK D W u j).card ≤ 3 := by
  have e := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := D) (W := W) (u := u) (by omega : j + 3 ≤ j + 4))
  have := H.hb; have := H.hbk; have := H.hb3
  simp only [KK]
  omega

end Setting

theorem mem_PP {p : ℕ} : p ∈ PP D W u j ↔
    p ∈ ball D W u (j + 3) ∧ p ∉ ball D W u (j + 2) ∧ ∃ c ∈ KK D W u j, D p c = true := by
  unfold PP
  rw [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨h1, h2⟩, c, hc⟩; exact ⟨h1, h2, c, (mem_outN.mp hc).1, (mem_outN.mp hc).2⟩
  · rintro ⟨h1, h2, c, hc, hpc⟩; exact ⟨⟨h1, h2⟩, c, mem_outN.mpr ⟨hc, hpc⟩⟩

theorem PP_sub : PP D W u j ⊆ ball D W u (j + 3) \ ball D W u (j + 2) := Finset.filter_subset _ _

theorem PP_W : PP D W u j ⊆ W := fun _ hp => ball_subset (mem_PP.mp hp).1

/-- A vertex of `V ∖ K` heading `K` lies in `P`. -/
theorem memPP_of {z : ℕ} (hzV : z ∈ VV D W u j) (hzK : z ∉ KK D W u j) (h : ∃ c ∈ KK D W u j, D z c = true) :
    z ∈ PP D W u j := by
  obtain ⟨c, hc, hzc⟩ := h
  refine mem_PP.mpr ⟨mem_ball_of_V hzV hzK, fun h2 => ?_, c, hc, hzc⟩
  exact (Finset.mem_sdiff.mp hc).2 (ball_step h2 (ball_subset (Finset.mem_sdiff.mp hc).1) hzc)

/-- `R2` facts: `z ∈ N_{k-1}` and `z → w ∈ P`. -/
theorem R2_facts {p z : ℕ} (hzW : z ∈ W) (h : R2 D W u j p z) :
    z ∈ ball D W u (j + 2) \ ball D W u (j + 1) ∧ ∃ w ∈ PP D W u j, D z w = true := by
  obtain ⟨y, hy, hyz, -, w, hwV, hwK, hzw, c, hc, hwc⟩ := h
  have hwP := memPP_of hwV hwK ⟨c, hc, hwc⟩
  refine ⟨Finset.mem_sdiff.mpr ⟨ball_step hy hzW hyz, fun h1 => ?_⟩, w, hwP, hzw⟩
  exact (mem_PP.mp hwP).2.1 (ball_step h1 (VV_sub hwV) hzw)

/-- **Lemma 14 (c), (d).** -/
theorem reach (H : Setting D W u j) {p z : ℕ} (hp : p ∈ ball D W u (j + 3)) (hp1 : p ∉ ball D W u (j + 2))
    (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j) (hzP : ¬ ∃ c ∈ KK D W u j, D z c = true) :
    (∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → ¬ D x p = true) ∧
      (∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → x ≠ p → ¬ D x z = true) := by
  have hfree := H.hfree
  have hu := H.hu
  -- (a): `M ∖ {p}` lies below depth `k`
  have hM : ∀ x ∈ VV D W u j, x ∉ BB D W u j z → x ≠ p → x ∈ ball D W u (j + 2) := by
    rcases tri H.hS hfree H.hout hu H.hV hp hp1 hpz hzW hzK with h | ⟨y, hy, -, hall, -⟩ | ⟨hM, -⟩
    · exact absurd h hzP
    · intro x hx hxB hxp; exact ball_step hy (VV_sub hx) (hall x hx hxB hxp)
    · intro x hx hxB hxp
      rcases (hM x hx).mp hxB with rfl | h'
      · exact absurd rfl hxp
      · exact h'.1
  -- (b) and Claim 0
  have hreach : ∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → x ≠ p → ∃ m ≤ j + 3, Walk D W z x m := by
    intro x hx hx2 hxp
    have hxV : x ∈ VV D W u j := memV_of hu hx hx2
    have hxB : x ∈ BB D W u j z := by by_contra h; exact hx2 (hM x hxV h hxp)
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hxB
    rcases fold_walk hzK w with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
    · exact ⟨m, hm, h⟩
    · exact absurd (mem_ball_of_walk w2 (by omega) (VV_sub hxV)) hx2
  refine ⟨fun x hx hx2 hxp => ?_, fun x hx hx2 hxp' hxz => ?_⟩
  · -- (c)
    have hxp' : x ≠ p := by rintro rfl; exact loopfree hfree (by omega) (ball_subset hp) hxp
    obtain ⟨m, hm, w⟩ := hreach x hx hx2 hxp'
    exact hfree z (m + 1 + 1) (by omega) (by omega) ((w.snoc (ball_subset hp) hxp).snoc hzW hpz)
  · -- (d)
    obtain ⟨m, hm, w⟩ := hreach x hx hx2 hxp'
    exact hfree z (m + 1) (by omega) (by omega) (w.snoc hzW hxz)

/-- Every `p ∈ W` has an out-neighbour outside `K`. -/
theorem exists_target (H : Setting D W u j) {p : ℕ} (hpW : p ∈ W) :
    ∃ z ∈ W, D p z = true ∧ z ∉ KK D W u j := by
  have h1 := Finset.le_card_sdiff (KK D W u j) (outN D W p)
  rw [H.hout p hpW] at h1
  have := H.hK
  obtain ⟨z, hz⟩ : (outN D W p \ KK D W u j).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp hz
  exact ⟨z, (mem_outN.mp hz1).1, (mem_outN.mp hz1).2, hzK⟩

/-- **Corollary 15, the `P_0` step.** Under `n_k ≤ k+2`, every `p ∈ P` has a π-target outside `P`. -/
theorem target_out (H : Setting D W u j)
    (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) {p : ℕ} (hp : p ∈ PP D W u j) :
    ∃ z ∈ W, D p z = true ∧ z ∉ KK D W u j ∧ ¬ ∃ c ∈ KK D W u j, D z c = true := by
  classical
  by_contra hcon
  set P0 := (PP D W u j).filter (fun t => ∀ z ∈ outN D W t, z ∉ KK D W u j → ∃ c ∈ KK D W u j, D z c = true)
    with hP0
  have hmem0 : ∀ t ∈ PP D W u j, (∀ z ∈ W, D t z = true → z ∉ KK D W u j → ∃ c ∈ KK D W u j, D z c = true) →
      t ∈ P0 := fun t ht h => Finset.mem_filter.mpr ⟨ht, fun z hz hzK => h z (mem_outN.mp hz).1 (mem_outN.mp hz).2 hzK⟩
  have hpP0 : p ∈ P0 := hmem0 p hp (fun z hzW hpz hzK => by
    by_contra h; exact hcon ⟨z, hzW, hpz, hzK, h⟩)
  have hP0W : P0 ⊆ W := (Finset.filter_subset _ _).trans PP_W
  have hstep : ∀ t ∈ P0, ∃ t' ∈ P0, D t t' = true := by
    intro t ht
    obtain ⟨htP, hall⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht3, ht2, -⟩ := mem_PP.mp htP
    obtain ⟨z, hzW, htz, hzK⟩ := exists_target H (ball_subset ht3)
    have hzc := hall z (mem_outN.mpr ⟨hzW, htz⟩) hzK
    have hzP := memPP_of (toV H.hfree H.hu ht3 htz hzW) hzK hzc
    refine ⟨z, hmem0 z hzP (fun z' hz'W hzz' hz'K => ?_), htz⟩
    by_contra h
    obtain ⟨hz3, hz2, -⟩ := mem_PP.mp hzP
    exact (reach H hz3 hz2 hzz' hz'W hz'K h).1 t (ball_mono_radius (by omega) ht3) ht2 htz
  have hcard : P0.card ≤ j + 5 :=
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_card PP_sub)).trans hnk
  obtain ⟨t, ht, hsink⟩ := exists_sink ((H.hfree).mono_set hP0W) ⟨p, hpP0⟩ hcard
  obtain ⟨t', ht', htt'⟩ := hstep t ht
  exact hsink t' ht' htt'

/-- **Corollary 15 (2).** No vertex of `N_k ∪ K` points into `P`. -/
theorem no_inP (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) {p : ℕ}
    (hp : p ∈ PP D W u j) : ∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → ¬ D x p = true := by
  obtain ⟨z, hzW, hpz, hzK, hzP⟩ := target_out H hnk hp
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  exact (reach H hp3 hp2 hpz hzW hzK hzP).1

/-- **Corollary 15 (1).** No π-target of a `P`-vertex lies in `P`. -/
theorem no_target_P (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5)
    {p z : ℕ} (hp : p ∈ PP D W u j) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j) :
    ¬ ∃ c ∈ KK D W u j, D z c = true := by
  intro h
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  have hzP := memPP_of (toV H.hfree H.hu hp3 hpz hzW) hzK h
  exact no_inP H hnk hzP p (ball_mono_radius (by omega) hp3) hp2 hpz

/-- **Corollary 15 (3).** Distinct `P`-vertices have disjoint π-targets. -/
theorem disj_target (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5)
    {p p' z : ℕ} (hp : p ∈ PP D W u j) (hp' : p' ∈ PP D W u j) (hzW : z ∈ W) (hzK : z ∉ KK D W u j)
    (hpz : D p z = true) (hp'z : D p' z = true) : p = p' := by
  by_contra hne
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  obtain ⟨hp'3, hp'2, -⟩ := mem_PP.mp hp'
  exact (reach H hp3 hp2 hpz hzW hzK (no_target_P H hnk hp hpz hzW hzK)).2 p'
    (ball_mono_radius (by omega) hp'3) hp'2 (Ne.symm hne) hp'z

/-- Every π-target of a `P`-vertex that is not `R0` is `R2`. -/
theorem R2_of_not_R0 (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5)
    {p z : ℕ} (hp : p ∈ PP D W u j) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j)
    (h0 : ¬ R0 D W u j p z) : R2 D W u j p z := by
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  rcases tri H.hS H.hfree H.hout H.hu H.hV hp3 hp2 hpz hzW hzK with h | h | h
  · exact absurd h (no_target_P H hnk hp hpz hzW hzK)
  · exact h
  · exact absurd h h0

/-- **Corollary 15 (4).** A set of non-`R0` π-targets: at least one, at least two if `|K| ≤ 2`
(Corollary of Lemma 9 for `|K| ≥ 2`; Lemma 10 for `|K| = 1`). -/
theorem nonR0 (H : Setting D W u j) {p : ℕ} (hp : p ∈ PP D W u j) :
    ∃ S ⊆ outN D W p \ KK D W u j, (∀ z ∈ S, ¬ R0 D W u j p z) ∧ 1 ≤ S.card ∧
      ((KK D W u j).card ≤ 2 → 2 ≤ S.card) := by
  classical
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  have hpW : p ∈ W := ball_subset hp3
  have hT := Finset.le_card_sdiff (KK D W u j) (outN D W p)
  rw [H.hout p hpW] at hT
  have hK := H.hK
  have hzT : ∀ z ∈ outN D W p \ KK D W u j, z ∈ W ∧ D p z = true :=
    fun z hz => mem_outN.mp (Finset.mem_sdiff.mp hz).1
  by_cases hK2 : 2 ≤ (KK D W u j).card
  · refine ⟨_, subset_rfl, fun z hz h0 => ?_, by omega, fun _ => by omega⟩
    have := r0_K H.hS H.hfree H.hout H.hu H.hV hp3 hp2 (hzT z hz).2 (hzT z hz).1 h0
    omega
  · by_cases h0 : ∃ z0 ∈ outN D W p \ KK D W u j, R0 D W u j p z0
    · obtain ⟨z0, hz0, hR0⟩ := h0
      refine ⟨(outN D W p \ KK D W u j).erase z0, Finset.erase_subset _ _, fun z hz hR => ?_, ?_, fun _ => ?_⟩
      · obtain ⟨hzz0, hz⟩ := Finset.mem_erase.mp hz
        exact two_R0 H.hS H.hfree H.hout H.hu H.hV hp3 hp2 (hzT z hz).2 (hzT z hz).1 (hzT z0 hz0).2
          (hzT z0 hz0).1 hzz0 hR hR0
      · rw [Finset.card_erase_of_mem hz0]; omega
      · rw [Finset.card_erase_of_mem hz0]; omega
    · push Not at h0
      exact ⟨_, subset_rfl, h0, by omega, fun _ => by omega⟩

/-- **Corollary 15 (6), per vertex.** `|Z_p| ≥ 1`, and `≥ 2` if `|K| ≤ 2`. -/
theorem Zp_bound (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) {p : ℕ}
    (hp : p ∈ PP D W u j) : 1 ≤ (Zp D W u j p).card ∧ ((KK D W u j).card ≤ 2 → 2 ≤ (Zp D W u j p).card) := by
  obtain ⟨S, hS, h0, h1, h2⟩ := nonR0 H hp
  have hsub : S ⊆ Zp D W u j p := by
    intro z hz
    obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp (hS hz)
    obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
    exact mem_outN.mpr ⟨(R2_facts hzW (R2_of_not_R0 H hnk hp hpz hzW hzK (h0 z hz))).1, hpz⟩
  have := Finset.card_le_card hsub
  exact ⟨by omega, fun h => by have := h2 h; omega⟩

/-- **Corollary 15 (4), successors.** Every `p ∈ P` has an `R2` detour `p → z → w` with `z ∈ N_{k-1}`, `w ∈ P`. -/
theorem Emin (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) {p : ℕ}
    (hp : p ∈ PP D W u j) :
    ∃ z ∈ ball D W u (j + 2) \ ball D W u (j + 1), D p z = true ∧ ∃ w ∈ PP D W u j, D z w = true := by
  obtain ⟨S, hS, h0, h1, -⟩ := nonR0 H hp
  obtain ⟨z, hz⟩ : S.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp (hS hz)
  obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
  obtain ⟨hzN, w, hwP, hzw⟩ := R2_facts hzW (R2_of_not_R0 H hnk hp hpz hzW hzK (h0 z hz))
  exact ⟨z, hzN, hpz, w, hwP, hzw⟩

/-- **Corollary 15 (4), `|K| ≥ 2`.** Every π-target is `R2`. -/
theorem allR2 (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5)
    (hK2 : 2 ≤ (KK D W u j).card) {p z : ℕ} (hp : p ∈ PP D W u j) (hpz : D p z = true) (hzW : z ∈ W)
    (hzK : z ∉ KK D W u j) :
    z ∈ ball D W u (j + 2) \ ball D W u (j + 1) ∧ ∃ w ∈ PP D W u j, D z w = true := by
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  refine R2_facts hzW (R2_of_not_R0 H hnk hp hpz hzW hzK (fun h0 => ?_))
  have := r0_K H.hS H.hfree H.hout H.hu H.hV hp3 hp2 hpz hzW h0
  omega

theorem PP_ne (H : Setting D W u j) : (PP D W u j).Nonempty := by
  obtain ⟨c, hc⟩ : (KK D W u j).Nonempty := by rw [← Finset.card_pos]; have := H.hK; omega
  obtain ⟨hc4, hc3⟩ := Finset.mem_sdiff.mp hc
  obtain ⟨p, hp, hpc⟩ := ball_succ_pred H.hu hc4 hc3
  have hp1 : p ∉ ball D W u (j + 2) := fun h => hc3 (ball_step h (ball_subset hc4) hpc)
  exact ⟨p, mem_PP.mpr ⟨hp, hp1, c, hc, hpc⟩⟩

/-- **Corollary 15 (5).** `|P| ≥ ⌈(k+3)/2⌉`, i.e. `2|P| ≥ k+3`. -/
theorem P_ge (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) :
    j + 6 ≤ 2 * (PP D W u j).card := by
  classical
  have hNW : ball D W u (j + 2) \ ball D W u (j + 1) ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hE : QFree (two D (ball D W u (j + 2) \ ball D W u (j + 1))) (PP D W u j) ((j + 5) / 2) :=
    two_qfree hNW PP_W H.hfree (by omega)
  by_contra hlt
  obtain ⟨t, ht, hsink⟩ := exists_sink hE (PP_ne H) (by omega)
  obtain ⟨z, hz, htz, w, hwP, hzw⟩ := Emin H hnk ht
  exact hsink w hwP (two_iff.mpr ⟨z, hz, htz, hzw⟩)

/-- **Corollary 15 (6).** `Σ_{p ∈ P} |Z_p| ≤ n_{k-1}`. -/
theorem sum_Zp (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) :
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
    exact hne (disj_target H hnk (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hp')
      (ball_subset (Finset.mem_sdiff.mp hzN).1) hzK hpz hp'z)
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun p _ => outN_subset))

end LeanCH.BR.BRq4
