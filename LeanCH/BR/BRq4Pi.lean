import LeanCH.BR.BRq4Fold

/-!
# Ball(q,4) route: the π-step, Lemma 5_s, Theorem 6_s and the trichotomy Lemma 8 (Lean 4.35.0)

Paper: `Route1_GeneralS_subagent.md` §2 (Lemma 5_s, Lemma 7, Theorem 6_s) and `BallQ4_attempt_subagent.md` §3
(Lemma 8), at out-degree `s = 4`. Level `k = j + 3 ≥ 3`; `D` is `(k+2)`-free with out-degree four on `W`.

* `pi_not_mem` (π-step): `p ∉ B^F_k(z)` for `p ∈ N_k`, `p → z`, `z ∉ K`.
* `stepA` (Case A′): a parent `a ∈ A_p` inside `B^F_k(z)` forces `z → K`.
* `stepExit` (cases (a), (b), (c) of Lemma 8): an exit vertex `y ∈ B^F_k(z)` with `|exitN y| ≥ |M|` forces `z → K`,
  or `p ∉ exitN y` and the residual `R2`.
* `pi_P6` (**Lemma 5_s**): if `|V♮| ≤ 4k+2`, every π-target lies in `P`.
* `thm6` (**Theorem 6_s**, `s = 4`): `BallSmall k 4`, `Ball(k+1,4)`, `b_{k-1} ≥ 4k-3` give `b_{k+1} ≥ 4k+4`.
* `tri` (**Lemma 8**): if `|V♮| = 4k+3`, a π-target is in `P`, or `R2`, or `R0`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

variable {D : CH.Digraph} {W : Finset ℕ} {u j : ℕ}

/-- `x ∈ A_p`: an in-neighbour of `p` in `N_{k-1}`. -/
def Ap (D : CH.Digraph) (W : Finset ℕ) (u j p x : ℕ) : Prop :=
  x ∈ ball D W u (j + 2) ∧ x ∉ ball D W u (j + 1) ∧ D x p = true

/-- Residual `R2`: a witness `y ∈ B_{k-2}` with `y → z` and `y → M ∖ {p}`, and `z → w → K` with `w ∈ V ∖ K`. -/
def R2 (D : CH.Digraph) (W : Finset ℕ) (u j p z : ℕ) : Prop :=
  ∃ y ∈ ball D W u (j + 1), D y z = true ∧
    (∀ x ∈ VV D W u j, x ∉ BB D W u j z → x ≠ p → D y x = true) ∧
    ∃ w ∈ VV D W u j, w ∉ KK D W u j ∧ D z w = true ∧ ∃ c ∈ KK D W u j, D w c = true

/-- Residual `R0`: `M = {p} ∪ A_p` and every vertex of `B^F_k(z)` has at most one arc to `z` or out of the ball. -/
def R0 (D : CH.Digraph) (W : Finset ℕ) (u j p z : ℕ) : Prop :=
  (∀ x ∈ VV D W u j, x ∉ BB D W u j z ↔ (x = p ∨ Ap D W u j p x)) ∧
    ∀ y ∈ BB D W u j z, (exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y).card ≤ 1

theorem exists_Ap (hu : u ∈ W) {p : ℕ} (hp : p ∈ ball D W u (j + 3)) (hp1 : p ∉ ball D W u (j + 2)) :
    ∃ a, Ap D W u j p a := by
  obtain ⟨a, ha, hap⟩ := ball_succ_pred hu hp hp1
  exact ⟨a, ha, fun h => hp1 (ball_step h (ball_subset hp) hap), hap⟩

theorem Ap_V (hu : u ∈ W) {p a : ℕ} (ha : Ap D W u j p a) : a ∈ VV D W u j :=
  memV_of hu (ball_mono_radius (by omega) ha.1) ha.2.1

theorem pV_of (hu : u ∈ W) {p : ℕ} (hp : p ∈ ball D W u (j + 3)) (hp1 : p ∉ ball D W u (j + 2)) :
    p ∈ VV D W u j :=
  memV_of hu (ball_mono_radius (by omega) hp) hp1

/-- **π-step.** -/
theorem pi_not_mem (hfree : QFree D W (j + 5)) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j) :
    p ∉ BB D W u j z := by
  intro hpb
  obtain ⟨_, m, hm, w⟩ := mem_ball.mp hpb
  rcases fold_walk hzK w with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
  · exact hfree z (m + 1) (by omega) (by omega) (h.snoc hzW hpz)
  · exact hp1 (mem_ball_of_walk w2 (by omega) (ball_subset hp))

/-- **Case A′.** -/
theorem stepA (hfree : QFree D W (j + 5)) {p z a : ℕ} (hp : p ∈ ball D W u (j + 3)) (hpz : D p z = true)
    (hzW : z ∈ W) (hzK : z ∉ KK D W u j) (ha : Ap D W u j p a) (haB : a ∈ BB D W u j z) :
    ∃ c ∈ KK D W u j, D z c = true := by
  obtain ⟨_, m, hm, w⟩ := mem_ball.mp haB
  rcases fold_walk hzK w with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
  · exact absurd ((h.snoc (ball_subset hp) ha.2.2).snoc hzW hpz) (hfree z (m + 1 + 1) (by omega) (by omega))
  · have hm2 : j + 2 ≤ m2 := by
      by_contra hlt
      exact ha.2.1 (mem_ball_of_walk w2 (by omega) (ball_subset ha.1))
    obtain rfl : m1 = 1 := by omega
    exact ⟨c, hc, fold_one hzK w1⟩

theorem exitN_sub {z y : ℕ} :
    exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y ⊆ insert z (VV D W u j \ BB D W u j z) := by
  intro b hb
  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
  rcases hb2 with rfl | hb2
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨(mem_outN.mp hb1).1, hb2⟩)

theorem exitN_arc {z y b : ℕ} (hb : b ∈ exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y) :
    FF D W u j y b = true :=
  (mem_outN.mp (Finset.mem_filter.mp hb).1).2

/-- An `F`-arc `y → b` with `b ∉ B_1` starts outside `K`, so it is a `D`-arc. -/
theorem notK_of_arc {y b : ℕ} (hbW : b ∈ W) (hb : b ∉ ball D W u 1) (h : FF D W u j y b = true) :
    y ∉ KK D W u j ∧ D y b = true := by
  by_cases hyK : y ∈ KK D W u j
  · rw [FF_of_mem hyK] at h
    exact absurd (ball_of_adj hbW h) hb
  · rw [FF_of_not_mem hyK] at h
    exact ⟨hyK, h⟩

/-- **Lemma 8, cases (a), (b), (c).** -/
theorem stepExit (hfree : QFree D W (j + 5)) (hu : u ∈ W) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j)
    (hA : ∀ a, Ap D W u j p a → a ∉ BB D W u j z) {y : ℕ} (hy : y ∈ BB D W u j z)
    (hcard : (VV D W u j \ BB D W u j z).card ≤ (exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y).card) :
    (∃ c ∈ KK D W u j, D z c = true) ∨
      (p ∉ exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y ∧ R2 D W u j p z) := by
  classical
  have hzV : z ∈ VV D W u j := toV hfree hu hp hpz hzW
  have hpV : p ∈ VV D W u j := pV_of hu hp hp1
  have hpW : p ∈ W := ball_subset hp
  have hzB : z ∈ BB D W u j z := self_mem_ball hzV
  have hpM : p ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨hpV, pi_not_mem hfree hp hp1 hpz hzW hzK⟩
  have hyV : y ∈ VV D W u j := ball_subset hy
  have hyW : y ∈ W := VV_sub hyV
  have hp1' : p ∉ ball D W u 1 := fun h => hp1 (ball_mono_radius (by omega) h)
  obtain ⟨_, m, hm, wzy⟩ := mem_ball.mp hy
  by_cases hzE : z ∈ exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y
  · by_cases hpE : p ∈ exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y
    · -- (b): `y → z`, `y → p`
      obtain ⟨hyK, hyp⟩ := notK_of_arc hpW hp1' (exitN_arc hpE)
      have hyz : D y z = true := by have := exitN_arc hzE; rwa [FF_of_not_mem hyK] at this
      rcases fold_walk hzK wzy with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
      · exact absurd (h.snoc hzW hyz) (hfree z (m + 1) (by omega) (by omega))
      · have hm2 : j + 2 ≤ m2 := by
          by_contra hlt
          exact hp1 (ball_step (mem_ball_of_walk w2 (by omega) hyW) hpW hyp)
        obtain rfl : m1 = 1 := by omega
        exact Or.inl ⟨c, hc, fold_one hzK w1⟩
    · -- (c): `y → z`, `y ↛ p`, `y → M ∖ {p}`
      have hsub : exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y ⊆
          insert z ((VV D W u j \ BB D W u j z).erase p) := by
        intro b hb
        rcases Finset.mem_insert.mp (exitN_sub hb) with rfl | hb'
        · exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨?_, hb'⟩)
          rintro rfl; exact hpE hb
      have hzM : z ∉ (VV D W u j \ BB D W u j z).erase p := fun h =>
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).2 hzB
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_insert_of_notMem hzM, Finset.card_erase_of_mem hpM]
        have : 1 ≤ (VV D W u j \ BB D W u j z).card := Finset.card_pos.mpr ⟨p, hpM⟩
        omega)
      have hall : ∀ x ∈ VV D W u j, x ∉ BB D W u j z → x ≠ p → FF D W u j y x = true := by
        intro x hx hxB hxp
        apply exitN_arc (z := z)
        rw [heq]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxp, Finset.mem_sdiff.mpr ⟨hx, hxB⟩⟩)
      obtain ⟨a, ha⟩ := exists_Ap (j := j) hu hp hp1
      have haV := Ap_V hu ha
      have hap : a ≠ p := by rintro rfl; exact hp1 ha.1
      have ha1 : a ∉ ball D W u 1 := fun h => ha.2.1 (ball_mono_radius (by omega) h)
      obtain ⟨hyK, hya⟩ := notK_of_arc (VV_sub haV) ha1 (hall a haV (hA a ha) hap)
      have hyz : D y z = true := by have := exitN_arc hzE; rwa [FF_of_not_mem hyK] at this
      have hallD : ∀ x ∈ VV D W u j, x ∉ BB D W u j z → x ≠ p → D y x = true := by
        intro x hx hxB hxp
        have := hall x hx hxB hxp
        rwa [FF_of_not_mem hyK] at this
      rcases fold_walk hzK wzy with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
      · exact absurd (h.snoc hzW hyz) (hfree z (m + 1) (by omega) (by omega))
      · have hm2 : j + 1 ≤ m2 := by
          by_contra hlt
          exact ha.2.1 (ball_step (mem_ball_of_walk w2 (by omega) hyW) (VV_sub haV) hya)
        rcases (by omega : m1 = 1 ∨ m1 = 2) with rfl | rfl
        · exact Or.inl ⟨c, hc, fold_one hzK w1⟩
        · obtain ⟨w, hwV, hwK, hzw, hwc⟩ := fold_two hzK hc w1
          exact Or.inr ⟨hpE, y, mem_ball_of_walk w2 (by omega) hyW, hyz, hallD, w, hwV, hwK, hzw, c, hc, hwc⟩
  · -- (a): `y ↛ z`, so `exitN y = M ∋ p`
    have hsub : exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y ⊆ VV D W u j \ BB D W u j z := by
      intro b hb
      rcases Finset.mem_insert.mp (exitN_sub hb) with rfl | hb'
      · exact absurd hb hzE
      · exact hb'
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hpE : p ∈ exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y := by rw [heq]; exact hpM
    obtain ⟨hyK, hyp⟩ := notK_of_arc hpW hp1' (exitN_arc hpE)
    rcases fold_walk hzK wzy with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
    · exact absurd ((h.snoc hpW hyp).snoc hzW hpz) (hfree z (m + 1 + 1) (by omega) (by omega))
    · exfalso
      have hy2 : y ∈ ball D W u (j + 2) := mem_ball_of_walk w2 (by omega) hyW
      have hy1 : y ∉ ball D W u (j + 1) := fun h => hp1 (ball_step h hpW hyp)
      exact hA y ⟨hy2, hy1, hyp⟩ hy

/-- `exit_small` on the fold, stated with `BB`. -/
theorem exit_BB (hS : BallSmall (j + 3) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W)
    {z r : ℕ} (hzV : z ∈ VV D W u j) (hr : 1 ≤ r) (hcard : (BB D W u j z).card + r ≤ 4 * (j + 3) + 1) :
    ∃ y ∈ BB D W u j z, r + 2 ≤ (exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y).card :=
  exit_small (G := FF D W u j) (W := VV D W u j) (k := j + 3) (s := 4) (by omega) hS (FF_qfree hfree)
    (FF_outEq hfree hout hu) hzV hr hcard

/-- **Lemma 5_s** (`s = 4`): if `|V♮| ≤ 4k+2`, every π-target `z` of `p ∈ N_k` has `z → K`. -/
theorem pi_P6 (hS : BallSmall (j + 3) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W)
    (hV : (VV D W u j).card ≤ 4 * (j + 3) + 2) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j) :
    ∃ c ∈ KK D W u j, D z c = true := by
  classical
  by_cases hA : ∃ a, Ap D W u j p a ∧ a ∈ BB D W u j z
  · obtain ⟨a, ha, haB⟩ := hA
    exact stepA hfree hp hpz hzW hzK ha haB
  push Not at hA
  have hzV : z ∈ VV D W u j := toV hfree hu hp hpz hzW
  have hpV : p ∈ VV D W u j := pV_of hu hp hp1
  obtain ⟨a, ha⟩ := exists_Ap (j := j) hu hp hp1
  have hap : a ≠ p := by rintro rfl; exact hp1 ha.1
  have hpM : p ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨hpV, pi_not_mem hfree hp hp1 hpz hzW hzK⟩
  have haM : a ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨Ap_V hu ha, hA a ha⟩
  have hM2 : 2 ≤ (VV D W u j \ BB D W u j z).card := by
    have hsub : ({p, a} : Finset ℕ) ⊆ VV D W u j \ BB D W u j z := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hpM
      · rw [Finset.mem_singleton.mp hx]; exact haM
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hap.symm] at this
  have hBV : (VV D W u j \ BB D W u j z).card + (BB D W u j z).card = (VV D W u j).card :=
    Finset.card_sdiff_add_card_eq_card ball_subset
  obtain ⟨y, hy, hc⟩ := exit_BB hS hfree hout hu (r := (VV D W u j \ BB D W u j z).card - 1) hzV
    (by omega) (by omega)
  rcases stepExit hfree hu hp hp1 hpz hzW hzK hA hy (by omega) with h | ⟨hpE, _⟩
  · exact h
  · exfalso
    have hzM : z ∉ VV D W u j \ BB D W u j z := fun h => (Finset.mem_sdiff.mp h).2 (self_mem_ball hzV)
    have heq := Finset.eq_of_subset_of_card_le (exitN_sub (z := z) (y := y)) (by
      rw [Finset.card_insert_of_notMem hzM]; omega)
    exact hpE (by rw [heq]; exact Finset.mem_insert_of_mem hpM)

/-- The closed case `N_{k+1} = ∅` is impossible under `Ball(k+1,4)` when `b_{k+1} ≤ 4k+4`. -/
theorem closed_case (hb4 : Ball (j + 4) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W)
    (hlt : (ball D W u (j + 4)).card ≤ 4 * (j + 3) + 4) (h : (ball D W u (j + 4)).card ≤ (ball D W u (j + 3)).card) :
    False := by
  obtain ⟨hout', hne⟩ := closed_outEq_s (q := j + 5) (k := j + 3) (s := 4) (by omega) (by omega) (by omega)
    hfree hout hu h
  have hUW : (ball D W u (j + 3)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hfE : QFree D ((ball D W u (j + 3)).erase u) (j + 4) := (hfree.mono_bound (by omega)).mono_set hUW
  have hc := card_ge_of_ball (q := j + 4) (s := 4) (b := 4 * (j + 3) + 1) (by omega) hfE
    (fun y hy => (hout' y hy).ge)
    (fun z hz => by
      have := hb4 D _ hfE hout' z hz
      rwa [show j + 4 - 1 = j + 3 by omega] at this) hne
  have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := j + 3) hu)
  have hsub : ball D W u (j + 3) ⊆ ball D W u (j + 4) := ball_mono_radius (by omega)
  have := Finset.card_le_card hsub
  omega

theorem bk_of_ball (hb4 : Ball (j + 4) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W) :
    4 * (j + 3) + 1 ≤ (ball D W u (j + 3)).card := by
  have := hb4 D W (hfree.mono_bound (by omega)) hout u hu
  rwa [show j + 4 - 1 = j + 3 by omega] at this

/-- **Theorem 6_s** (`s = 4`): `b_{k+1} ≥ 4k+4`. -/
theorem thm6 (hS : BallSmall (j + 3) 4) (hb4 : Ball (j + 4) 4) (hfree : QFree D W (j + 5))
    (hout : OutEq 4 D W) (hu : u ∈ W) (hbk1 : 4 * (j + 2) + 1 ≤ (ball D W u (j + 2)).card) :
    4 * (j + 3) + 4 ≤ (ball D W u (j + 4)).card := by
  classical
  have hbk := bk_of_ball hb4 hfree hout hu
  by_contra hlt
  have hsub : ball D W u (j + 3) ⊆ ball D W u (j + 4) := ball_mono_radius (by omega)
  have eK := Finset.card_sdiff_add_card_eq_card hsub
  by_cases c0 : (ball D W u (j + 4)).card ≤ (ball D W u (j + 3)).card
  · exact closed_case hb4 hfree hout hu (by omega) c0
  have hV : (VV D W u j).card ≤ 4 * (j + 3) + 2 := by
    rw [Finset.card_erase_of_mem (self_mem_ball hu)]; omega
  have hK : (KK D W u j).card ≤ 2 := by simp only [KK]; omega
  have hN : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ 5 := by
    rw [Finset.card_sdiff_of_subset (ball_mono_radius (by omega))]; omega
  set P := (ball D W u (j + 3) \ ball D W u (j + 2)).filter (fun p => (outN D (KK D W u j) p).Nonempty) with hPdef
  have hP5 : P.card ≤ 5 := (Finset.card_filter_le _ _).trans hN
  have hPW : P ⊆ W := fun p hp => ball_subset (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  have hPne : P.Nonempty := by
    obtain ⟨c, hc⟩ : (KK D W u j).Nonempty := by rw [← Finset.card_pos]; simp only [KK]; omega
    obtain ⟨hc4, hc3⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨p, hp, hpc⟩ := ball_succ_pred hu hc4 hc3
    have hp1 : p ∉ ball D W u (j + 2) := fun h => hc3 (ball_step h (ball_subset hc4) hpc)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp, hp1⟩, c, mem_outN.mpr ⟨hc, hpc⟩⟩⟩
  have hmin : ∀ p ∈ P, 2 ≤ (outN D P p).card := by
    intro p hpP
    obtain ⟨hpN, -⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hp, hp1⟩ := Finset.mem_sdiff.mp hpN
    have hpW : p ∈ W := ball_subset hp
    have hsub2 : outN D W p \ KK D W u j ⊆ outN D P p := by
      intro z hz
      obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
      obtain ⟨c, hc, hzc⟩ := pi_P6 hS hfree hout hu hV hp hp1 hpz hzW hzK
      have hz3 := mem_ball_of_V (toV hfree hu hp hpz hzW) hzK
      have hz2 : z ∉ ball D W u (j + 2) := fun h =>
        (Finset.mem_sdiff.mp hc).2 (ball_step h (ball_subset (Finset.mem_sdiff.mp hc).1) hzc)
      exact mem_outN.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hz3, hz2⟩, c, mem_outN.mpr ⟨hc, hzc⟩⟩, hpz⟩
    have h1 := Finset.le_card_sdiff (KK D W u j) (outN D W p)
    rw [hout p hpW] at h1
    have := Finset.card_le_card hsub2
    omega
  have := ch2_set (q := 3) (by omega) ((hfree.mono_bound (by omega)).mono_set hPW) hmin hPne
  omega

/-- **Lemma 8 (trichotomy)** for `|V♮| = 4k+3`. -/
theorem tri (hS : BallSmall (j + 3) 4) (hfree : QFree D W (j + 5)) (hout : OutEq 4 D W) (hu : u ∈ W)
    (hV : (VV D W u j).card = 4 * (j + 3) + 3) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j) :
    (∃ c ∈ KK D W u j, D z c = true) ∨ R2 D W u j p z ∨ R0 D W u j p z := by
  classical
  by_cases hA : ∃ a, Ap D W u j p a ∧ a ∈ BB D W u j z
  · obtain ⟨a, ha, haB⟩ := hA
    exact Or.inl (stepA hfree hp hpz hzW hzK ha haB)
  push Not at hA
  have hzV : z ∈ VV D W u j := toV hfree hu hp hpz hzW
  have hpV : p ∈ VV D W u j := pV_of hu hp hp1
  obtain ⟨a, ha⟩ := exists_Ap (j := j) hu hp hp1
  have hap : a ≠ p := by rintro rfl; exact hp1 ha.1
  have hpM : p ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨hpV, pi_not_mem hfree hp hp1 hpz hzW hzK⟩
  have haM : a ∈ VV D W u j \ BB D W u j z := Finset.mem_sdiff.mpr ⟨Ap_V hu ha, hA a ha⟩
  have hpa : ({p, a} : Finset ℕ) ⊆ VV D W u j \ BB D W u j z := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hpM
    · rw [Finset.mem_singleton.mp hx]; exact haM
  have hM2 : 2 ≤ (VV D W u j \ BB D W u j z).card := by
    have := Finset.card_le_card hpa
    rwa [Finset.card_pair hap.symm] at this
  have hBV : (VV D W u j \ BB D W u j z).card + (BB D W u j z).card = (VV D W u j).card :=
    Finset.card_sdiff_add_card_eq_card ball_subset
  by_cases hY : ∃ y ∈ BB D W u j z, (VV D W u j \ BB D W u j z).card ≤
      (exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y).card
  · obtain ⟨y, hy, hc⟩ := hY
    rcases stepExit hfree hu hp hp1 hpz hzW hzK hA hy hc with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at hY
  have hM : (VV D W u j \ BB D W u j z).card = 2 := by
    by_contra hne
    obtain ⟨y, hy, hc⟩ := exit_BB hS hfree hout hu (r := (VV D W u j \ BB D W u j z).card - 2) hzV
      (by omega) (by omega)
    have := hY y hy
    omega
  refine Or.inr (Or.inr ⟨fun x hx => ⟨fun hxB => ?_, ?_⟩, fun y hy => by have := hY y hy; omega⟩)
  · have heq : ({p, a} : Finset ℕ) = VV D W u j \ BB D W u j z :=
      Finset.eq_of_subset_of_card_le hpa (by rw [hM, Finset.card_pair hap.symm])
    have hx' : x ∈ ({p, a} : Finset ℕ) := by rw [heq]; exact Finset.mem_sdiff.mpr ⟨hx, hxB⟩
    rcases Finset.mem_insert.mp hx' with rfl | hx'
    · exact Or.inl rfl
    · rw [Finset.mem_singleton.mp hx']; exact Or.inr ha
  · rintro (rfl | hx')
    · exact pi_not_mem hfree hp hp1 hpz hzW hzK
    · exact hA x hx'

end LeanCH.BR.BRq4
