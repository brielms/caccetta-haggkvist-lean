import LeanCH.BR.BRq4Pi

/-!
# The fold at general out-degree `s`: Lemma 5_s, Theorem 6_s and Lemma 8 (e = 2) (Lean 4.35.0)

Paper: `BallQ5_attempt_subagent.md` §3 (Q4), `Route1_GeneralS_subagent.md` §2, `BallQ4_attempt_subagent.md` §3. The
`s = 4` versions are `BRq4Pi.lean` (`exit_BB`, `pi_P6`, `closed_case`, `thm6`, `tri`).

Level `k = j + 3`, `D` `(k+2)`-free with out-degree `s` on `W`. The `BRq4` definitions `KK`, `VV`, `FF`, `BB`, `Ap`,
`R2`, `R0` and the lemmas `pi_not_mem`, `stepA`, `stepExit`, `fold_walk`, … never mention the out-degree and are
reused as they are.

* `digon_bound`: a digon-free `D[U]` with min out `≥ δ` has `|U| ≥ 2δ+1` (the tournament count).
* `pi_P6_s` (**Lemma 5_s**): if `|V♮| ≤ sk+2`, every π-target heads `K`.
* `closed_case_s`, `thm6_s` (**Theorem 6_s**, `4 ≤ s`): `BallSmall(k,s)`, `Ball(k+1,s)`, `b_{k-1} ≥ s(k-1)+1` give
  `b_{k+1} ≥ sk+4`, i.e. excess `e ≥ 2`.
* `tri_s` (**Lemma 8**, `e = 2`): if `|V♮| = sk+3`, a π-target heads `K`, or is `R2`, or is `R0`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRq4

variable {D : CH.Digraph} {W : Finset ℕ} {u j s : ℕ}

/-- The fold has out-degree `s` on `V♮`. -/
theorem FF_outEq_s (hfree : QFree D W (j + 5)) (hout : OutEq s D W) (hu : u ∈ W) :
    OutEq s (FF D W u j) (VV D W u j) :=
  rewire_outEq_s (q := j + 5) (k := j + 3) (by omega) hfree hout hu

/-- **Tournament count.** A digon-free `D[U]` with min out `≥ δ` has at least `2δ+1` vertices. -/
theorem digon_bound {U : Finset ℕ} {δ : ℕ} (hfree : QFree D U 2) (hmin : ∀ y ∈ U, δ ≤ (outN D U y).card)
    (hne : U.Nonempty) : 2 * δ + 1 ≤ U.card := by
  classical
  have hball : ∀ z ∈ U, δ + 1 ≤ (ball D U z (2 - 1)).card := by
    intro z hz
    have hsub : insert z (outN D U z) ⊆ ball D U z 1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact self_mem_ball hz
      · exact ball_of_adj (mem_outN.mp hx).1 (mem_outN.mp hx).2
    have hzO : z ∉ outN D U z := fun h => loopfree hfree (by omega) hz (mem_outN.mp h).2
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hzO] at this
    have := hmin z hz
    exact (by omega : δ + 1 ≤ (ball D U z 1).card)
  have := card_ge_of_ball (q := 2) (s := δ) (b := δ + 1) (by omega) hfree hmin hball hne
  omega

/-- `exit_small` on the fold at out-degree `s`. -/
theorem exit_BB_s (hS : BallSmall (j + 3) s) (hfree : QFree D W (j + 5)) (hout : OutEq s D W) (hu : u ∈ W)
    {z r : ℕ} (hzV : z ∈ VV D W u j) (hr : 1 ≤ r) (hcard : (BB D W u j z).card + r ≤ s * (j + 3) + 1) :
    ∃ y ∈ BB D W u j z, r + 2 ≤ (exitN (FF D W u j) (VV D W u j) (BB D W u j z) z y).card :=
  exit_small (G := FF D W u j) (W := VV D W u j) (k := j + 3) (s := s) (by omega) hS (FF_qfree hfree)
    (FF_outEq_s hfree hout hu) hzV hr hcard

/-- **Lemma 5_s**: if `|V♮| ≤ sk+2`, every π-target `z` of `p ∈ N_k` has `z → K`. -/
theorem pi_P6_s (hS : BallSmall (j + 3) s) (hfree : QFree D W (j + 5)) (hout : OutEq s D W) (hu : u ∈ W)
    (hV : (VV D W u j).card ≤ s * (j + 3) + 2) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
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
  obtain ⟨y, hy, hc⟩ := exit_BB_s hS hfree hout hu (r := (VV D W u j \ BB D W u j z).card - 1) hzV
    (by omega) (by omega)
  rcases stepExit hfree hu hp hp1 hpz hzW hzK hA hy (by omega) with h | ⟨hpE, _⟩
  · exact h
  · exfalso
    have hzM : z ∉ VV D W u j \ BB D W u j z := fun h => (Finset.mem_sdiff.mp h).2 (self_mem_ball hzV)
    have heq := Finset.eq_of_subset_of_card_le (exitN_sub (z := z) (y := y)) (by
      rw [Finset.card_insert_of_notMem hzM]; omega)
    exact hpE (by rw [heq]; exact Finset.mem_insert_of_mem hpM)

/-- The closed case `N_{k+1} = ∅` is impossible under `Ball(k+1,s)` when `b_{k+1} ≤ sk+s+1` (`1 ≤ s`). -/
theorem closed_case_small_s (hs : 1 ≤ s)
    (hb4 : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U (j + 5) → OutEq s F U →
      U.card ≤ s * (j + 4) + 1 → ∀ z ∈ U, s * (j + 3) + 1 ≤ (ball F U z (j + 3)).card)
    (hfree : QFree D W (j + 5)) (hout : OutEq s D W)
    (hu : u ∈ W) (hlt : (ball D W u (j + 4)).card ≤ s * (j + 3) + s + 1)
    (h : (ball D W u (j + 4)).card ≤ (ball D W u (j + 3)).card) : False := by
  obtain ⟨hout', hne⟩ := closed_outEq_s (q := j + 5) (k := j + 3) (s := s) hs (by omega) (by omega)
    hfree hout hu h
  have hUW : (ball D W u (j + 3)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hfE := hfree.mono_set hUW
  have hsub : ball D W u (j + 3) ⊆ ball D W u (j + 4) := ball_mono_radius (by omega)
  have hle := Finset.card_le_card hsub
  have herase := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := j + 3) hu)
  have hsize : ((ball D W u (j + 3)).erase u).card ≤ s * (j + 4) + 1 := by
    rw [show j + 4 = (j + 3) + 1 by omega, Nat.mul_add_one]
    omega
  have hc := card_ge_of_ball (q := j + 4) (s := s) (b := s * (j + 3) + 1) (by omega)
    (hfE.mono_bound (by omega))
    (fun y hy => (hout' y hy).ge)
    (by simpa only [show j + 4 - 1 = j + 3 by omega] using hb4 D _ hfE hout' hsize) hne
  omega

theorem bk_of_ball_s (hb4 : Ball (j + 4) s) (hfree : QFree D W (j + 5)) (hout : OutEq s D W) (hu : u ∈ W) :
    s * (j + 3) + 1 ≤ (ball D W u (j + 3)).card := by
  have := hb4 D W (hfree.mono_bound (by omega)) hout u hu
  rwa [show j + 4 - 1 = j + 3 by omega] at this

theorem closed_case_s (hs : 1 ≤ s) (hb4 : Ball (j + 4) s) (hfree : QFree D W (j + 5)) (hout : OutEq s D W)
    (hu : u ∈ W) (hlt : (ball D W u (j + 4)).card ≤ s * (j + 3) + s + 1)
    (h : (ball D W u (j + 4)).card ≤ (ball D W u (j + 3)).card) : False :=
  closed_case_small_s hs (fun _ _ hf ho _ _ hz => bk_of_ball_s hb4 hf ho hz) hfree hout hu hlt h

/-- The fold uses the radius-`k` bound in the ambient graph and the
boundary-size version of that bound in the closed case. -/
theorem thm6_of_local_ball_s (hs : 4 ≤ s) (hS : BallSmall (j + 3) s)
    (hb4 : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U (j + 5) → OutEq s F U →
      U.card ≤ s * (j + 4) + 1 → ∀ z ∈ U, s * (j + 3) + 1 ≤ (ball F U z (j + 3)).card)
    (hfree : QFree D W (j + 5))
    (hout : OutEq s D W) (hu : u ∈ W) (hbk1 : s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card)
    (hbk : s * (j + 3) + 1 ≤ (ball D W u (j + 3)).card) :
    s * (j + 3) + 4 ≤ (ball D W u (j + 4)).card := by
  classical
  by_contra hlt
  have hsub : ball D W u (j + 3) ⊆ ball D W u (j + 4) := ball_mono_radius (by omega)
  have eK := Finset.card_sdiff_add_card_eq_card hsub
  have e3 : (ball D W u (j + 3) \ ball D W u (j + 2)).card + (ball D W u (j + 2)).card =
      (ball D W u (j + 3)).card := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hsj : s * (j + 3) = s * (j + 2) + s := by rw [show j + 3 = (j + 2) + 1 by omega, Nat.mul_add_one]
  by_cases c0 : (ball D W u (j + 4)).card ≤ (ball D W u (j + 3)).card
  · exact closed_case_small_s (by omega) hb4 hfree hout hu (by omega) c0
  have hV : (VV D W u j).card ≤ s * (j + 3) + 2 := by
    rw [Finset.card_erase_of_mem (self_mem_ball hu)]; omega
  have hK : (KK D W u j).card ≤ 2 := by simp only [KK]; omega
  have hN : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ s + 1 := by omega
  set P := (ball D W u (j + 3) \ ball D W u (j + 2)).filter (fun p => (outN D (KK D W u j) p).Nonempty) with hPdef
  have hPN : P.card ≤ s + 1 := (Finset.card_filter_le _ _).trans hN
  have hPW : P ⊆ W := fun p hp => ball_subset (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  have hPne : P.Nonempty := by
    obtain ⟨c, hc⟩ : (KK D W u j).Nonempty := by rw [← Finset.card_pos]; simp only [KK]; omega
    obtain ⟨hc4, hc3⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨p, hp, hpc⟩ := ball_succ_pred hu hc4 hc3
    have hp1 : p ∉ ball D W u (j + 2) := fun h => hc3 (ball_step h (ball_subset hc4) hpc)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp, hp1⟩, c, mem_outN.mpr ⟨hc, hpc⟩⟩⟩
  have hmin : ∀ p ∈ P, s - 2 ≤ (outN D P p).card := by
    intro p hpP
    obtain ⟨hpN, -⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hp, hp1⟩ := Finset.mem_sdiff.mp hpN
    have hpW : p ∈ W := ball_subset hp
    have hsub2 : outN D W p \ KK D W u j ⊆ outN D P p := by
      intro z hz
      obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
      obtain ⟨c, hc, hzc⟩ := pi_P6_s hS hfree hout hu hV hp hp1 hpz hzW hzK
      have hz3 := mem_ball_of_V (toV hfree hu hp hpz hzW) hzK
      have hz2 : z ∉ ball D W u (j + 2) := fun h =>
        (Finset.mem_sdiff.mp hc).2 (ball_step h (ball_subset (Finset.mem_sdiff.mp hc).1) hzc)
      exact mem_outN.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hz3, hz2⟩, c, mem_outN.mpr ⟨hc, hzc⟩⟩, hpz⟩
    have h1 := Finset.le_card_sdiff (KK D W u j) (outN D W p)
    rw [hout p hpW] at h1
    have := Finset.card_le_card hsub2
    omega
  have hfP : QFree D P (j + 5) := hfree.mono_set hPW
  have h7 := ch2_set (q := 3) (by omega) (hfP.mono_bound (by omega))
    (fun p hp => (by have := hmin p hp; omega : 2 ≤ (outN D P p).card)) hPne
  have hd := digon_bound (hfP.mono_bound (by omega)) hmin hPne
  omega

/-- **Theorem 6_s** (`4 ≤ s`): `BallSmall(k,s)`, `Ball(k+1,s)` and `b_{k-1} ≥ s(k-1)+1` give `b_{k+1} ≥ sk+4`. -/
theorem thm6_s (hs : 4 ≤ s) (hS : BallSmall (j + 3) s) (hb4 : Ball (j + 4) s) (hfree : QFree D W (j + 5))
    (hout : OutEq s D W) (hu : u ∈ W) (hbk1 : s * (j + 2) + 1 ≤ (ball D W u (j + 2)).card) :
    s * (j + 3) + 4 ≤ (ball D W u (j + 4)).card :=
  thm6_of_local_ball_s hs hS (fun _ _ hf ho _ _ hz => bk_of_ball_s hb4 hf ho hz)
    hfree hout hu hbk1 (bk_of_ball_s hb4 hfree hout hu)

/-- **Lemma 8 (trichotomy)** for `|V♮| = sk+3` (excess `e = 2`), any `s`. -/
theorem tri_s (hS : BallSmall (j + 3) s) (hfree : QFree D W (j + 5)) (hout : OutEq s D W) (hu : u ∈ W)
    (hV : (VV D W u j).card = s * (j + 3) + 3) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
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
    obtain ⟨y, hy, hc⟩ := exit_BB_s hS hfree hout hu (r := (VV D W u j \ BB D W u j z).card - 2) hzV
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

end LeanCH.BR.BRsGen
