import LeanCH.BR.BRBallFive
import LeanCH.BR.BRsGen2Step

/-! Excluding a radius-four ball of size nineteen at out-degree five. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BRq4 BR45

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

private theorem no_twelve_two_five {U X : Finset ℕ} (hf : QFree D U 5)
    (hU : U.card = 12) (hXU : X ⊆ U) (hX : X.card = 5)
    (hmin : ∀ v ∈ U, 2 ≤ (outN D U v).card)
    (hhigh : ∀ v ∈ X, 5 ≤ (outN D U v).card) : False := by
  have hin : ∀ v ∈ U, (inN D U v).card ≤ 3 := by
    intro v hv
    have hb := ball_growth 5 (by decide) D U hf hmin v hv 4 (by decide)
    have hs : inN D U v ⊆ U \ ball D U v 4 := by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨(mem_inN.mp hz).1,
        fun hzB => no_back_arc hf hv hzB (by decide) (mem_inN.mp hz).2⟩
    have hc := Finset.card_le_card hs
    have he := Finset.card_sdiff_add_card_eq_card (ball_subset (D := D) (W := U) (u := v) (k := 4))
    omega
  have hc := Finset.card_sdiff_add_card_eq_card hXU
  have hlo := Finset.sum_le_sum (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1)
    (s := U \ X)
  have hhi := Finset.sum_le_sum hhigh
  have hup := Finset.sum_le_sum hin
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hlo hhi hup
  have he := Finset.sum_sdiff hXU (f := fun v => (outN D U v).card)
  have hsum := sum_out_in D U
  omega

/-- The excess-two fold at degree five and level three is impossible. -/
theorem no_five_equality (H : GSet D W u 0 5 2) : False := by
  classical
  let X := outN D W u
  let Y := ball D W u 2 \ ball D W u 1
  let Z := ball D W u 3 \ ball D W u 2
  let K := KK D W u 0
  let P := PP D W u 0
  have hf := H.hfree
  have ho := H.hout
  have hu := H.hu
  have hX : X.card = 5 := ho u hu
  have hY : 5 ≤ Y.card := n2_ge_s (by decide) hf ho hu
  have hb1 : (ball D W u 1).card = 6 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have hYB : Y.card + (ball D W u 1).card = (ball D W u 2).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hZB : Z.card + (ball D W u 2).card = (ball D W u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hKB : K.card + (ball D W u 3).card = (ball D W u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hb2 : 11 ≤ (ball D W u 2).card := by omega
  have C := c15_two (by decide) H hb2
  have htargets : P.card * (5 - K.card - 1) ≤ Y.card := by
    have hlo := Finset.sum_le_sum (fun p hp => (Zp_bound_s C hp).1)
    have hup := sum_Zp_g C
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at hlo
    exact hlo.trans hup
  have hcnt := count_two (by decide) H hb2
  have hPZ : P ⊆ Z := PP_sub
  have hPZc := Finset.card_le_card hPZ
  have hK := H.hK
  have hb := H.hb
  change (ball D W u 4).card = 19 at hb
  change 1 ≤ K.card ∧ K.card ≤ 3 at hK
  change P.card * (5 - K.card - 1) + P.card ≤ Y.card + Z.card ∧
    (2 ≤ K.card → P.card * (5 - K.card) + P.card ≤ Y.card + Z.card) ∧
    6 ≤ 2 * P.card at hcnt
  have hcases : (K.card = 1 ∧ P.card = 3 ∧ Y.card = 9 ∧ Z.card = 3) ∨
      (K.card = 3 ∧ P.card = 3) := by
    rcases (show K.card = 1 ∨ K.card = 2 ∨ K.card = 3 by omega) with h | h | h
    · left
      simp only [h] at hcnt
      simp only [h] at htargets
      omega
    · have hc := hcnt.2.1 (by omega)
      simp only [h] at hc
      omega
    · right
      have hc := hcnt.2.1 (by omega)
      simp only [h] at hc
      omega
  have hP : P.card = 3 := hcases.elim (fun h => h.2.1) (fun h => h.2)
  let U := (ball D W u 3).erase u \ P
  have hUW : U ⊆ W := fun _ hv => ball_subset (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hv).1)
  have hPT : P ⊆ (ball D W u 3).erase u := by
    intro p hp
    obtain ⟨hp3, hp2, _⟩ := mem_PP.mp hp
    exact Finset.mem_erase.mpr ⟨fun h => hp2 (h.symm ▸ self_mem_ball hu), hp3⟩
  have hUcard : U.card + 4 = (ball D W u 3).card := by
    have h := Finset.card_sdiff_add_card_eq_card hPT
    rw [Finset.card_erase_of_mem (self_mem_ball hu)] at h
    have hpos : 0 < (ball D W u 3).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    change U.card + P.card = (ball D W u 3).card - 1 at h
    omega
  have hXU : X ⊆ U := by
    intro x hx
    have hx1 := X_B1 hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by decide) hx1⟩, ?_⟩
    · intro h
      exact loopfree hf (by decide) hu (h ▸ (mem_outN.mp hx).2)
    · intro hp
      exact (mem_PP.mp hp).2.1 (ball_mono_radius (by decide) hx1)
  have hYin : Y ⊆ U := by
    intro y hy
    obtain ⟨hy2, hy1⟩ := Finset.mem_sdiff.mp hy
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hy1 (h.symm ▸ self_mem_ball hu),
      ball_mono_radius (by decide) hy2⟩, ?_⟩
    exact fun hp => (mem_PP.mp hp).2.1 hy2
  have hsplit (v : ℕ) (hv : v ∈ U) : v ∈ X ∨ v ∈ Y ∨ v ∈ Z := by
    obtain ⟨hvt, _⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvu, hv3⟩ := Finset.mem_erase.mp hvt
    rcases split4 hu v with h | h | h | h | h
    · exact (hvu h).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (h hv3).elim
  have hXhead (v : ℕ) (hv : v ∈ X) : outN D W v ⊆ outN D U v := by
    intro z hz
    have hs := headX (hf.mono_bound (by decide)) hu hv (mem_outN.mp hz).1 (mem_outN.mp hz).2
    refine mem_outN.mpr ⟨?_, (mem_outN.mp hz).2⟩
    rcases Finset.mem_union.mp hs with h | h
    · exact hXU h
    · exact hYin h
  have hZhead (v : ℕ) (hv : v ∈ U) (hvZ : v ∈ Z) : outN D W v ⊆ outN D U v := by
    intro z hz
    obtain ⟨hzW, hvz⟩ := mem_outN.mp hz
    have hv3 := (Finset.mem_sdiff.mp hvZ).1
    have hz4 := ball_step hv3 hzW hvz
    have hz3 : z ∈ ball D W u 3 := by
      by_contra hn
      have hvP : v ∈ P := mem_PP.mpr ⟨hv3, (Finset.mem_sdiff.mp hvZ).2,
        z, Finset.mem_sdiff.mpr ⟨hz4, hn⟩, hvz⟩
      exact (Finset.mem_sdiff.mp hv).2 hvP
    refine mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, hz3⟩, ?_⟩, hvz⟩
    · intro h
      exact no_back_arc hf hu hv3 (by decide) (h ▸ hvz)
    · intro hp
      exact no_inP_g C hp v (ball_mono_radius (by decide) hv3) (Finset.mem_sdiff.mp hvZ).2 hvz
  have hYhead (v : ℕ) (hv : v ∈ Y) : outN D W v \ P ⊆ outN D U v := by
    intro z hz
    obtain ⟨hzO, hzP⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzW, hvz⟩ := mem_outN.mp hzO
    have hv2 := (Finset.mem_sdiff.mp hv).1
    exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr
      ⟨fun h => no_back_arc hf hu hv2 (by decide) (h ▸ hvz), ball_step hv2 hzW hvz⟩, hzP⟩, hvz⟩
  have hhigh (v : ℕ) (hv : v ∈ X) : 5 ≤ (outN D U v).card := by
    have h := Finset.card_le_card (hXhead v hv)
    rwa [ho v (outN_subset hv)] at h
  have hmin (v : ℕ) (hv : v ∈ U) : 2 ≤ (outN D U v).card := by
    rcases hsplit v hv with hx | hy | hz
    · exact (by decide : 2 ≤ 5).trans (hhigh v hx)
    · have h := Finset.le_card_sdiff P (outN D W v)
      have hle := Finset.card_le_card (hYhead v hy)
      rw [ho v (hUW hv), hP] at h
      omega
    · have h := Finset.card_le_card (hZhead v hv hz)
      rw [ho v (hUW hv)] at h
      omega
  rcases hcases with ⟨hK1, _, hY9, _⟩ | ⟨hK3, _⟩
  · have hcover : ∀ y ∈ Y, ∃ p ∈ P, D p y = true := by
      have hdisj : ((P : Finset ℕ) : Set ℕ).PairwiseDisjoint (Zp D W u 0) := by
        intro p hp p' hp' hne
        apply Finset.disjoint_left.mpr
        intro y hy hy'
        obtain ⟨hyN, hpy⟩ := mem_outN.mp hy
        have hyW := ball_subset (Finset.mem_sdiff.mp hyN).1
        have hyK : y ∉ KK D W u 0 := fun h => (Finset.mem_sdiff.mp h).2
          (ball_mono_radius (by decide) (Finset.mem_sdiff.mp hyN).1)
        exact hne (disj_target_g C hp hp' hyW hyK hpy (mem_outN.mp hy').2)
      have hsub : P.biUnion (Zp D W u 0) ⊆ Y := Finset.biUnion_subset.mpr (fun _ _ => outN_subset)
      have hlo : ∑ p ∈ P, 3 ≤ ∑ p ∈ P, (Zp D W u 0 p).card := by
        apply Finset.sum_le_sum
        intro p hp
        have h := (Zp_bound_s C hp).1
        change 5 - K.card - 1 ≤ _ at h
        omega
      rw [Finset.sum_const_nat (fun _ _ => rfl), hP] at hlo
      have heq : P.biUnion (Zp D W u 0) = Y := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_biUnion hdisj, hY9]
        exact hlo)
      intro y hy
      rw [← heq] at hy
      obtain ⟨p, hp, hpy⟩ := Finset.mem_biUnion.mp hy
      exact ⟨p, hp, (mem_outN.mp hpy).2⟩
    have hmin3 (v : ℕ) (hv : v ∈ U) : 3 ≤ (outN D U v).card := by
      rcases hsplit v hv with hx | hy | hz
      · exact (by decide : 3 ≤ 5).trans (hhigh v hx)
      · obtain ⟨p, hp, hpv⟩ := hcover v hy
        have hnot : p ∉ outN D W v := fun h =>
          digonfree hf (by decide) (PP_W hp) (hUW hv) hpv (mem_outN.mp h).2
        have heq : outN D W v \ P = outN D W v \ P.erase p := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_erase]
          constructor
          · tauto
          · rintro ⟨hz, hn⟩
            exact ⟨hz, fun hzP => hn ⟨fun he => hnot (he ▸ hz), hzP⟩⟩
        have h := Finset.le_card_sdiff (P.erase p) (outN D W v)
        rw [ho v (hUW hv), Finset.card_erase_of_mem hp, hP, ← heq] at h
        have hle := Finset.card_le_card (hYhead v hy)
        omega
      · have h := Finset.card_le_card (hZhead v hv hz)
        rw [ho v (hUW hv)] at h
        omega
    have hU14 : U.card = 14 := by omega
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hsize := dt_size (by decide) (ball_all 5 (by decide)) (hf.mono_set hUW) hmin3 hne
    omega
  · apply no_twelve_two_five (hf.mono_set hUW) (by omega) hXU hX hmin hhigh

/-- Every radius-four ball in a 5-free digraph with minimum out-degree
five contains at least twenty vertices. -/
theorem card_ball_four_ge_twenty (hf : QFree D W 5)
    (hmin : ∀ v ∈ W, 5 ≤ (outN D W v).card) (hu : u ∈ W) :
    20 ≤ (ball D W u 4).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hmin
  have hF := qfree_sub hsub hf
  have hminF : ∀ v ∈ W, 5 ≤ (outN F W v).card := fun v hv => (ho v hv).ge
  have h20 : 20 ≤ (ball F W u 4).card := by
    by_contra hsmall
    have h19 := card_ball_four_ge_nineteen hF hminF hu
    have heq : (ball F W u 4).card = 19 := by omega
    have h16 := card_ball_three_ge_sixteen hF hminF hu
    have h18 : (ball F W u 3).card ≤ 18 := by
      by_contra hbig
      exact closed_case_small_s (j := 0) (s := 5) (by decide)
        (fun G U hG hOut _ z hz => card_ball_three_ge_sixteen hG
          (fun v hv => (hOut v hv).ge) hz) hF ho hu
          (show (ball F W u 4).card ≤ 21 by omega)
          (show (ball F W u 4).card ≤ (ball F W u 3).card by omega)
    exact no_five_equality ⟨BRsGen35.bball35, hF, ho, hu, heq, h16, h18⟩
  exact h20.trans (Finset.card_le_card (ball_sub hsub))

/-- The cutoff-five cycle bound at minimum out-degree five holds through order 24. -/
theorem ch_five_of_le_twenty_four {n : ℕ} (hn : 0 < n) (hn24 : n ≤ 24)
    (hloop : CH.Loopless D n) (hout : CH.MinOutdegreeAtLeast D n 5) :
    CH.HasDirectedCycleAtMost D n 5 := by
  by_contra hshort
  have hf := qfree_of_noShort hloop hshort
  have hmin : ∀ v ∈ Finset.range n, 5 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hout (Finset.mem_range.mp hv)
  have hsize := card_ge_of_ball (q := 5) (s := 5) (b := 20) (by decide) hf hmin
    (fun _ hu => card_ball_four_ge_twenty hf hmin hu) ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hsize
  omega

end LeanCH.BR.BRsGen
