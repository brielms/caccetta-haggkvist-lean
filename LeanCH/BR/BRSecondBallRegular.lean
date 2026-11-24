import LeanCH.BR.BRPrefixFullHeads

/-! A uniform second-ball cap forces out-regularity at every degree s>=2. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem out_regular_of_second_ball_cap {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (hs : 2 ≤ s) (hf : QFree D V s)
    (hmin : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hcap : ∀ v ∈ V, (ball D V v 2).card ≤ 2 * s + 1) : OutEq s D V := by
  classical
  intro u hu
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := Finset.sdiff_subset.trans ball_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hXE : (ball D V u 1).erase u = X := erase_ball_one_eq_outN hf (by omega) hu
  have hB1 : (ball D V u 1).card = X.card + 1 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    rw [hXE] at he
    omega
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  change Y.card + (ball D V u 1).card = (ball D V u 2).card at hsplit
  have hB2 := hcap u hu
  have hminu : s ≤ X.card := hmin u hu
  have hXhi : X.card ≤ s + 1 := by
    by_contra hn
    have hminX : ∀ v ∈ X, 2 ≤ (outN D X v).card := by
      have hh := minOut_prefix_erase (d := 2) hf hu (by omega : 1 + 1 ≤ s) hmin
        (by change 2 + Y.card ≤ s; omega)
      simpa only [hXE] using hh
    have hc := corB (by omega : 1 ≤ s) (hf.mono_set hXV) hminX
      (Finset.card_pos.mp (by omega : 0 < X.card))
    omega
  by_contra hn
  have hXc : X.card = s + 1 := by change X.card ≠ s at hn; omega
  have hminX : ∀ v ∈ X, 1 ≤ (outN D X v).card := by
    have hh := minOut_prefix_erase (d := 1) hf hu (by omega : 1 + 1 ≤ s) hmin
      (by change 1 + Y.card ≤ s; omega)
    simpa only [hXE] using hh
  have hreg := (dt_reg (by omega : 1 ≤ s) (ball_q_one s (by omega))
    (hf.mono_set hXV) hminX (by omega : X.card = s * 1 + 1)).1
  have hYc : Y.card = s - 1 := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
    have hsub := outN_prefix_loss hf hu (by omega : 1 + 1 ≤ s) (hXE.symm ▸ hx)
    rw [hXE] at hsub
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hr := hreg x hx
    have hm := hmin x (hXV hx)
    change (outN D V x).card ≤ (outN D X x).card + Y.card at hc
    omega
  have hfull : ∀ x ∈ X, ∀ y ∈ Y, D x y = true := by
    intro x hx
    apply prefix_loss_full_next hf hu (by omega : 1 + 1 ≤ s) (hXE.symm ▸ hx)
    rw [hXE]
    change (outN D X x).card + Y.card ≤ (outN D V x).card
    have hr := hreg x hx
    have hm := hmin x (hXV hx)
    omega
  obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV)
    (Finset.card_pos.mp (by omega : 0 < Y.card)) (by omega : Y.card ≤ s)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (hminX x hx)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (hminX z (mem_outN.mp hz).1)
  have hzX := (mem_outN.mp hz).1
  have hwX := (mem_outN.mp hw).1
  have hxz := (mem_outN.mp hz).2
  have hzw := (mem_outN.mp hw).2
  have hzx : z ≠ x := fun h => loopfree hf (by omega) (hXV hx) (h ▸ hxz)
  have hwz : w ≠ z := fun h => loopfree hf (by omega) (hXV hzX) (h ▸ hzw)
  have hwx : w ≠ x := fun h => digonfree hf hs (hXV hx) (hXV hzX) hxz (h ▸ hzw)
  let C : Finset ℕ := {x, z, w}
  have hCX : C ⊆ X := by intro a ha; simp only [C, Finset.mem_insert,
    Finset.mem_singleton] at ha; rcases ha with rfl | rfl | rfl <;> assumption
  have hCc : C.card = 3 := by simp [C, Ne.symm hzx, Ne.symm hwx, Ne.symm hwz]
  have hCB : C ⊆ ball D V x 2 := by
    intro a ha
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact self_mem_ball (hXV hx)
    · exact ball_mono_radius (by decide : 1 ≤ 2) (ball_of_adj (hXV hzX) hxz)
    · exact mem_ball.mpr ⟨hXV hwX, 2, le_rfl,
        .step (hXV hzX) hxz (.step (hXV hwX) hzw (.refl _))⟩
  have hYB : Y ⊆ ball D V x 2 := fun a ha =>
    ball_mono_radius (by decide : 1 ≤ 2) (ball_of_adj (hYV ha) (hfull x hx a ha))
  have hOB : outN D V y ⊆ ball D V x 2 := by
    intro a ha
    exact mem_ball.mpr ⟨(mem_outN.mp ha).1, 2, le_rfl,
      .step (hYV hy) (hfull x hx y hy)
        (.step (mem_outN.mp ha).1 (mem_outN.mp ha).2 (.refl a))⟩
  have hCO : Disjoint C (outN D V y) := Finset.disjoint_left.mpr (by
    intro a ha hoa
    exact digonfree hf hs (hXV (hCX ha)) (hYV hy) (hfull a (hCX ha) y hy)
      (mem_outN.mp hoa).2)
  have hYO : Disjoint Y (outN D V y) := Finset.disjoint_left.mpr
    (fun a ha hoa => hsink a ha (mem_outN.mp hoa).2)
  have hCY : Disjoint C Y := hXY.mono_left hCX
  have hU := Finset.card_le_card
    (Finset.union_subset (Finset.union_subset hCB hYB) hOB)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hCO, hYO⟩),
    Finset.card_union_of_disjoint hCY, hCc] at hU
  have hm := hmin y (hYV hy)
  have hc := hcap x (hXV hx)
  omega

end LeanCH.BR.BRsGen
