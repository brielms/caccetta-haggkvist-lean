import LeanCH.BR.BRStrictPrefixDeficiency
import LeanCH.BR.BRHighTwoGrowth
import LeanCH.BR.BRNearBoundaryRows

/-! One high head gives strict growth at a degree-three predecessor. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem high_predecessor_ball_four {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 5) (hmin : ∀ x ∈ V, 3 ≤ (outN D V x).card)
    (hu : u ∈ V) (hv : v ∈ outN D V u)
    (hdegree : (outN D V u).card = 3) (hhigh : 6 ≤ (outN D V v).card) :
    14 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 4).card ≤ 13 := by omega
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  let U := (ball D V u 2).erase u
  have hXc : X.card = 3 := hdegree
  have hXV : X ⊆ V := outN_subset
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXU : X ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) (hX1 hx)⟩
  have hvU := hXU hv
  have hhighX : ∀ x ∈ X, 3 ≤ (outN D U x).card := by
    intro x hx
    exact (hmin x (hXV hx)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hx)))
  have hhighV : 6 ≤ (outN D U v).card := hhigh.trans (Finset.card_le_card
    (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hv)))
  have hUeq : U = X ∪ Y := by
    dsimp only [U]
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by decide) hu]
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hUc : U.card = 3 + Y.card := by rw [hUeq, Finset.card_union_of_disjoint hXY, hXc]
  have hYlo : 4 ≤ Y.card := by
    have hsub : outN D U v ⊆ X.erase v ∪ Y := by
      intro z hz
      obtain ⟨hzU, hvz⟩ := mem_outN.mp hz
      rw [hUeq] at hzU
      rcases Finset.mem_union.mp hzU with hzX | hzY
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨fun heq => loopfree hf (by decide) (hXV hv) (heq ▸ hvz), hzX⟩)
      · exact Finset.mem_union_right _ hzY
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem hv, hXc] at hc
    omega
  have hB1 : (ball D V u 1).card = 4 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by decide) hu, hdegree] at he
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  change Y.card + (ball D V u 1).card = (ball D V u 2).card at h12
  change Z.card + (ball D V u 2).card = (ball D V u 3).card at h23
  change T.card + (ball D V u 3).card = (ball D V u 4).card at h34
  have hZlo : 2 ≤ Z.card := by
    by_contra hZsmall
    by_cases hzero : Z.card = 0
    · have hmin3 : ∀ x ∈ U, 3 ≤ (outN D U x).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
          (by change 3 + Z.card ≤ 3; omega)
      have hh := dt_size (by decide : 1 ≤ 5) (BRq3.ball_all 5 (by decide))
        (hf.mono_set hUV) hmin3 ⟨v, hvU⟩
      omega
    · have hmin2 : ∀ x ∈ U, 2 ≤ (outN D U x).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
          (by change 2 + Z.card ≤ 3; omega)
      have hh := high_two_ball_four (by decide : 5 ≤ 5) (hf.mono_set hUV) hmin2 hvU hhighV
      have hc := Finset.card_le_card (ball_subset (D := D) (W := U) (u := v) (k := 4))
      omega
  have hTc : T.card = 3 := by
    have hTcap : T.card ≤ 3 := by omega
    by_contra hTne
    have hd := prefix_deficiency_strict (d := 3) (k := 2) (by decide : 1 ≤ 5)
      (BRq3.ball_all 5 (by decide)) hf hu (by decide) hmin (by decide)
      (by change T.card < 3; omega)
      (by change (ball D V u 3).card - 1 ≤ 5 * 3; omega)
    change 17 ≤ (ball D V u 3).card - 1 + Z.card * (3 + T.card - 3) at hd
    have hd' : 17 ≤ 3 + Y.card + Z.card + Z.card * T.card := by
      simpa using (show 17 ≤ 3 + Y.card + Z.card + Z.card * (3 + T.card - 3) by omega)
    rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2) with ht | ht | ht <;>
      rw [ht] at hd' <;> omega
  have hYc : Y.card = 4 := by omega
  have hZc : Z.card = 2 := by omega
  have hU7 : U.card = 7 := by omega
  have hmin1 : ∀ x ∈ U, 1 ≤ (outN D U x).card :=
    minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
      (by change 1 + Z.card ≤ 3; omega)
  have hOut : outN D U v = U.erase v := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_erase.mpr
        ⟨fun heq => loopfree hf (by decide) (hXV hv) (heq ▸ (mem_outN.mp hx).2),
          (mem_outN.mp hx).1⟩
    · rw [Finset.card_erase_of_mem hvU, hU7]
      omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hv, hXc]; decide : 0 < (X.erase v).card)
  have hxX := (Finset.mem_erase.mp hx).2
  have hvx : D v x = true := by
    have hxe : x ∈ U.erase v := Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, hXU hxX⟩
    rw [← hOut] at hxe
    exact (mem_outN.mp hxe).2
  have hc := near_boundary_parent_row_cap (by decide : 2 ≤ 5) (hf.mono_set hUV)
    (by omega) hmin1 (hXU hxX) hvU hvx
  have hh := hhighX x hxX
  omega

end LeanCH.BR.BRsGen
