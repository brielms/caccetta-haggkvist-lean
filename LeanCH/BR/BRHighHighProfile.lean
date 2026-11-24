import LeanCH.BR.BRHighThreeGrowth
import LeanCH.BR.BRMarkedSmallCore

/-! A sharp degree-six ball with a high head has only two possible layer profiles. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem high_high_small_four_profile {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 5) (hmin : ∀ x ∈ V, 3 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = 6)
    (hv : v ∈ outN D V u) (hhigh : 6 ≤ (outN D V v).card)
    (hsmall : (ball D V u 4).card ≤ 15) :
    (ball D V u 2 \ ball D V u 1).card = 3 ∧
      (((ball D V u 3 \ ball D V u 2).card = 4 ∧
          (ball D V u 4 \ ball D V u 3).card = 1) ∨
       ((ball D V u 3 \ ball D V u 2).card = 3 ∧
          (ball D V u 4 \ ball D V u 3).card = 2)) := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  let U := (ball D V u 2).erase u
  have hXc : X.card = 6 := hdegree
  have hXV : X ⊆ V := outN_subset
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXE : (ball D V u 1).erase u = X := erase_ball_one_eq_outN hf (by decide) hu
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXU : X ⊆ U := by
    rw [← hXE]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hUc : U.card = 6 + Y.card := by
    have heq : U = X ∪ Y := by
      dsimp only [U]
      rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu, hXE]
    have hdis : Disjoint X Y := Finset.disjoint_left.mpr
      (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
    rw [heq, Finset.card_union_of_disjoint hdis, hXc]
  have hYlo : 3 ≤ Y.card := by
    by_contra hn
    have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
      have hh := minOut_prefix_erase (d := 1) hf hu (by decide : 1 + 1 ≤ 5) hmin
        (by change 1 + Y.card ≤ 3; omega)
      simpa only [hXE] using hh
    have hr := (dt_reg (by decide : 1 ≤ 5) (ball_q_one 5 (by decide))
      (hf.mono_set hXV) hminX (by omega : X.card = 5 * 1 + 1)).1 v hv
    have hve : v ∈ (ball D V u 1).erase u := by rw [hXE]; exact hv
    have hsub := outN_prefix_loss hf hu (by decide : 1 + 1 ≤ 5) hve
    rw [hXE] at hsub
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    change (outN D V v).card ≤ (outN D X v).card + Y.card at hc
    omega
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  change Y.card + (ball D V u 1).card = (ball D V u 2).card at h12
  change Z.card + (ball D V u 2).card = (ball D V u 3).card at h23
  change T.card + (ball D V u 3).card = (ball D V u 4).card at h34
  have hB3 := high_row_ball_three_min (by decide : 2 ≤ 3) (by decide) hf hmin hu
    (by omega : 5 + 1 ≤ (outN D V u).card)
  have hTcap : T.card ≤ 3 := by omega
  have hdef : T.card ≤ 2 → 17 ≤ 6 + Y.card + Z.card + Z.card * T.card := by
    intro ht
    have hd := prefix_deficiency_strict (d := 3) (k := 2) (by decide : 1 ≤ 5)
      (BRq3.ball_all 5 (by decide)) hf hu (by decide) hmin (by decide)
      (by change T.card < 3; omega)
      (by change (ball D V u 3).card - 1 ≤ 5 * 3; omega)
    change 17 ≤ (ball D V u 3).card - 1 + Z.card * (3 + T.card - 3) at hd
    simpa using (show 17 ≤ 6 + Y.card + Z.card + Z.card * (3 + T.card - 3) by omega)
  change Y.card = 3 ∧ ((Z.card = 4 ∧ T.card = 1) ∨ (Z.card = 3 ∧ T.card = 2))
  rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3) with
    ht0 | ht1 | ht2 | ht3
  · have hh := hdef (by omega); rw [ht0] at hh; omega
  · have hh := hdef (by omega); rw [ht1] at hh
    exact ⟨by omega, Or.inl (by omega)⟩
  · have hh := hdef (by omega); rw [ht2] at hh
    exact ⟨by omega, Or.inr (by omega)⟩
  · exfalso
    have hZlo : 2 ≤ Z.card := by
      by_contra hn
      by_cases hz0 : Z.card = 0
      · have hmin3 : ∀ x ∈ U, 3 ≤ (outN D U x).card :=
          minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
            (by change 3 + Z.card ≤ 3; omega)
        have hh := dt_size (by decide : 1 ≤ 5) (BRq3.ball_all 5 (by decide))
          (hf.mono_set hUV) hmin3 ⟨v, hXU hv⟩
        omega
      · have hmin2 : ∀ x ∈ U, 2 ≤ (outN D U x).card :=
          minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
            (by change 2 + Z.card ≤ 3; omega)
        have hh := corB (by decide : 1 ≤ 5) (hf.mono_set hUV) hmin2 ⟨v, hXU hv⟩
        omega
    have hYc : Y.card = 3 := by omega
    have hZc : Z.card = 2 := by omega
    have hmin1 : ∀ x ∈ U, 1 ≤ (outN D U x).card :=
      minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
        (by change 1 + Z.card ≤ 3; omega)
    have hhighX : ∀ x ∈ X, 3 ≤ (outN D U x).card := by
      intro x hx
      exact (hmin x (hXV hx)).trans (Finset.card_le_card
        (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hx)))
    have hc := Finset.card_sdiff_add_card_eq_card hXU
    exact marked_small_one_core_false (by decide : 2 ≤ 5) (hf.mono_set hUV)
      hmin1 hXU (by omega) hhighX (by omega) (by omega)

end LeanCH.BR.BRsGen
