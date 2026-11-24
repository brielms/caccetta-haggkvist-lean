import LeanCH.BR.BRSixLowCore
import LeanCH.BR.BRsubFiveThree
import LeanCH.BR.BRTwoExitCore
import LeanCH.BR.BRPrefixFullHeads

/-! The 20/14 contradiction removes every deficient (6,3) tail. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

variable {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}

theorem no_six_three_deficient (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (h3 : (ball D V u 3 \ ball D V u 2).card = 6)
    (h4 : (ball D V u 4 \ ball D V u 3).card = 3) : False := by
  classical
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hUc : U.card = (ball D V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have hfirst := hmin u hu
  have hsecond := second_layer_ge_five hf hu hmin hb4
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hcount : U.card = H.card + 6 := by omega
  have hUlo : 17 ≤ U.card := by omega
  have hUhi : U.card ≤ 20 := by omega
  have hminU : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by rw [h4])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  have hd := three_core_six_density (hf.mono_set hUV) hminU hHU hhigh
  have hU20 : U.card = 20 := by
    by_contra hn
    have hp := Nat.mul_le_mul_right U.card (by omega : U.card ≤ 19)
    nlinarith
  exact three_core_twenty_fourteen_false (hf.mono_set hUV) hminU hHU hhigh hU20 (by omega)

theorem fourth_three_third_ge_seven (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (h4 : (ball D V u 4 \ ball D V u 3).card = 3) :
    7 ≤ (ball D V u 3 \ ball D V u 2).card := by
  have hh := fourth_three_third_ge_six hf hu hmin hb4 h4
  by_contra hn
  exact no_six_three_deficient hf hu hmin hb4 (by omega) h4

theorem no_third_four_small_first_pair (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (h3 : (ball D V u 3 \ ball D V u 2).card = 4)
    (hpair : (outN D V u).card + (ball D V u 2 \ ball D V u 1).card ≤ 14) : False := by
  classical
  let U := (ball D V u 2).erase u
  let H := outN D V u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have hUc : U.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have hsecond := second_layer_ge_five hf hu hmin hb4
  have hfirst : 6 ≤ H.card := hmin u hu
  have hHc : H.card = (outN D V u).card := rfl
  have hUhi : U.card ≤ 14 := by omega
  have hcount := Finset.card_sdiff_add_card_eq_card hHU
  have hminU : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin (by rw [h3])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (outN_subset hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
        ((mem_ball_one hu).mpr (Or.inr hv))))
  have hd := two_core_one_exit_density (by decide : 5 ≤ 5) (hf.mono_set hUV)
    hminU hHU hhigh (by omega) (by omega)
  have hp := Nat.mul_le_mul_right U.card hUhi
  nlinarith

theorem eight_six_deficient_profile (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24) (h1 : (outN D V u).card = 8)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 6) :
    (ball D V u 3 \ ball D V u 2).card = 5 ∧
      (ball D V u 4 \ ball D V u 3).card = 4 ∧ (ball D V u 4).card = 24 := by
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have h3 := third_layer_ge_four hf hu hmin hb4
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  have h3ge : 5 ≤ (ball D V u 3 \ ball D V u 2).card := by
    by_contra hn
    exact no_third_four_small_first_pair hf hu hmin hb4 (by omega) (by omega)
  have h4ge : 4 ≤ (ball D V u 4 \ ball D V u 3).card := by
    by_contra hn
    have hh := fourth_three_third_ge_seven hf hu hmin hb4 (by omega)
    omega
  omega

theorem eight_six_two_full_third_parents (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24) (h1 : (outN D V u).card = 8)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 6) :
    2 ≤ ((ball D V u 3 \ ball D V u 2).filter
      (fun v => ∀ w ∈ ball D V u 4 \ ball D V u 3, D v w = true)).card := by
  classical
  obtain ⟨h3, h4, hB4⟩ := eight_six_deficient_profile hf hu hmin hb4 h1 h2
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hUc : U.card = (ball D V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hU19 : U.card = 19 := by omega
  have hH14 : H.card = 14 := by omega
  have hminU : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by rw [h4])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  have htwo := two_core_nineteen_fourteen_two_low_rows (hf.mono_set hUV) hminU hHU hhigh hU19 hH14
  apply htwo.trans
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hvU, hv2⟩ := Finset.mem_filter.mp hv
  have hvnotH : v ∉ H := by
    intro hvH
    have hh := hhigh v hvH
    omega
  have hvZ : v ∈ ball D V u 3 \ ball D V u 2 := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hvU,
      fun h => hvnotH (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hvU).1, h⟩)⟩
  refine Finset.mem_filter.mpr ⟨hvZ, ?_⟩
  apply prefix_loss_full_next hf hu (by decide : 3 + 1 ≤ 5) hvU
  change (outN D U v).card + (ball D V u 4 \ ball D V u 3).card ≤ _
  have hh := hmin v (hUV hvU)
  omega

end LeanCH.BR.BRsub
