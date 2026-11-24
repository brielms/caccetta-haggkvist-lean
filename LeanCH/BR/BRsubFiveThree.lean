import LeanCH.BR.BRsubFirstPairDensity
import LeanCH.BR.BRTwentyFifteenCore
import LeanCH.BR.BRsubNineFive

/-! The mixed-core contradiction excludes every deficient (5,3) tail. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

variable {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}

theorem no_five_three_deficient (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (h3 : (ball D V u 3 \ ball D V u 2).card = 5)
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
  have hcount : U.card = H.card + 5 := by omega
  have hUlo : 16 ≤ U.card := by omega
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
    have hprod := Nat.mul_le_mul_right U.card (by omega : U.card ≤ 19)
    nlinarith
  exact three_core_twenty_fifteen_false (hf.mono_set hUV) hminU hHU hhigh hU20 (by omega)

theorem fourth_three_third_ge_six (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (h4 : (ball D V u 4 \ ball D V u 3).card = 3) :
    6 ≤ (ball D V u 3 \ ball D V u 2).card := by
  have h3 := third_layer_ge_four hf hu hmin hb4
  by_contra hn
  rcases (by omega : (ball D V u 3 \ ball D V u 2).card = 4 ∨
    (ball D V u 3 \ ball D V u 2).card = 5) with hfour | hfive
  · exact no_four_three_deficient hf hu hmin hb4 hfour h4
  · exact no_five_three_deficient hf hu hmin hb4 hfive h4

theorem no_large_first_fifteen_deficient (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (hpair : (outN D V u).card + (ball D V u 2 \ ball D V u 1).card = 15)
    (hfirst : 9 ≤ (outN D V u).card) : False := by
  have h3 := third_layer_ge_four hf hu hmin hb4
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have h3five : 5 ≤ (ball D V u 3 \ ball D V u 2).card := by
    by_contra hn
    have hd := third_four_first_pair_density_strong hf hu hmin (by omega)
    dsimp only at hd
    rw [hpair] at hd
    omega
  exact no_five_three_deficient hf hu hmin hb4 (by omega) (by omega)

theorem no_ten_five_deficient (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24) (h1 : (outN D V u).card = 10)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 5) : False :=
  no_large_first_fifteen_deficient hf hu hmin hb4 (by omega) (by omega)

theorem no_nine_six_deficient (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24) (h1 : (outN D V u).card = 9)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 6) : False :=
  no_large_first_fifteen_deficient hf hu hmin hb4 (by omega) (by omega)

theorem second_ge_six_of_first_pair_bounds (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (hpair : 13 ≤ (outN D V u).card + (ball D V u 2 \ ball D V u 1).card ∧
      (outN D V u).card + (ball D V u 2 \ ball D V u 1).card ≤ 15) :
    6 ≤ (ball D V u 2 \ ball D V u 1).card := by
  have hlo := second_layer_ge_five hf hu hmin hb4
  by_contra hn
  have h2 : (ball D V u 2 \ ball D V u 1).card = 5 := by omega
  rcases (by omega : (outN D V u).card = 8 ∨ (outN D V u).card = 9 ∨
      (outN D V u).card = 10) with h8 | h9 | h10
  · exact no_eight_five_deficient hf hu hmin h8 h2 hb4
  · exact no_nine_five_deficient hf hu hmin h9 h2 hb4
  · exact no_ten_five_deficient hf hu hmin hb4 h10 h2

theorem first_le_eight_of_first_pair_bounds (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (hpair : 13 ≤ (outN D V u).card + (ball D V u 2 \ ball D V u 1).card ∧
      (outN D V u).card + (ball D V u 2 \ ball D V u 1).card ≤ 15) :
    (outN D V u).card ≤ 8 := by
  have h2 := second_ge_six_of_first_pair_bounds hf hu hmin hb4 hpair
  by_contra hn
  exact no_nine_six_deficient hf hu hmin hb4 (by omega) (by omega)

end LeanCH.BR.BRsub
