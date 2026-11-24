import LeanCH.BR.BRLocalSixCycle
import LeanCH.BR.BRsubNTC6Assembly

/-! Localizing a six-cycle in the deficient third ball of surviving NTC6 profiles. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

theorem six_cycle_in_small_third_ball {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hB2 : 14 ≤ (ball D V u 2).card) (hB3 : (ball D V u 3).card ≤ 19)
    (h4 : (ball D V u 4 \ ball D V u 3).card ≤ 4) :
    ∃ M : Finset ℕ, M ⊆ (ball D V u 3).erase u ∧ M.card = 6 ∧ OutEq 1 D M := by
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hUc : U.card = (ball D V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hminU : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hm (by
      change 2 + (ball D V u 4 \ ball D V u 3).card ≤ 6; omega)
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hm v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  exact six_cycle_in_two_core (hf.mono_set hUV) hminU hHU hhigh
    (by change 13 ≤ H.card; omega) (by change U.card ≤ 18; omega)

theorem six_cycle_in_third_ball_of_three_fourth {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hB2 : 8 ≤ (ball D V u 2).card) (hB3 : (ball D V u 3).card ≤ 21)
    (h4 : (ball D V u 4 \ ball D V u 3).card ≤ 3) :
    ∃ M : Finset ℕ, M ⊆ (ball D V u 3).erase u ∧ M.card = 6 ∧ OutEq 1 D M := by
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hUc : U.card = (ball D V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hminU : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hm (by
      change 3 + (ball D V u 4 \ ball D V u 3).card ≤ 6; omega)
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hm v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  exact six_cycle_in_three_core (hf.mono_set hUV) hminU hHU hhigh
    (by change 7 ≤ H.card; omega) (by change U.card ≤ 20; omega)

/-- The only surviving profiles with B4<=23 contain a six-cycle inside B3 minus the root. -/
theorem remaining_six_small_ball_local_cycle {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hp : RemainingSixProfile D V u) (hsmall : (ball D V u 4).card ≤ 23) :
    ∃ M : Finset ℕ, M ⊆ (ball D V u 3).erase u ∧ M.card = 6 ∧ OutEq 1 D M := by
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hpair := hp.first_pair_bounds
  have h3 := hp.third_ge_four
  have h4 := hp.fourth_ge_three
  have ht4 : 4 ≤ (ball D V u 4 \ ball D V u 3).card := by
    by_contra hn
    have := hp.fourth_three_exact (by omega)
    omega
  have ht5 : 5 ≤ (ball D V u 3 \ ball D V u 2).card := by
    by_contra hn
    have := hp.third_four_pair_fifteen (by omega)
    omega
  exact six_cycle_in_small_third_ball hf hu hm (by omega) (by omega) (by omega)

/-- Fourth layer three also places a six-cycle in the third ball. -/
theorem remaining_six_fourth_three_local_cycle {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hp : RemainingSixProfile D V u) (h4 : (ball D V u 4 \ ball D V u 3).card = 3) :
    ∃ M : Finset ℕ, M ⊆ (ball D V u 3).erase u ∧ M.card = 6 ∧ OutEq 1 D M := by
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hpair := hp.first_pair_bounds
  have hb := hp.deficient
  exact six_cycle_in_third_ball_of_three_fourth hf hu hm (by omega) (by omega) (by omega)

end LeanCH.BR.BRsub
