import LeanCH.BR.BRSmallHighCycle
import LeanCH.BR.BRHighTwoGrowth

/-! Sharp ball growth already starts at root degree q, one below the previous threshold. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem threshold_first_second_ge {D : CH.Digraph} {V : Finset ℕ} {u q d : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = q) :
    d ≤ (ball D V u 2 \ ball D V u 1).card := by
  by_contra hn
  have hm := minOut_prefix_erase (d := 1) hf hu (by omega : 1 + 1 ≤ q) hmin (by
    change 1 + (ball D V u 2 \ ball D V u 1).card ≤ d; omega)
  rw [erase_ball_one_eq_outN hf (by omega) hu] at hm
  have hh := dt_size (by omega : 1 ≤ q) (ball_q_one q (by omega)) (hf.mono_set outN_subset) hm
    (Finset.card_pos.mp (by omega : 0 < (outN D V u).card))
  omega

theorem threshold_ball_three_min {D : CH.Digraph} {V : Finset ℕ} {u q d : ℕ}
    (hd : 2 ≤ d) (hqd : 2 * d ≤ q + 1) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card) (hu : u ∈ V)
    (hhigh : q ≤ (outN D V u).card) :
    q + 2 * d + 1 ≤ (ball D V u 3).card := by
  by_cases hmore : q + 1 ≤ (outN D V u).card
  · exact high_row_ball_three_min hd hqd hf hmin hu hmore
  have hdegree : (outN D V u).card = q := by omega
  have hYlo := threshold_first_second_ge (by omega) hf hmin hu hdegree
  classical
  by_contra hn
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let A := (ball D V u 2).erase u
  have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXA : X ⊆ A := by
    change outN D V u ⊆ (ball D V u 2).erase u
    rw [← erase_ball_one_eq_outN hf (by omega) hu]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXc : X.card = q := hdegree
  have hAne : A.Nonempty := (Finset.card_pos.mp (by omega : 0 < X.card)).mono hXA
  have hB1 : (ball D V u 1).card = q + 1 := by
    have hh := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by omega) hu, hdegree] at hh
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 : Y.card + (ball D V u 1).card = (ball D V u 2).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have h23 : Z.card + (ball D V u 2).card = (ball D V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hAc : A.card = (ball D V u 2).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  change d ≤ Y.card at hYlo
  have hhighX : ∀ v ∈ X, d ≤ (outN D A v).card := by
    intro v hv
    exact (hmin v (outN_subset hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q)
        ((mem_ball_one hu).mpr (Or.inr hv))))
  have hZeq : Z.card + 1 = d := by
    by_contra hz
    have hm : ∀ v ∈ A, 2 ≤ (outN D A v).card :=
      minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin (by
        change 2 + Z.card ≤ d; omega)
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set hAV) hm hAne
    omega
  have hYeq : Y.card = d := by omega
  have hAeq : A.card = q + d := by omega
  have hm : ∀ v ∈ A, 1 ≤ (outN D A v).card :=
    minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin (by
      change 1 + Z.card ≤ d; omega)
  by_cases hd3 : 3 ≤ d
  · have hh := small_one_high_degree_count (by omega) hd3 (by omega)
      (hf.mono_set hAV) hAeq hm hXA hhighX
    omega
  · have hd2 : d = 2 := by omega
    have hh := small_one_core_high_count (by omega) (hf.mono_set hAV) hm hAne
      (by omega) hXA (fun v hv => by have hh := hhighX v hv; omega)
    omega

theorem threshold_two_ball_four {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hu : u ∈ V) (hhigh : q ≤ (outN D V u).card) :
    q + 7 ≤ (ball D V u 4).card := by
  by_cases hmore : q + 1 ≤ (outN D V u).card
  · exact high_two_ball_four hq hf hmin hu hmore
  have hdegree : (outN D V u).card = q := by omega
  have hY := threshold_first_second_ge (by omega) hf hmin hu hdegree
  have hB3 := threshold_ball_three_min (by decide : 2 ≤ 2) (by omega) hf hmin hu hhigh
  classical
  by_contra hn
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  let T := ball D V u 4 \ ball D V u 3
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXH : outN D V u ⊆ H := by
    change outN D V u ⊆ (ball D V u 2).erase u
    rw [← erase_ball_one_eq_outN hf (by omega) hu]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hne : U.Nonempty :=
    (Finset.card_pos.mp (by omega : 0 < (outN D V u).card)).mono (hXH.trans hHU)
  have hUc : U.card = (ball D V u 3).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hB1 : (ball D V u 1).card = q + 1 := by
    have hh := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by omega) hu, hdegree] at hh
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h34 : T.card + (ball D V u 3).card = (ball D V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hTcap : T.card ≤ 1 := by omega
  have hTpos : 1 ≤ T.card := by
    by_contra ht
    have hm : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
      minOut_prefix_erase hf hu (by omega : 3 + 1 ≤ q) hmin (by
        change 2 + T.card ≤ 2; omega)
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set hUV) hm hne
    omega
  have hm : ∀ v ∈ U, 1 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : 3 + 1 ≤ q) hmin (by
      change 1 + T.card ≤ 2; omega)
  have hhH : ∀ v ∈ H, 2 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 2 + 1 ≤ q) (Finset.mem_of_mem_erase hv)))
  have hc := small_one_core_high_count (by omega) (hf.mono_set hUV) hm hne
    (by omega : U.card ≤ 2 * q) hHU hhH
  omega

theorem threshold_two_predecessor_four {D : CH.Digraph} {V : Finset ℕ} {u v q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 2 ≤ (outN D V x).card)
    (hu : u ∈ V) (hv : v ∈ outN D V u) (hhigh : q ≤ (outN D V v).card) :
    q + 6 ≤ (ball D V u 4).card := by
  classical
  have hvV := outN_subset hv
  have hB3 := threshold_ball_three_min (by decide : 2 ≤ 2) (by omega) hf hmin hvV hhigh
  have hnot : u ∉ ball D V v 3 := fun h => no_back_arc hf hvV h (by omega) (mem_outN.mp hv).2
  have hsub : insert u (ball D V v 3) ⊆ ball D V u 4 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact self_mem_ball hu
    · exact ball_trans ((mem_ball_one hu).mpr (Or.inr hv)) hx
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hc
  omega

end LeanCH.BR.BRsGen
