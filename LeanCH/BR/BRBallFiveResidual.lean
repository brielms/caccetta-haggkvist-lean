import LeanCH.BR.BRThresholdDensity
import LeanCH.BR.BRBallFiveEquality

/-! Necessary profiles for the open arbitrary-host Ball(5,5) statement. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BRq4 BR45

theorem no_five_eight_three_three {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 5 D V) (hu : u ∈ V)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 8)
    (h3 : (ball D V u 3 \ ball D V u 2).card = 3)
    (h4 : (ball D V u 4 \ ball D V u 3).card = 3) : False := by
  classical
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase _ (ball_mono_radius (by decide))
  have hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have hminU : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by rw [h4])
  have hhigh : ∀ v ∈ H, 5 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  have hb1 : (ball D V u 1).card = 6 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have hb2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have hb3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have hUc : U.card = 16 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 3) hu)
    change U.card = _ at he
    omega
  have hHc : H.card = 13 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 2) hu)
    change H.card = _ at he
    omega
  exact two_core_sixteen_thirteen_false (hf.mono_set hUV) hminU hHU hhigh hUc hHc

/-- The five numerical possibilities still requiring structural exclusion.
This definition asserts no graph realizing a possibility. -/
def FiveBallProfile (b c t : ℕ) : Prop :=
  (b = 5 ∧ c = 5 ∧ t = 4) ∨ (b = 6 ∧ c = 4 ∧ t = 4) ∨
  (b = 5 ∧ c = 6 ∧ t = 3) ∨ (b = 6 ∧ c = 5 ∧ t = 3) ∨
  (b = 7 ∧ c = 4 ∧ t = 3)

theorem FiveBallProfile.sum {b c t : ℕ} (h : FiveBallProfile b c t) :
    b + c + t = 14 := by
  unfold FiveBallProfile at h
  omega

theorem deficient_five_ball_profile {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 5 D V) (hu : u ∈ V)
    (hsmall : (ball D V u 4).card ≤ 20) :
    FiveBallProfile (ball D V u 2 \ ball D V u 1).card
      (ball D V u 3 \ ball D V u 2).card
      (ball D V u 4 \ ball D V u 3).card := by
  classical
  let b := (ball D V u 2 \ ball D V u 1).card
  let c := (ball D V u 3 \ ball D V u 2).card
  let t := (ball D V u 4 \ ball D V u 3).card
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  let X := outN D V u
  have hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have hb : 5 ≤ b := n2_ge_s (by decide) hf ho hu
  have h1 : (ball D V u 1).card = 6 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have h2 : b + 6 = (ball D V u 2).card := by
    have hh := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
    omega
  have h3 : c + (ball D V u 2).card = (ball D V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have h4 : t + (ball D V u 3).card = (ball D V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hsum : b + c + t = 14 := by
    have hh := card_ball_four_ge_twenty hf hmin hu
    omega
  have ht4 : t ≤ 4 := by
    have hh := card_ball_three_ge_sixteen hf hmin hu
    omega
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHV : H ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase _ (ball_mono_radius (by decide))
  have hUc : U.card = b + c + 5 := by
    have hh := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 3) hu)
    change U.card = _ at hh
    omega
  have hHc : H.card = b + 5 := by
    have hh := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 2) hu)
    change H.card = _ at hh
    omega
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hhigh : ∀ v ∈ H, 5 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hHV hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  have ht3 : 3 ≤ t := by
    by_contra hn
    by_cases ht1 : t ≤ 1
    · have hm : ∀ v ∈ U, 4 ≤ (outN D U v).card :=
        minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by
          change 4 + t ≤ 5
          omega)
      have hs := dt_size (by decide : 1 ≤ 5) (ball_all4 5 (by decide))
        (hf.mono_set hUV) hm hUne
      omega
    · have hm : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
        minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by
          change 3 + t ≤ 5
          omega)
      have hc := mixed_degree_density_of_ball (by decide : 1 ≤ 5)
        (BRq3.ball_all 5 (by decide)) (hf.mono_set hUV) hm hHU hhigh
      have hU17 : U.card = 17 := by omega
      rw [hU17] at hc
      omega
  have hXH : X ⊆ H := by
    change outN D V u ⊆ (ball D V u 2).erase u
    rw [← erase_ball_one_eq_outN hf (by decide) hu]
    exact Finset.erase_subset_erase _ (ball_mono_radius (by decide))
  have hXc : X.card = 5 := ho u hu
  have hhighX : ∀ v ∈ X, 5 ≤ (outN D H v).card := by
    intro v hv
    exact (hmin v (outN_subset hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
        ((mem_ball_one hu).mpr (Or.inr hv))))
  have hc4 : 4 ≤ c := by
    by_contra hn
    by_cases hc1 : c ≤ 1
    · have hm : ∀ v ∈ H, 4 ≤ (outN D H v).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin (by
          change 4 + c ≤ 5
          omega)
      have hs := dt_size (by decide : 1 ≤ 5) (ball_all4 5 (by decide))
        (hf.mono_set hHV) hm hHne
      omega
    by_cases hc2 : c = 2
    · have hm : ∀ v ∈ H, 3 ≤ (outN D H v).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin (by
          change 3 + c ≤ 5
          omega)
      have hs := dt_size (by decide : 1 ≤ 5) (BRq3.ball_all 5 (by decide))
        (hf.mono_set hHV) hm hHne
      omega
    · have hm : ∀ v ∈ H, 2 ≤ (outN D H v).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin (by
          change 2 + c ≤ 5
          omega)
      have hd := two_core_threshold_exit_density (K := ∅) (by decide : 5 ≤ 5)
        (hf.mono_set hHV) hm hXH hhighX (Finset.empty_subset _)
        (by simp)
      simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero, hXc] at hd
      have hH13 : H.card ≤ 13 := by omega
      have hs := Nat.mul_le_mul_left H.card hH13
      nlinarith
  have hrigid : b = 5 → 5 ≤ c := fun he => rigid_s (by decide) hf ho hu he
  change FiveBallProfile b c t
  unfold FiveBallProfile
  omega

/-- The missing structural statement for Ball(5,5), stated on actual digraphs. -/
def FiveBallResidual : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V 5 → OutEq 5 D V →
    ∀ u ∈ V, FiveBallProfile (ball D V u 2 \ ball D V u 1).card
      (ball D V u 3 \ ball D V u 2).card
      (ball D V u 4 \ ball D V u 3).card → False

/-- This is a conditional reduction. No proof of `FiveBallResidual` is asserted. -/
theorem ball_five_of_residual (h : FiveBallResidual) : Ball 5 5 := by
  intro D V hf ho u hu
  change 21 ≤ (ball D V u 4).card
  by_contra hn
  exact h D V hf ho u hu (deficient_five_ball_profile hf ho hu (by omega))

theorem five_residual_of_ball (h : Ball 5 5) : FiveBallResidual := by
  intro D V hf ho u hu hp
  have h1 : (ball D V u 1).card = 6 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have h2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h4 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hs := hp.sum
  have hb : 21 ≤ (ball D V u 4).card := h D V hf ho u hu
  omega

theorem ball_five_iff_residual : Ball 5 5 ↔ FiveBallResidual :=
  ⟨five_residual_of_ball, ball_five_of_residual⟩

end LeanCH.BR.BRsGen
