import LeanCH.BR.BRsubNTC6
import LeanCH.BR.BRsubEqualLayers
import LeanCH.BR.BRsubNearLayers
import LeanCH.BR.BRsubTripleLayers
import LeanCH.BR.BRsubExtraLayers
import LeanCH.BR.BRsubFourthLayer
import LeanCH.BR.BRsubTwoExtraLayers
import LeanCH.BR.BRsubSmallSecond
import LeanCH.BR.BRsubFirstPairDensity
import LeanCH.BR.BRsubNineFive
import LeanCH.BR.BRsubFiveCredit
import LeanCH.BR.BRsubFiveThree
import LeanCH.BR.BRsubEightSeven
import LeanCH.BR.BRsubSixThree
import LeanCH.BR.BRsubHighPair

/-! The checked profile exclusions as an explicit remaining goal for `BR(5,6)`.
No inhabitant of `NTC6Residual` is asserted here. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 Compose.Boundary

/-- Conditions still necessary for a deficient non-tight root after the proved exclusions. -/
structure RemainingSixProfile (E : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop where
  non_tight : ¬ TightRoot E V 6 u
  deficient : (ball E V u 4).card ≤ 24
  fourth_ge_three : 3 ≤ (ball E V u 4 \ ball E V u 3).card
  second_ge_six : 6 ≤ (ball E V u 2 \ ball E V u 1).card
  third_ge_four : 4 ≤ (ball E V u 3 \ ball E V u 2).card
  first_pair_bounds : 13 ≤ (outN E V u).card + (ball E V u 2 \ ball E V u 1).card ∧
    (outN E V u).card + (ball E V u 2 \ ball E V u 1).card ≤ 15
  not_seven_five : ¬ ((outN E V u).card = 7 ∧
    (ball E V u 2 \ ball E V u 1).card = 5)
  equal_pair_profile : (outN E V u).card = 6 →
    (ball E V u 2 \ ball E V u 1).card = 6 →
    (ball E V u 3 \ ball E V u 2).card = 8 ∧
    (ball E V u 4 \ ball E V u 3).card = 3 ∧ (ball E V u 4).card = 24
  third_four_density : (ball E V u 3 \ ball E V u 2).card = 4 →
    let a := (outN E V u).card
    let b := (ball E V u 2 \ ball E V u 1).card
    11 * (a + b) + 7 * a ≤ (a + b) * (a + b)
  five_second_small_first : (outN E V u).card ≤ 8 →
    (ball E V u 2 \ ball E V u 1).card = 5 →
    6 ≤ (ball E V u 3 \ ball E V u 2).card
  fourth_three_exact : (ball E V u 4 \ ball E V u 3).card = 3 →
    (ball E V u 4).card = 24
  not_eight_five : ¬ ((outN E V u).card = 8 ∧
    (ball E V u 2 \ ball E V u 1).card = 5)
  nine_five_profile : (outN E V u).card = 9 →
    (ball E V u 2 \ ball E V u 1).card = 5 →
    (ball E V u 3 \ ball E V u 2).card = 6 ∧
    (ball E V u 4 \ ball E V u 3).card = 3 ∧ (ball E V u 4).card = 24
  not_nine_five : ¬ ((outN E V u).card = 9 ∧
    (ball E V u 2 \ ball E V u 1).card = 5)
  five_three_core : (ball E V u 3 \ ball E V u 2).card = 5 →
    (ball E V u 4 \ ball E V u 3).card = 3 →
    let U := (ball E V u 3).erase u
    let H := (ball E V u 2).erase u
    (∀ v ∈ H, (outN E U v).card = 6 ∧ (inN E U v).card = 5 ∧
      (ball E U v 4).card = 15) ∧
    (∀ v ∈ U \ H, (outN E U v).card = 3)
  first_le_eight : (outN E V u).card ≤ 8
  fourth_three_third_ge_seven : (ball E V u 4 \ ball E V u 3).card = 3 →
    7 ≤ (ball E V u 3 \ ball E V u 2).card
  not_eight_seven : ¬ ((outN E V u).card = 8 ∧
    (ball E V u 2 \ ball E V u 1).card = 7)
  third_four_pair_fifteen : (ball E V u 3 \ ball E V u 2).card = 4 →
    (outN E V u).card + (ball E V u 2 \ ball E V u 1).card = 15
  eight_six_full_parents : (outN E V u).card = 8 →
    (ball E V u 2 \ ball E V u 1).card = 6 →
    2 ≤ ((ball E V u 3 \ ball E V u 2).filter
      (fun v => ∀ w ∈ ball E V u 4 \ ball E V u 3, E v w = true)).card
  eight_six_high_balls : (outN E V u).card = 8 →
    (ball E V u 2 \ ball E V u 1).card = 6 →
    let U := (ball E V u 3).erase u
    let H := (ball E V u 2).erase u
    ∀ v ∈ H, 13 ≤ (ball E U v 4).card ∧ (inN E U v).card ≤ 6

/-- The remaining degree-six obligation, restricted to profiles not yet excluded.
This is a proposition to prove, not an axiom or a completed result. -/
def NTC6Residual : Prop :=
  ∀ E : CH.Digraph, QFree E (Finset.range 31) 5 →
    (∀ v ∈ Finset.range 31, 6 ≤ (outN E (Finset.range 31) v).card) →
    Sat 5 E (Finset.range 31) → ∀ u ∈ Finset.range 31,
      RemainingSixProfile E (Finset.range 31) u → False

/-- The remaining degree-six goal after the equal first pair has been excluded. UNPROVED. -/
def NTC6OtherFirstPairs : Prop :=
  ∀ E : CH.Digraph, QFree E (Finset.range 31) 5 →
    (∀ v ∈ Finset.range 31, 6 ≤ (outN E (Finset.range 31) v).card) →
    Sat 5 E (Finset.range 31) → ∀ u ∈ Finset.range 31,
      RemainingSixProfile E (Finset.range 31) u →
      ¬ ((outN E (Finset.range 31) u).card = 6 ∧
        (ball E (Finset.range 31) u 2 \ ball E (Finset.range 31) u 1).card = 6) → False

/-- Conditional assembly retained to display the structural dependency. -/
theorem ntc6_residual_of_two_extra (htwo : BRsGen.TwoExtraTripleImpossible)
    (hother : NTC6OtherFirstPairs) : NTC6Residual := by
  intro E hf hmin hsat u hu hp
  by_cases hpair : (outN E (Finset.range 31) u).card = 6 ∧
      (ball E (Finset.range 31) u 2 \ ball E (Finset.range 31) u 1).card = 6
  · obtain ⟨h3, h4, _⟩ := hp.equal_pair_profile hpair.1 hpair.2
    exact no_six_six_eight_three_of_two_extra htwo hf hu hmin hpair.1 hpair.2 h3 h4
  · exact hother E hf hmin hsat u hu hp hpair

/-- A deficient `(6,6)` pair forces `(6,6,8,3)`, now excluded below. -/
theorem equal_pair_deficient_profile {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree E V 5) (hsat : Sat 5 E V) (hV : V.card = 31)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (hb4 : (ball E V u 4).card ≤ 24)
    (h1 : (outN E V u).card = 6)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 6) :
    (ball E V u 3 \ ball E V u 2).card = 8 ∧
    (ball E V u 4 \ ball E V u 3).card = 3 ∧ (ball E V u 4).card = 24 := by
  have h4min := fourth_layer_ge_three hf hu hmin hb4
  have hb1 := card_B1 (hf.mono_bound (by decide)) hu
  have hb2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have hb3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
  have hb4sum := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  have h3ge : 8 ≤ (ball E V u 3 \ ball E V u 2).card := by
    by_contra hsmall
    by_cases h3 : (ball E V u 3 \ ball E V u 2).card ≤ 5
    · exact no_first_layers_six_six_small hf hsat hV hmin hu h1 h2 h3
    · by_cases h3eq : (ball E V u 3 \ ball E V u 2).card = 6
      · exact no_first_layers_six_six_six_small hf hsat hV hmin hu h1 h2 h3eq (by omega)
      · exact (deficient_six_six_seven_config hf hu hmin h1 h2 (by omega) hb4).false
  omega

/-- Every equal first pair satisfies the desired radius-four bound. -/
theorem equal_pair_ball_four_ge_twenty_five {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree E V 5) (hsat : Sat 5 E V) (hV : V.card = 31)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (h1 : (outN E V u).card = 6)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 6) :
    25 ≤ (ball E V u 4).card := by
  by_contra hn
  obtain ⟨h3, h4, _⟩ := equal_pair_deficient_profile hf hsat hV hmin hu (by omega) h1 h2
  exact no_six_six_eight_three hf hu hmin h1 h2 h3 h4

/-- The equal first pair no longer remains as an assumption. -/
theorem ntc6_residual_of_other_first_pairs (h : NTC6OtherFirstPairs) : NTC6Residual :=
  ntc6_residual_of_two_extra BRsGen.two_extra_triple_impossible h

/-- Lean supplies every field narrowing the surviving profile. -/
theorem deficient_non_tight_first_pair_bounds {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree E V 5) (hsat : Sat 5 E V) (hV : V.card = 31)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (hnt : ¬ TightRoot E V 6 u) (hb4 : (ball E V u 4).card ≤ 24) :
    13 ≤ (outN E V u).card + (ball E V u 2 \ ball E V u 1).card ∧
    (outN E V u).card + (ball E V u 2 \ ball E V u 1).card ≤ 15 := by
  have h1 := hmin u hu
  have h2 := second_layer_ge_five hf hu hmin hb4
  have h3 := third_layer_ge_four hf hu hmin hb4
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hupper : (outN E V u).card + (ball E V u 2 \ ball E V u 1).card ≤ 15 := by
    by_contra hn
    exact no_four_three_deficient hf hu hmin hb4 (by omega) (by omega)
  refine ⟨?_, hupper⟩
  by_contra hn
  rcases (by omega :
      ((outN E V u).card = 6 ∧ (ball E V u 2 \ ball E V u 1).card = 5) ∨
      ((outN E V u).card = 6 ∧ (ball E V u 2 \ ball E V u 1).card = 6) ∨
      ((outN E V u).card = 7 ∧ (ball E V u 2 \ ball E V u 1).card = 5)) with
    h65 | h66 | h75
  · exact hnt (tight_of_first_pair (by decide : 3 ≤ 6) hf hu hmin h65.1 h65.2)
  · have := equal_pair_ball_four_ge_twenty_five hf hsat hV hmin hu h66.1 h66.2
    omega
  · have := wide_first_ball_four_ge_twenty_five hf hsat hV hmin hu h75.1 h75.2
    omega

/-- Lean supplies every field narrowing the surviving profile. -/
theorem remaining_six_profile {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree E V 5) (hsat : Sat 5 E V) (hV : V.card = 31)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (hnt : ¬ TightRoot E V 6 u) (hb4 : (ball E V u 4).card ≤ 24) :
    RemainingSixProfile E V u := by
  have hpair := deficient_non_tight_first_pair_bounds hf hsat hV hmin hu hnt hb4
  refine ⟨hnt, hb4, fourth_layer_ge_three hf hu hmin hb4,
    second_ge_six_of_first_pair_bounds hf hu hmin hb4 hpair,
    third_layer_ge_four hf hu hmin hb4, hpair, ?_, ?_,
    third_four_first_pair_density_strong hf hu hmin,
    five_second_small_first_third_ge_six hf hu hmin, ?_, ?_, ?_, ?_, ?_,
    first_le_eight_of_first_pair_bounds hf hu hmin hb4 hpair,
    fourth_three_third_ge_seven hf hu hmin hb4,
    fun h => no_eight_seven_deficient hf hu hmin hb4 h.1 h.2, ?_,
    eight_six_two_full_third_parents hf hu hmin hb4,
    eight_six_core_high_balls hf hu hmin hb4⟩
  · rintro ⟨h1, h2⟩
    have := wide_first_ball_four_ge_twenty_five hf hsat hV hmin hu h1 h2
    omega
  · exact equal_pair_deficient_profile hf hsat hV hmin hu hb4
  · intro h4
    apply fourth_three_deficient_exact hf hu hmin ?_ hb4 h4
    have hh := (deficient_non_tight_first_pair_bounds hf hsat hV hmin hu hnt hb4).1
    omega
  · rintro ⟨h1, h2⟩
    exact no_eight_five_deficient hf hu hmin h1 h2 hb4
  · intro h1 h2
    exact nine_five_deficient_profile hf hu hmin h1 h2 hb4
  · rintro ⟨h1, h2⟩
    exact no_nine_five_deficient hf hu hmin h1 h2 hb4
  · intro h3 h4
    apply five_three_core_rigid hf hu hmin ?_ h3 h4
    apply fourth_three_deficient_exact hf hu hmin ?_ hb4 h4
    have hh := (deficient_non_tight_first_pair_bounds hf hsat hV hmin hu hnt hb4).1
    omega
  · intro h3
    by_contra hn
    exact no_third_four_small_first_pair hf hu hmin hb4 h3 (by omega)

/-- The residual goal suffices for the original non-tight cap. -/
theorem ntc6_of_residual (h : NTC6Residual) : NTC6 := by
  intro E hf hmin hsat u hu hnt
  by_contra hb4
  exact h E hf hmin hsat u hu
    (remaining_six_profile hf hsat (Finset.card_range 31) hmin hu hnt (by omega))

/-- The residual reformulation is logically exact, using the checked exclusions. -/
theorem ntc6_iff_residual : NTC6 ↔ NTC6Residual := by
  refine ⟨?_, ntc6_of_residual⟩
  intro h E hf hmin hsat u hu hp
  have := h E hf hmin hsat u hu hp.non_tight
  have := hp.deficient
  omega

/-- The checked path from the remaining profile goal to boundary regularity. -/
theorem br_five_six_of_residual (h : NTC6Residual) : BoundaryRegular 5 6 :=
  br_five_six_of_ntc (ntc6_of_residual h)

theorem ntc6_iff_other_first_pairs : NTC6 ↔ NTC6OtherFirstPairs := by
  refine ⟨?_, fun h => ntc6_of_residual (ntc6_residual_of_other_first_pairs h)⟩
  intro h E hf hmin hsat u hu hp _
  exact ntc6_iff_residual.mp h E hf hmin hsat u hu hp

theorem br_five_six_of_other_first_pairs (h : NTC6OtherFirstPairs) : BoundaryRegular 5 6 :=
  br_five_six_of_residual (ntc6_residual_of_other_first_pairs h)

end LeanCH.BR.BRsub
