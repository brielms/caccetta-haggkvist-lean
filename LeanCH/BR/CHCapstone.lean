import LeanCH.BR.BR55Consequences
import LeanCH.BR.BR75
import LeanCH.BR.BRq5All
import LeanCH.BR.BRHalfBallWindowCap
import LeanCH.BR.BR96
import LeanCH.BR.BR76Residual
import LeanCH.BR.BRSecondBallBoundary
import LeanCH.BR.BRDenseHighReduction
import LeanCH.BR.BRHighPairFour
import LeanCH.BR.BRCapstone
import LeanCH.BR.BR45
import LeanCH.BR.BRsubNTC6Assembly
import LeanCH.BR.BRsubLocalSix
import LeanCH.BR.BRModuleLayers
import LeanCH.BR.BRModuleCover
import LeanCH.BR.BRModuleReach
import LeanCH.BR.BRsubCycleReturn
import LeanCH.BR.BRsubFirstReturn
import LeanCH.BR.BRAlternatingSubstitution
import LeanCH.BR.BRCompensatedCounter
import LeanCH.BR.BRWeightedSDBridge
import LeanCH.BR.BRWeightedSupport
import LeanCH.BR.BRWeightedCritical
import LeanCH.BR.BRClosedNeighborhoodRepair
import LeanCH.BR.BRWeightedCases
import LeanCH.BR.BRWeightedTwoSided
import LeanCH.BR.BRWeightedPrefixControl
import LeanCH.BR.BRWeightedDualReceiver
import LeanCH.BR.BRWeightedCutInverse
import LeanCH.BR.BRWeightedStrictCapstone
import LeanCH.BR.BRSerialChain
import LeanCH.BR.BRWeightedArcCapstone
import LeanCH.BR.BRWeightedInverseComparison
import LeanCH.BR.BRWeightedDeletionThreshold
import LeanCH.BR.BRWeightedCycleStructure
import LeanCH.BR.BRWeightedThirdExterior
import LeanCH.BR.BRWeightedEqualityCycle
import LeanCH.BR.BRWeightedGapDischarge
import LeanCH.BR.BRWeightedCycleSenderFamily
import LeanCH.BR.BRWeightedEqualityInterface
import LeanCH.BR.BRWeightedLayerDefect
import LeanCH.BR.BR37
import LeanCH.BR.BR36Disc

/-!
The active assembly has the literal `CH.CaccettaHaggkvistConjecture` as its conclusion.
`OpenBoundaryGoals` records its unproved inputs. It has no asserted inhabitant.
The assembly uses the proved cases and the new profile exclusions.
-/

namespace LeanCH.BR.CHCapstone

open BRq2 BRq3 BR45 BRsub Compose.Boundary

/-- The positive-parameter cases with cutoff one are already elementary. -/
theorem br_cutoff_one (s : ℕ) : BoundaryRegular 1 s := by
  apply br_of_ball (by decide)
  intro D W hf hout u hu
  change 1 ≤ (ball D W u 0).card
  exact Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩

/-- The positive-parameter cases with cutoff two are already elementary. -/
theorem br_cutoff_two (s : ℕ) : BoundaryRegular 2 s := by
  apply br_of_ball (by decide)
  intro D W hf hout u hu
  simp only [Nat.reduceSub, Nat.mul_one]
  classical
  have heq : ball D W u 1 = insert u (outN D W u) := by
    ext v
    simp only [mem_ball_one hu, Finset.mem_insert]
  have hnot : u ∉ outN D W u :=
    fun h => loopfree hf (by decide) hu (mem_outN.mp h).2
  rw [heq, Finset.card_insert_of_notMem hnot, hout u hu]

/-- The three unproved families on the current boundary-regularity route.
These fields are proof obligations, not axioms. Supplying this structure would close literal CH.
The off-subdiagonal field is below Shen's window. It remains infinite as s varies. -/
structure OpenBoundaryGoals : Prop where
  nonTightSix : NTC6OtherFirstPairs
  higherSubdiagonal : ∀ s, 7 ≤ s → SC s
  otherParameters : ∀ q s, 3 ≤ q → 6 ≤ s →
    q < 2 * s - 2 → (q = 3 → 8 ≤ s) → (s = 6 → q ≤ 5) →
      q + 1 ≠ s → BoundaryRegular q s

/-- Boundary regularity in the residual parameter range follows from the remaining goals.
Every degree through five, the triangle cases, and the solved degree-six profiles are used here. -/
theorem boundaryRegular_of_remaining (h : OpenBoundaryGoals) :
    ∀ q s, 0 < q → 0 < s → q < 2 * s - 2 → (s = 6 → q ≤ 5) → BoundaryRegular q s := by
  intro q s hq hs hwindow hsix
  by_cases hq1 : q = 1
  · subst q
    exact br_cutoff_one s
  by_cases hq2 : q = 2
  · subst q
    exact br_cutoff_two s
  have hq3 : 3 ≤ q := by omega
  by_cases hs4 : s ≤ 4
  · rcases (by omega : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4) with rfl | rfl | rfl | rfl
    · exact BR45.br_q_one q hq
    · exact BRq2.br_q_two q hq
    · exact BRq3.br_q_three q hq
    · by_cases hqeq : q = 3
      · subst q
        exact BR34.br_four
      · exact BRq4.br_q_four q (by omega)
  by_cases hs5 : s = 5
  · subst s
    exact BRq5.br_q_five q hq
  have hs6 : 6 ≤ s := by omega
  by_cases ht : q = 3 ∧ s ≤ 7
  · obtain ⟨rfl, hs7⟩ := ht
    rcases (by omega : s = 6 ∨ s = 7) with rfl | rfl
    · exact BR36.br_six
    · exact BR37.br_seven
  by_cases hsub : q + 1 = s
  · by_cases hs6 : s = 6
    · have hq5 : q = 5 := by omega
      subst q
      subst s
      exact br_five_six_of_other_first_pairs h.nonTightSix
    · have hs7 : 7 ≤ s := by omega
      have hqs : q = s - 1 := by omega
      rw [hqs]
      exact br_of_sc (by omega) (h.higherSubdiagonal s hs7)
  · exact h.otherParameters q s hq3 hs6 hwindow (by omega) hsix hsub

/-- The literal full CH target, conditional on the explicitly named open goals.
This is not an unconditional proof of the conjecture. -/
theorem caccettaHaggkvist_of_remaining (h : OpenBoundaryGoals) :
    CH.CaccettaHaggkvistConjecture := by
  intro n s G hn hs hloop hdeg
  have hnq : n ≤ CH.ceilDiv n s * s := by
    have hmod := Nat.mod_lt (n + s - 1) hs
    have hdiv := Nat.mod_add_div (n + s - 1) s
    rw [Nat.mul_comm s] at hdiv
    unfold CH.ceilDiv
    omega
  have hq : 0 < CH.ceilDiv n s := by
    by_contra hh
    have hz : CH.ceilDiv n s = 0 := by omega
    rw [hz, Nat.zero_mul] at hnq
    omega
  by_cases hsixhigh : s = 6 ∧ 6 ≤ CH.ceilDiv n s
  · obtain ⟨rfl, hcut⟩ := hsixhigh
    exact BRq6.ch_six_high_cutoff hcut hn hnq hloop hdeg
  by_cases hs3 : 3 ≤ s
  · by_cases hregular : 2 * s - 1 ≤ CH.ceilDiv n s
    · exact ch_of_boundaryRegular hs (BRsGen.br_in_window hs3 hregular) hn hnq hloop hdeg
    by_cases hwindow : 2 * s - 2 ≤ CH.ceilDiv n s
    · exact BRsGen.ch_in_window (by omega) hwindow hn hnq hloop hdeg
    exact ch_of_boundaryRegular hs
      (boundaryRegular_of_remaining h _ _ hq hs (by omega) (by omega)) hn hnq hloop hdeg
  · rcases (by omega : s = 1 ∨ s = 2) with rfl | rfl
    · exact ch_of_boundaryRegular (by decide) (BR45.br_q_one _ hq) hn hnq hloop hdeg
    · exact ch_of_boundaryRegular (by decide) (BRq2.br_q_two _ hq) hn hnq hloop hdeg

/-- Under the proposed dense-high bound, every remaining profile has first layer at most seven.
The growth input is explicitly conditional; this does not exclude `(8,6)` unconditionally. -/
theorem first_le_seven_of_dense_growth (hgrowth : BRsGen.DenseHighGrowth)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hp : RemainingSixProfile D V u) : (outN D V u).card ≤ 7 := by
  by_contra hn
  have hfirst : (outN D V u).card = 8 := by
    have hh := hp.first_le_eight
    omega
  have hsecond : (ball D V u 2 \ ball D V u 1).card = 6 := by
    have hlo := hp.second_ge_six
    have hhi := hp.first_pair_bounds.2
    have hne := hp.not_eight_seven
    omega
  exact no_eight_six_of_dense_growth hgrowth hf hu hmin hp.deficient hfirst hsecond

/-- The numerical possibilities conditional on dense-high growth; no existence is claimed. -/
theorem first_pair_options_of_dense_growth (hgrowth : BRsGen.DenseHighGrowth)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hp : RemainingSixProfile D V u) :
    ((outN D V u).card = 6 ∧
      ((ball D V u 2 \ ball D V u 1).card = 7 ∨
       (ball D V u 2 \ ball D V u 1).card = 8 ∨
       (ball D V u 2 \ ball D V u 1).card = 9)) ∨
    ((outN D V u).card = 7 ∧
      ((ball D V u 2 \ ball D V u 1).card = 6 ∨
       (ball D V u 2 \ ball D V u 1).card = 7 ∨
       (ball D V u 2 \ ball D V u 1).card = 8)) := by
  have hfirst := first_le_seven_of_dense_growth hgrowth hf hu hmin hp
  have hlo := hmin u hu
  have hpairs := hp.first_pair_bounds
  omega

/-- The six first pairs left after a hypothetical proof of DenseHighGrowth.
This proposition has no asserted inhabitant. -/
def NTC6FirstAtMostSeven : Prop :=
  ∀ E : CH.Digraph, QFree E (Finset.range 31) 5 →
    (∀ v ∈ Finset.range 31, 6 ≤ (outN E (Finset.range 31) v).card) →
    Sat 5 E (Finset.range 31) → ∀ u ∈ Finset.range 31,
      RemainingSixProfile E (Finset.range 31) u →
      ¬ ((outN E (Finset.range 31) u).card = 6 ∧
        (ball E (Finset.range 31) u 2 \ ball E (Finset.range 31) u 1).card = 6) →
      (outN E (Finset.range 31) u).card ≤ 7 → False

/-- A checked adapter from the new mathematical probe to the established degree-six interface. -/
theorem other_first_pairs_of_dense_growth (hgrowth : BRsGen.DenseHighGrowth)
    (hremaining : NTC6FirstAtMostSeven) : NTC6OtherFirstPairs := by
  intro E hf hmin hsat u hu hp hne
  exact hremaining E hf hmin hsat u hu hp hne
    (first_le_seven_of_dense_growth hgrowth hf hu hmin hp)

/-- Alternative full-CH goals exposing dense-high growth on the literal capstone path.
Every field remains an unproved obligation; there is no asserted inhabitant. -/
structure DenseBoundaryGoals : Prop where
  denseHighGrowth : BRsGen.DenseHighGrowth
  firstAtMostSeven : NTC6FirstAtMostSeven
  higherSubdiagonal : ∀ s, 7 ≤ s → SC s
  otherParameters : ∀ q s, 3 ≤ q → 6 ≤ s →
    q < 2 * s - 2 → (q = 3 → 8 ≤ s) → (s = 6 → q ≤ 5) →
      q + 1 ≠ s → BoundaryRegular q s

/-- All four inputs of the alternate interface are passed to the original capstone. -/
theorem remaining_of_dense_remaining (h : DenseBoundaryGoals) : OpenBoundaryGoals where
  nonTightSix := other_first_pairs_of_dense_growth h.denseHighGrowth h.firstAtMostSeven
  higherSubdiagonal := h.higherSubdiagonal
  otherParameters := h.otherParameters

/-- Literal full CH conditional on the four explicit dense-route goals, all still unproved. -/
theorem caccettaHaggkvist_of_dense_remaining (h : DenseBoundaryGoals) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_remaining (remaining_of_dense_remaining h)

/-- Historical stronger interface, retained for callers. The five-profile input
is no longer needed for any BR(q,5), all of which close in the main capstone.
The remaining parameter field is still infinite. No inhabitant is asserted. -/
structure FiveBallBoundaryGoals : Prop where
  fiveBallResidual : BRsGen.FiveBallResidual
  nonTightSix : NTC6OtherFirstPairs
  higherSubdiagonal : ∀ s, 7 ≤ s → SC s
  otherParameters : ∀ q s, 3 ≤ q → 5 ≤ s →
    (q = 3 → 8 ≤ s) → (q = 4 → 6 ≤ s) → (q = 5 → 6 ≤ s) → (q = 6 → 6 ≤ s) →
      (q = 7 → 6 ≤ s) → q + 1 ≠ s → BoundaryRegular q s

theorem remaining_of_five_ball_remaining (h : FiveBallBoundaryGoals) : OpenBoundaryGoals where
  nonTightSix := h.nonTightSix
  higherSubdiagonal := h.higherSubdiagonal
  otherParameters := fun q s hq hs _hwindow htri _hsix hsub =>
    h.otherParameters q s hq (by omega) htri (by omega) (by omega) (by omega) (by omega) hsub

/-- Historical conditional interface; the extra five-profile input is now unnecessary. -/
theorem caccettaHaggkvist_of_five_ball_remaining (h : FiveBallBoundaryGoals) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_remaining (remaining_of_five_ball_remaining h)

/-- A stronger interface retained for the seven-free structural probe.
Its three-profile input is unnecessary for literal CH at cutoff seven, now closed.
No inhabitant of this structure is asserted. -/
structure SevenSixBoundaryGoals : Prop where
  sevenSixResidual : BRq6.SevenFreeFourBallResidual
  nonTightSix : NTC6OtherFirstPairs
  higherSubdiagonal : ∀ s, 7 ≤ s → SC s
  otherParameters : ∀ q s, 3 ≤ q → 6 ≤ s →
    q < 2 * s - 2 → (q = 3 → 8 ≤ s) → (s = 6 → q ≤ 5) →
      q + 1 ≠ s → BoundaryRegular q s

theorem remaining_of_seven_six_remaining (h : SevenSixBoundaryGoals) : OpenBoundaryGoals where
  nonTightSix := h.nonTightSix
  higherSubdiagonal := h.higherSubdiagonal
  otherParameters := h.otherParameters

/-- Historical stronger supplier; the extra seven-free profile premise is now unnecessary. -/
theorem caccettaHaggkvist_of_seven_six_remaining (h : SevenSixBoundaryGoals) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_remaining (remaining_of_seven_six_remaining h)

/-- Alternative literal-CH obligations using the proved global module count at degree six.
The module-cover supplier and both higher-parameter families are unproved. -/
structure ModuleCoverBoundaryGoals : Prop where
  moduleCover : SixModuleCover
  higherSubdiagonal : ∀ s, 7 ≤ s → SC s
  otherParameters : ∀ q s, 3 ≤ q → 6 ≤ s →
    q < 2 * s - 2 → (q = 3 → 8 ≤ s) → (s = 6 → q ≤ 5) →
      q + 1 ≠ s → BoundaryRegular q s

theorem remaining_of_module_cover_remaining (h : ModuleCoverBoundaryGoals) : OpenBoundaryGoals where
  nonTightSix := ntc6_other_of_module_cover h.moduleCover
  higherSubdiagonal := h.higherSubdiagonal
  otherParameters := h.otherParameters

/-- Literal full CH with module coverage explicitly retained as an unproved input. -/
theorem caccettaHaggkvist_of_module_cover_remaining (h : ModuleCoverBoundaryGoals) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_remaining (remaining_of_module_cover_remaining h)

end LeanCH.BR.CHCapstone
