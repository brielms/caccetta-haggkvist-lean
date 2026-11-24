import LeanCH.BR.BRWeightedArcInverse
import LeanCH.BR.BRWeightedStrictCapstone

/-! Literal CH through an actual arc-critical strict core.
The exclusion supplier is an explicit open proposition, not an axiom. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub Compose.Boundary

def ArcCoreExclusion : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ),
    QFree D V q → SmallerSmallRow q V.card → ArcCritical q D V →
    StrictPositiveRows q D V → False

theorem allSmallRow_of_arcCoreExclusion (hX : ArcCoreExclusion) : AllSmallRow := by
  intro q hq
  by_cases hthree : 3 ≤ q
  · have main : ∀ n : ℕ, ∀ V : Finset ℕ, V.card = n →
        ∀ D : CH.Digraph, QFree D V q → SmallRow q D V := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro V hcard D hf
        have hsmall : SmallerSmallRow q V.card := by
          intro E U hlt hUf
          exact ih U.card (by simpa only [hcard] using hlt) U rfl E hUf
        by_contra hbad
        obtain ⟨E, _, hEf, hcritical, hs, H, hH, hcharges, hbranches⟩ :=
          exists_arc_core_with_charges hsmall hf hbad
        exact hX q hthree E V hEf hsmall hcritical hs
    intro D V hf
    exact main V.card V rfl D hf
  · intro D V hf
    rcases (by omega : q = 1 ∨ q = 2) with rfl | rfl
    · exact smallRow_of_selfDual (selfDual_one hf)
    · exact smallRow_of_selfDual (selfDual_two hf)

theorem caccettaHaggkvist_of_arcCoreExclusion (hX : ArcCoreExclusion) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_allSmallRow (allSmallRow_of_arcCoreExclusion hX)

theorem boundaryRegular_of_arcCore_and_balance (hX : ArcCoreExclusion)
    (hB : PrimeEqualityBalance) {q s : ℕ} (hq : 0 < q) : BoundaryRegular q s :=
  boundaryRegular_of_allSelfDual
    (allSelfDual_of_smallRow_and_balance (allSmallRow_of_arcCoreExclusion hX) hB) hq

end LeanCH.BR.WeightedSD
