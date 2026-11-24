import LeanCH.BR.BRExtraTriple

/-! A larger structural conjecture stated before it is proved.
Neither target proposition below is asserted. The forced-return direction is proved. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3

/-- Local hypotheses for the first unequal third-layer problem. -/
structure OneExtraTriple (D : CH.Digraph) (X Y Z : Finset ℕ) (s : ℕ) : Prop where
  large : 6 ≤ s
  free : QFree D (X ∪ Y ∪ Z) (s - 1)
  disjoint_first : Disjoint X Y
  disjoint_third : Disjoint (X ∪ Y) Z
  card_first : X.card = s
  card_second : Y.card = s
  card_third : Z.card = s + 1
  high_first : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card
  high_second : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card
  low_third : ∀ z ∈ Z, 2 ≤ (outN D (X ∪ Y ∪ Z) z).card
  parents : ∀ z ∈ Z, ∃ y ∈ Y, D y z = true

/-- Research target: every such unequal triple is impossible, uniformly in s. UNPROVED. -/
def OneExtraTripleImpossible : Prop :=
  ∀ s D X Y Z, OneExtraTriple D X Y Z s → False

/-- A sufficient structural target: no third-to-first arc can occur. UNPROVED. -/
def OneExtraReturnExcluded : Prop :=
  ∀ s D X Y Z, OneExtraTriple D X Y Z s →
    ∀ z ∈ Z, ∀ a ∈ X, ¬ D z a = true

/-- This direction of the attack is proved: a return is forced. -/
theorem OneExtraTriple.forced_return {s D X Y Z} (h : OneExtraTriple D X Y Z s) :
    ∃ z ∈ Z, ∃ a ∈ X, D z a = true :=
  one_extra_has_first_return h.large h.free h.disjoint_first h.disjoint_third
    h.card_first h.card_second h.card_third h.high_first h.high_second h.low_third h.parents

/-- Lean reduces the larger conjecture exactly to excluding the forced return. -/
theorem one_extra_impossible_iff_return_excluded :
    OneExtraTripleImpossible ↔ OneExtraReturnExcluded := by
  refine ⟨?_, ?_⟩
  · intro h s D X Y Z hc
    exact (h s D X Y Z hc).elim
  · intro h s D X Y Z hc
    obtain ⟨z, hz, a, ha, hza⟩ := hc.forced_return
    exact h s D X Y Z hc z hz a ha hza

end LeanCH.BR.BRsGen
