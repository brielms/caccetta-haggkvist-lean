import LeanCH.BR.BRq3Base

/-! Explicit research propositions. Neither has an asserted inhabitant here.
The unrestricted proposition is refuted in BRPersistentHighCounter. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3

def PersistentHighGrowth : Prop :=
  ∀ (D : CH.Digraph) (V H : Finset ℕ) (q : ℕ), 5 ≤ q → QFree D V q →
    (∀ v ∈ V, 2 ≤ (outN D V v).card) → H ⊆ V →
    (∀ v ∈ H, q + 1 ≤ (outN D V v).card) →
    (∀ v ∈ H, (outN D H v).Nonempty) →
    ∀ u ∈ H, q + 11 ≤ (ball D V u 4).card

def DenseHighGrowth : Prop :=
  ∀ (D : CH.Digraph) (V H : Finset ℕ) (q : ℕ), 5 ≤ q → QFree D V q →
    (∀ v ∈ V, 2 ≤ (outN D V v).card) → H ⊆ V →
    (∀ v ∈ H, q + 1 ≤ (outN D V v).card) → (V \ H).card ≤ q →
    ∀ u ∈ H, q + 11 ≤ (ball D V u 4).card

end LeanCH.BR.BRsGen
