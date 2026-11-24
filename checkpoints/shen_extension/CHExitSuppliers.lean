import checkpoints.shen_extension.ForwardMerge
import checkpoints.shen_extension.RankedMerge
import checkpoints.shen_extension.SharedArcPivotGate

namespace LeanCH.BR.Closure.CHExitSuppliers
open Finset WeightedSD ShortestCycleWeights

/-- Expose the existing chain rule at the existentially packaged native exit. -/
theorem native_chain {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (J : CH.Digraph) (sub : ∀i j,J i j=true → D i j=true)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q J V w i) (C : ℕ→Finset ℕ)
    (inside : C 0⊆V) (room : (C 0).card+1<V.card) (live : (C 0).Nonempty)
    (step : ∀i<q-1,C (i+1)⊆C i ∧ ∀v∈C (i+1),mass V w≤WeightedSD.row q J (C i) w v)
    (bill : mass (C 0) w ≤ q*mass (C (q-1)) w) : ForwardMerge.NativeMergePays q D V :=
  ⟨J,sub,Or.inl (ForwardMerge.pays_of_chain w positive strict C inside room live step bill)⟩

theorem reverse_chain {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (J : CH.Digraph) (sub : ∀i j,J i j=true → D i j=true)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q (fun i j=>J j i) V w i) (C : ℕ→Finset ℕ)
    (inside : C 0⊆V) (room : (C 0).card+1<V.card) (live : (C 0).Nonempty)
    (step : ∀i<q-1,C (i+1)⊆C i ∧ ∀v∈C (i+1),mass V w≤WeightedSD.row q (fun i j=>J j i) (C i) w v)
    (bill : mass (C 0) w ≤ q*mass (C (q-1)) w) : ForwardMerge.NativeMergePays q D V :=
  ⟨J,sub,Or.inr (ForwardMerge.pays_of_chain w positive strict C inside room live step bill)⟩

/-- The same carrier, heads, arc restriction and rational prices must satisfy all three bills. -/
theorem pair {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (U H : Finset ℕ) (E : CH.Digraph) (w : ℕ→ℚ)
    (inside : U⊆V) (room : U.card+1<V.card) (sub : ∀i j,E i j=true → D i j=true)
    (heads : H⊆U) (live : H.Nonempty) (positive : ∀i∈U,0<w i)
    (headBill : mass U w < q*mass H w)
    (inner : ∀i∈BRsub.ballSet E U H (q-2),mass U w < WeightedSD.row q E U w i)
    (outer : ∀i∈BRsub.ballSet E U H (q-2),∀j∈U\BRsub.ballSet E U H (q-2),
      mass U w≤(q-1:ℚ)*(WeightedSD.row q E U w i-mass U w)+WeightedSD.row q E U w j) :
    RankedMerge.PairPays q D V :=
  ⟨U,inside,room,E,sub,H,heads,live,w,positive,headBill,fun i hi=>⟨inner i hi,outer i hi⟩⟩
end LeanCH.BR.Closure.CHExitSuppliers
