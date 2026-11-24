import checkpoints.shen_extension.RootFirstArcReturns

namespace LeanCH.BR.Closure.FirstArcRecurrence
open Finset BRq2 BRq3 BR45 DeficitLevels RootFirstArcReturns

/-- Every proper nonempty family of roots closed under continuing at any
certified first arc contains a vertex whose original degrees satisfy the
displayed bound. It applies to any period and to a closed component. -/
theorem closed_component {s} (O : Origin 3 s) (laws : ∀j<s, OrderLaw 3 j (3*j+1))
    {C : Finset ℕ} (cv : C⊆O.V) (proper : C.card<O.V.card) (live : C.Nonempty)
    (closed : ∀h∈C, firstArcs O.G O.V h s⊆C) :
    ∃h∈C, 3*((outN O.G O.V h).card-s)+3*(((inN O.G O.V h).card+2)/3)+1≤C.card := by
  obtain ⟨h,hc,light⟩ := PaidLayerDescent.light O laws cv proper live
  have le := first_arc_bound O (cv hc)
  have inc : firstArcs O.G O.V h s⊆outN O.G C h := by
    intro a ha
    have old := (mem_filter.mp ha).1
    exact mem_outN.mpr ⟨closed h hc ha,(mem_outN.mp old).2⟩
  have cnt := card_le_card inc
  exact ⟨h,hc,by omega⟩

/-- The sum counts distinct ordered arcs, each carrying an actual original
four-cycle by cycle_of_mem. -/
theorem arc_share {s} (O : Origin 3 s) :
    (∑h∈O.V,(outN O.G O.V h).card) ≤ 3*(∑h∈O.V,(firstArcs O.G O.V h s).card) := by
  have per (h) (hv : h∈O.V) : (inN O.G O.V h).card≤3*(firstArcs O.G O.V h s).card := by
    have le := first_arc_bound O hv
    omega
  have total := sum_le_sum per
  rw [←mul_sum] at total
  have eq : (∑h∈O.V,(outN O.G O.V h).card)=(∑h∈O.V,(inN O.G O.V h).card) := by
    simp only [inN,outN,card_filter]
    exact sum_comm
  exact eq.trans_le total

#print axioms closed_component
#print axioms arc_share
end LeanCH.BR.Closure.FirstArcRecurrence
