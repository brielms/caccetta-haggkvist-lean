import checkpoints.shen_extension.RankedLiveSources

namespace LeanCH.BR.RankedContractionReplayTest
open Finset BRq2 BRq3 WeightedSD Closure CHRuleCatalog RankedContractionEntry

theorem child_on_marks {p : Input} (_bad : Bad p) (_hq : 2≤cutoff p) {a d : ℕ}
    (_av : a∈range p.n) (_dv : d∈range p.n) (_ad : a≠d)
    (_rich : p.s≤(FlatPeelReach.interior p.D (range p.n) (range p.n\{a,d}) (cutoff p-1)).card)
    (_spare : ∀i∈range p.n\{a,d},p.D i a=true → p.D i d=true → p.s<(outN p.D (range p.n) i).card) :
    ∃c : Input,Child p c ∧ Bad c ∧ c.s=p.s ∧ c.n+1=p.n ∧ cutoff c≤cutoff p := by
  replay_ch_typed_families
  have made : Contracted p {a,d} (FlatPeelReach.interior p.D (range p.n) (range p.n\{a,d}) (cutoff p-1)) a := by assumption
  obtain ⟨degree,order,_,qle⟩ := next_size made
  have cut : ({a,d}:Finset ℕ)⊆range p.n := insert_subset _av (singleton_subset_iff.mpr _dv)
  have size := card_sdiff_add_card_eq_card cut
  have off : a∉range p.n\({a,d}:Finset ℕ) := fun ha=>(mem_sdiff.mp ha).2 (mem_insert_self ..)
  rw [card_insert_of_notMem off] at order
  rw [card_range,card_pair _ad] at size
  exact ⟨next made,by assumption,by assumption,degree,by omega,qle⟩

#print axioms child_on_marks

theorem bank_on_any_carrier {p : Input} (_bad : Bad p) {W H : Finset ℕ} {z : ℕ}
    (_offer : Proposal p W H z) :
    ∃c : Input,Child p c ∧ Bad c ∧ c.s=p.s ∧ c.n=(range p.n\W).card+1 ∧ c.n<p.n ∧ cutoff c≤cutoff p := by
  replay_ch_typed_families
  have made : Contracted p W H z := by assumption
  obtain ⟨degree,order,small,limit⟩ := next_size made
  have outside : z∉range p.n\W := fun h=>(mem_sdiff.mp h).2 _offer.rep
  rw [card_insert_of_notMem outside] at order
  exact ⟨next made,by assumption,by assumption,degree,order,small,limit⟩

#print axioms bank_on_any_carrier

/-- The exact predicate used by the capstone must trigger the unit-price law. -/
example {q r : ℕ} {D : CH.Digraph} {V : Finset ℕ} (_hq : 2≤q) (_regular : OutEq r D V) :
    RankedUnitWindow.WindowLaw q r D V := by
  replay_ch_typed_families
  assumption

end LeanCH.BR.RankedContractionReplayTest
