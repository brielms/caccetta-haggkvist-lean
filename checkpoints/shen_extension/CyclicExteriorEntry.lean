import checkpoints.shen_extension.ExteriorSinkPayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog
open scoped Classical

def CyclicExteriorInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s), ShellBooking t ∧ ∃C,
      RemainingPayer t C δ cap ∅ ∧ C.card=cutoff p+1 ∧ p.s=cutoff p+2 ∧
      CompleteAccount t C ∅ ∧ ∀x∈exterior F (range p.n) C,Rooted F (range p.n) x (exterior F (range p.n) C)

theorem rooted_direct_exterior {D V q r C target δ cap} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap ∅) (account : CompleteAccount t C ∅)
    (length : C.card=q+1) (degree : r=q+2) (prices : CompletePriceRoom q r) :
    ∀x∈exterior D V C,Rooted D V x (exterior D V C) := by
  obtain ⟨enough,_,capacity,reserve,_⟩ := prices
  have hq := ready.cycle.1
  have width := account.width
  have sub : exterior D V C⊆V := by
    intro z zm
    obtain ⟨a,_,az⟩ := mem_biUnion.mp (mem_sdiff.mp zm).1
    exact outN_subset az
  have all := direct_exterior_no_sink free reg t policy ready mark account (by omega) (by omega) (by omega) capacity (by omega)
  exact fun x xm=>ShellCycleSupply.rooted_on_small_set free (by omega) sub (by omega) (fun e em=>by
    obtain ⟨z,zm,az⟩ := all e em
    exact card_pos.mpr ⟨z,mem_outN.mpr ⟨zm,az⟩⟩) xm

theorem cyclic_exterior_from_direct {p : Input} {δ cap target} (bad : Bad p)
    (direct : DirectAccountInput p δ cap) (ready : RoutingRoom (cutoff p) p.s p.n target)
    (prices : CompletePriceRoom (cutoff p) p.s) : CyclicExteriorInput p δ cap := by
  obtain ⟨F,sub,reg,t,policy,C,mark,length,degree,account⟩ := direct
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  exact ⟨F,sub,reg,t,policy,C,mark,length,degree,account,rooted_direct_exterior free reg t policy
    (by simpa using ready) mark account length degree prices⟩

structure OnCyclicExterior (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s →
    CompletePriceRoom (cutoff p) p.s → ArrivalRoom (cutoff p) p.s (p.n-((p.s-1)+top)) cap →
    CyclicExteriorInput p (p.n-((p.s-1)+top)) cap

theorem cyclic_exterior_on_bad {p : Input} (bad : Bad p) : OnCyclicExterior p :=
  ⟨fun _ _ _ _ _ room reserve afford prices route=>cyclic_exterior_from_direct bad
    (direct_from_bad bad room reserve afford prices route) room.route prices⟩

attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,account,length,degree,prices]) (rule_sets := [CHGraphFamilies])] rooted_direct_exterior
attribute [aesop safe forward (immediate := [bad,direct,ready,prices]) (rule_sets := [CHGraphFamilies])] cyclic_exterior_from_direct
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] cyclic_exterior_on_bad
#print axioms rooted_direct_exterior
#print axioms cyclic_exterior_from_direct
#print axioms cyclic_exterior_on_bad
end LeanCH.BR.LowShellCycleSelection
