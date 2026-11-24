import checkpoints.shen_extension.CompleteAccount

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

/-- The inequalities compare the score tiers on the marked cycle with
their actual class budgets. Its length will be supplied by descent. -/
def CompletePriceRoom (q r : ℕ) : Prop :=
  2*(r-q+1)<q+1 ∧ 4*6<3*(q+1)+6 ∧
  (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14 ∧
  4*(r-q+1)<3*(3*q+3-2*r) ∧ 4*(r-q+1)<q+1+6
instance {q r} : Decidable (CompletePriceRoom q r) := by unfold CompletePriceRoom; infer_instance

def CompleteAccountInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s),ShellBooking t ∧ ∃C A,
      RemainingPayer t C δ cap A ∧ C.card=cutoff p+1 ∧ p.s=cutoff p+2 ∧ CompleteAccount t C A

theorem complete_from_bad {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) (afford : 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s)
    (prices : CompletePriceRoom (cutoff p) p.s) : CompleteAccountInput p (p.n-((p.s-1)+top)) cap := by
  obtain ⟨F,sub,reg,t,policy,C,A,mark,len,degree⟩ := remaining_from_input bad room reserve afford
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have ready : RoutingRoom (cutoff p) p.s (range p.n).card target := by simpa using room.route
  obtain ⟨enough,margin,capacity,narrow,score⟩ := prices
  have width := remaining_complete free reg t policy ready mark (by omega) (by omega) (by omega) capacity narrow (by omega)
  exact ⟨F,sub,reg,t,policy,C,A,mark,len,degree,complete_account free reg t ready mark width⟩

structure OnCompleteAccount (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s →
    CompletePriceRoom (cutoff p) p.s → CompleteAccountInput p (p.n-((p.s-1)+top)) cap

theorem complete_on_bad {p : Input} (bad : Bad p) : OnCompleteAccount p := ⟨fun _ _ _ _ _=>complete_from_bad bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] complete_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve,afford,prices]) (rule_sets := [CHGraphFamilies])] complete_from_bad
attribute [aesop safe forward (immediate := [free,yv,xv,cx,dag,time,inside,cycleMiss,miss,ret]) (rule_sets := [CHGraphFamilies])] separate_sink_budgets
attribute [aesop safe forward (immediate := [free,hq,reg,uv,first,len,cy,fit,size,ys,zs,same]) (rule_sets := [CHGraphFamilies])] same_exterior_high
attribute [aesop safe forward (immediate := [free,sv,cy,long,sa,xv,path,time]) (rule_sets := [CHGraphFamilies])] missed_cycle_segment
#print axioms complete_from_bad
#print axioms complete_on_bad
end LeanCH.BR.LowShellCycleSelection
