import checkpoints.shen_extension.PureMiddleFrontier

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

def PureMiddleInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s), ShellBooking t ∧ ∃C A,
      RemainingPayer t C δ cap A ∧ C.card=cutoff p+1 ∧ p.s=cutoff p+2 ∧
      ((exterior F (range p.n) C).card=p.s → 2*(p.s-cutoff p+1)<C.card →
        4*6<3*C.card+6 → (2*p.s-1)*(2*p.s)<(p.s-1)*(2*(p.s+4))+p.s*14 →
        4*(p.s-cutoff p+1)<3*(3*cutoff p+3-2*p.s) → MiddleRows t C)

theorem pure_from_input {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) (afford : 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s) :
    PureMiddleInput p (p.n-((p.s-1)+top)) cap := by
  obtain ⟨F,sub,reg,t,policy,C,A,mark,len,degree⟩ := remaining_from_input bad room reserve afford
  refine ⟨F,sub,reg,t,policy,C,A,mark,len,degree,?_⟩
  intro ew enough margin capacity supply
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have ready : RoutingRoom (cutoff p) p.s (range p.n).card target := by simpa using room.route
  exact pure_middle_rows free reg t policy ready mark ew (by omega) enough margin capacity supply

structure OnPureMiddle (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s →
    PureMiddleInput p (p.n-((p.s-1)+top)) cap

theorem pure_on_bad {p : Input} (bad : Bad p) : OnPureMiddle p := ⟨fun _ _ _ _ _=>pure_from_input bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] pure_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve,afford]) (rule_sets := [CHGraphFamilies])] pure_from_input
attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,width,size,enough,margin,capacity,supply]) (rule_sets := [CHGraphFamilies])] pure_middle_rows
attribute [aesop safe forward (immediate := [free,hq,reg,uv,fits,len,rooted,first,size,ys,thin]) (rule_sets := [CHGraphFamilies])] short_large_second_escape
#print axioms pure_on_bad
#print axioms pure_from_input
end LeanCH.BR.LowShellCycleSelection
