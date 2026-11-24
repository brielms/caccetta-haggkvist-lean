import checkpoints.shen_extension.PayIncomingAccounts

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

def ArrivalRoom (q r δ cap : ℕ) : Prop :=
  r≤fullRowFloor q r+(q-3) ∧ fullRowFloor q r≤r-1 ∧ δ+8+cap<3*(r-1)+fullRowFloor q r
instance {q r δ cap} : Decidable (ArrivalRoom q r δ cap) := by unfold ArrivalRoom; infer_instance

def DirectAccountInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s), ShellBooking t ∧ ∃C,
      RemainingPayer t C δ cap ∅ ∧ C.card=cutoff p+1 ∧ p.s=cutoff p+2 ∧ CompleteAccount t C ∅

theorem direct_from_bad {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) (afford : 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s)
    (prices : CompletePriceRoom (cutoff p) p.s)
    (route : ArrivalRoom (cutoff p) p.s (p.n-((p.s-1)+top)) cap) :
    DirectAccountInput p (p.n-((p.s-1)+top)) cap := by
  obtain ⟨F,sub,reg,t,policy,C,A,mark,len,degree,account⟩ := complete_from_bad bad room reserve afford prices
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have ready : RoutingRoom (cutoff p) p.s (range p.n).card target := by simpa using room.route
  have empty := incoming_accounts_paid free reg t policy ready mark account route.1 route.2.1 route.2.2
  subst A
  exact ⟨F,sub,reg,t,policy,C,mark,len,degree,account⟩

structure OnDirectAccount (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s →
    CompletePriceRoom (cutoff p) p.s → ArrivalRoom (cutoff p) p.s (p.n-((p.s-1)+top)) cap →
    DirectAccountInput p (p.n-((p.s-1)+top)) cap
theorem direct_on_bad {p : Input} (bad : Bad p) : OnDirectAccount p := ⟨fun _ _ _ _ _=>direct_from_bad bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] direct_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve,afford,prices,route]) (rule_sets := [CHGraphFamilies])] direct_from_bad
attribute [aesop safe forward (immediate := [free,reg,ready,arrival,length,cheap]) (rule_sets := [CHGraphFamilies])] arrival_reserves_parents
#print axioms direct_from_bad
#print axioms direct_on_bad
end LeanCH.BR.LowShellCycleSelection
