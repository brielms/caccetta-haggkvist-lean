import checkpoints.shen_extension.MixedPayerMark
import checkpoints.shen_extension.SwitchFamilyEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

/-- A repaired booking, its physical first-layer payer, and the actual
incoming weak cycles, on an exact thinning of the native graph. -/
def MixedInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s),
      ShellBooking t ∧ ∃C A,MixedPayer t C δ cap A

theorem mixed_from_input {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) : MixedInput p (p.n-((p.s-1)+top)) cap := by
  obtain ⟨F,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have onF : PrimaryRoom (cutoff p) p.s (range p.n).card target g mid top cap := by simpa using room
  obtain ⟨hq,a,b,c,d,e,f,h⟩ := room.route.cycle
  obtain ⟨s⟩ := native_selection free hq reg a b c d e f h
  obtain ⟨t,_,policy⟩ := book_short_shells free reg s room.route.cycle room.route.growth.2.1 room.route.close
  obtain ⟨C,A,mark⟩ := mixed_on_booking free reg ⟨0,mem_range.mpr bad.order⟩ t policy onF reserve
  exact ⟨F,sub,reg,t,policy,C,A,by simpa only [card_range] using mark⟩

structure OnMixedPayer (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → MixedInput p (p.n-((p.s-1)+top)) cap

theorem mixed_on_bad {p : Input} (bad : Bad p) : OnMixedPayer p := ⟨fun _ _ _ _ _=>mixed_from_input bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] mixed_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve]) (rule_sets := [CHGraphFamilies])] mixed_from_input
#print axioms mixed_on_bad
#print axioms mixed_from_input
end LeanCH.BR.LowShellCycleSelection
