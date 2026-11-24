import checkpoints.shen_extension.ProperPrimaryFrontier
import checkpoints.shen_extension.ShortShellSwitchReplay

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen PhysicalCycleStock ExteriorPacking
open CHRuleCatalog

/-- Both counterexample witnesses live on one exact thinning. The marked
old cycle belongs to the original booking. The remaining class belongs to
its particular repaired booking, linked by the labelled switch. -/
def SwitchedInput (p : Input) (cap : ℕ) : Prop :=
  ∃F,(∀a b,F a b=true → p.D a b=true) ∧ OutEq p.s F (range p.n) ∧
    ∃s : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s),∃C,ProperMark s cap C ∧
      ∃t,SwitchStep s t ∧ ∃Y,SwitchedDeficit t Y

theorem switch_from_input {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap) : SwitchedInput p cap := by
  obtain ⟨F,sub,reg,s,C,mark⟩ := proper_from_input bad room
  have ff := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have hr := room.route.growth.2.1
  have hq := room.route.cycle.1
  have gap : p.s-cutoff p+1<p.s-1 := by have := room.route.close; omega
  have lower : MeasuredFloor F (range p.n) 3 (3*p.s) := by
    constructor
    intro v vm
    have := ShellBankOrders.mixed_third ff room.route.growth reg vm
    omega
  obtain ⟨t,step,Y,kept⟩ := switch_frontier s ff reg hq hr room.route.close gap lower
    (by simpa only [card_range] using room.route.small) (nonempty_range_iff.mpr bad.order.ne')
  exact ⟨F,sub,reg,s,C,mark,t,step,Y,kept⟩

structure OnShellSwitch (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap → SwitchedInput p cap

theorem switch_on_bad {p : Input} (bad : Bad p) : OnShellSwitch p := ⟨fun _ _ _ _ _=>switch_from_input bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] switch_on_bad
attribute [aesop safe forward (immediate := [bad,room]) (rule_sets := [CHGraphFamilies])] switch_from_input

#print axioms switch_from_input
#print axioms switch_on_bad
end LeanCH.BR.LowShellCycleSelection
