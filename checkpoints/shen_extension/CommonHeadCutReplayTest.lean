import checkpoints.shen_extension.CommonHeadCutReplay
import checkpoints.shen_extension.BankRefinementReplayTest

namespace LeanCH.BR.CommonHeadCutReplayTest
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay JointShortcutReplay
open CommonHeadLastCut CommonHeadCutDepth CommonHeadCutReplay BankRefinementReplayTest
set_option linter.unusedTactic false

/-- The source opens with symbolic q and retains the same pair on a second pass. -/
theorem native_shared {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_cert : SelectedParentOrder X m) (_shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_hq : 3≤q) (_none : NoHost q (s-1)) :
    CommonBank X := by
  replay_ch_typed_families
  check_refinement_goals 1
  check_refinement_count CommonBank 1
  check_refinement_count Assignment 1
  check_refinement_count Branches 1
  check_refinement_count ForkLaw 1
  replay_ch_typed_families
  check_refinement_count ForkLaw 1
  assumption

theorem native_missed {q s n} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_cert : SelectedParentOrder X m) (_miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_hq : 3≤q) (_none : NoHost q (s-1))
    (_order : X.V.card≤n) (_cap : n≤q*s) : True := by
  replay_ch_typed_families
  check_refinement_count CommonBank 0
  check_refinement_count Assignment 0
  check_refinement_count Branches 0
  check_refinement_count ForkLaw 0
  trivial

/-- Two chosen target functions on this one bank. An assignment on a
different labelled bank alone cannot trigger the local payment law. -/
theorem assigned_labels {D V q s p h p' h' f g} (_law : ForkLaw D V q s p h)
    (_f : Assignment D V p h f) (_g : Assignment D V p h g) (_other : Assignment D V p' h' f) :
    (∃ b∈V \ {p,h},(outN D (V \ {p,h}) b).card=s ∧
      2≤(previousBill D (V \ {p,h}) (jointParents D V p h) q f b).card) ∧
    (∃ b∈V \ {p,h},(outN D (V \ {p,h}) b).card=s ∧
      2≤(previousBill D (V \ {p,h}) (jointParents D V p h) q g b).card) := by
  saturate_ch_families
  fail_if_success have : ∃ b∈V \ {p',h'},(outN D (V \ {p',h'}) b).card=s ∧
      2≤(previousBill D (V \ {p',h'}) (jointParents D V p' h') q f b).card := by assumption
  exact ⟨by assumption,by assumption⟩

theorem labelled_depth {D V q s p h f g} (_law : ForkLaw D V q s p h)
    (_f : Assignment D V p h f) (_g : Assignment D V p h g) : True := by
  replay_ch_typed_families
  check_refinement_count Branches 2
  replay_ch_typed_families
  check_refinement_count Branches 2
  trivial

#print axioms labelled_depth
#print axioms native_shared
#print axioms native_missed
#print axioms assigned_labels
end LeanCH.BR.CommonHeadCutReplayTest
