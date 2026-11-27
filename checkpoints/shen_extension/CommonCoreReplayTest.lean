import checkpoints.shen_extension.CommonCoreReplay
import checkpoints.shen_extension.BankRefinementReplayTest

namespace LeanCH.BR.CommonCoreReplayTest
open Finset BRq2 BRq3 BypassRepair BypassBankReplay JointShortcutReplay
open CommonHeadCutReplay CommonCoreReplay BankRefinementReplayTest
set_option linter.unusedTactic false

theorem shared_bounds {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_cert : SelectedParentOrder X m) (_shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_hq : 3≤q) (_none : NoHost q (s-1))
    (_lower : ∀ k,k<s → NoHost q k) : True := by
  replay_ch_typed_families
  check_refinement_count RowCoreBound 2
  replay_ch_typed_families
  check_refinement_count RowCoreBound 2
  trivial

theorem missed_bounds {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_cert : SelectedParentOrder X m) (_miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_hq : 3≤q) (_none : NoHost q (s-1))
    (_lower : ∀ k,k<s → NoHost q k) : True := by
  replay_ch_typed_families
  check_refinement_count RowCoreBound 0
  trivial

#print axioms shared_bounds
#print axioms missed_bounds
end LeanCH.BR.CommonCoreReplayTest
