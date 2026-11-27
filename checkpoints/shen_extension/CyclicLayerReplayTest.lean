import checkpoints.shen_extension.CyclicLayerReplay
import checkpoints.shen_extension.CommonHeadCutReplayTest

namespace LeanCH.BR.CyclicLayerReplayTest
open Finset BRq2 BRq3 BypassRepair BypassBankReplay JointShortcutReplay
open CommonHeadCutReplay CyclicLayerReplay
set_option linter.unusedTactic false

theorem shared {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_cert : SelectedParentOrder X m) (_shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_hs2 : 2≤s) (_hq : 3≤q)
    (_none : NoHost q (s-1)) (_lower : ∀ t, t<s → NoHost q t) : True := by
  replay_ch_typed_families
  check_refinement_count CountedBank 1
  check_refinement_count Representatives 1
  check_refinement_count Budget 1
  replay_ch_typed_families
  check_refinement_count Budget 1
  trivial

theorem missed {q s n} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_cert : SelectedParentOrder X m) (_miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_hs2 : 2≤s) (_hq : 3≤q)
    (_none : NoHost q (s-1)) (_lower : ∀ t, t<s → NoHost q t)
    (_order : X.V.card≤n) (_cap : n≤q*s) : True := by
  replay_ch_typed_families
  check_refinement_count CountedBank 0
  check_refinement_count Budget 0
  trivial

theorem labelled {q s} {X : ShenMinimumOrder.Source q s} {m : Cell} {p h a b f g}
    (_cert : SelectedParentOrder X m) (_shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 2≤s) (_hq : 3≤q) (_lower : ∀ t, t<s → NoHost q t)
    (_law : ForkLaw X.D X.V q s p h) (_f : Assignment X.D X.V p h f)
    (_g : Assignment X.D X.V p h g) (_other : Assignment X.D X.V a b f)
    (_pv : p∈X.V) (_hv : h∈X.V) (_ph : p≠h)
    (_av : a∈X.V) (_bv : b∈X.V) (_ab : a≠b) :
    CountedBank X.D X.V q p h f ∧ CountedBank X.D X.V q p h g := by
  saturate_ch_families
  fail_if_success have : CountedBank X.D X.V q a b f := by assumption
  exact ⟨by assumption, by assumption⟩

#print axioms shared
#print axioms missed
#print axioms labelled
end LeanCH.BR.CyclicLayerReplayTest
