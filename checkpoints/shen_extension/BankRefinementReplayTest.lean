import checkpoints.shen_extension.BankRefinementReplay
import checkpoints.shen_extension.CHFamilyWorklist

namespace LeanCH.BR.BankRefinementReplayTest
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay JointShortcutReplay BankRefinementReplay
open Lean Meta Elab Tactic

-- The assertions inspect the proof state without changing it.
set_option linter.unusedTactic false

elab "check_refinement_count " c:ident n:num : tactic => withMainContext do
  let key ← realizeGlobalConstNoOverloadWithInfo c
  let mut count := 0
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if (← instantiateMVars d.type).getAppFn.isConstOf key then count := count+1
  unless count=n.getNat do throwError "expected {n.getNat} facts of {key}, found {count}"

elab "check_refinement_goals " n:num : tactic => do
  let count := (← getGoals).length
  unless count=n.getNat do throwError "expected {n.getNat} branches, found {count}"

/-- A symbolic shared leaf keeps the guard. Upon specialization the same
engine opens the selected graph's bank and retains both payment laws. -/
theorem shared_after_cutoff {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_certificate : SelectedParentOrder X m) (_common : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_none : NoHost q (s-1)) :
    q=3 → SharedTriangleBank X := by
  replay_ch_typed_families
  check_refinement_count AtTriangle 1
  check_refinement_count SharedTriangleBank 0
  check_refinement_count FourTargetLaw 0
  intro triangle
  replay_ch_typed_families
  check_refinement_goals 1
  check_refinement_count SharedTriangleBank 1
  check_refinement_count FourTargetLaw 1
  check_refinement_count TwoSinkLaw 1
  check_refinement_count SharedSourceLaw 1
  replay_ch_typed_families
  check_refinement_count FourTargetLaw 1
  assumption

/-- The missed-parent cutoff-three certificate actually splits the
several-short-row and one-short-row cases in the worklist. -/
theorem missed_after_cutoff {q s n} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (_certificate : SelectedParentOrder X m) (_miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (_reg : OutEq s X.D X.V) (_hs : 8≤s) (_none : NoHost q (s-1)) (_order : X.V.card≤n) (_cap : n≤q*s) :
    q=3 → MissedTriangleBank X := by
  replay_ch_typed_families
  check_refinement_count AtTriangle 1
  check_refinement_count MissedTriangleBank 0
  intro triangle
  replay_ch_typed_families
  check_refinement_goals 2
  all_goals check_refinement_count MissedTriangleBank 1
  all_goals assumption

/-- Two label assignments on one bank and a negative control with an
independent bank. The rule can feed a cycle conclusion for a specified set. -/
theorem labelled_limits {D V p y p' y' W W' v v' B}
    (_law : FourTargetLaw D V p y)
    (_first : FourTargetFrame D V p y v W) (_second : FourTargetFrame D V p y v' W')
    (_other : FourTargetFrame D V p' y' v W)
    (_subset : B⊆exceptions D V p y v W) (_four : B.card=4) :
    (exceptions D V p y v W).card≤4 ∧ (exceptions D V p y v' W').card≤4 ∧
      ∃ i, Walk D B i i 4 := by
  saturate_ch_families
  fail_if_success have : (exceptions D V p' y' v W).card≤4 := by assumption
  exact ⟨by assumption,by assumption,by assumption⟩

theorem labelled_two_sink {E U t v} (_law : TwoSinkLaw U t) (_frame : TwoSinkFrame E U t v) :
    ∃ e∈U, (∀ i, e≠v i) ∧ E (v TwoSinkPayer.Role.z) e=true ∧ E e (v TwoSinkPayer.Role.payer)=true := by
  saturate_ch_families
  assumption

/-- The payer on this assignment must hit this assignment's second middle.
The corresponding negative literal rules out this specialized leaf. -/
theorem labelled_sole_payer {D V p y v m} (_law : SharedSourceLaw D V p y)
    (_frame : SharedSourceFrame D V p y v) (_single : SinglePayerFrame D V p y v m)
    (miss : D m (v FourLayerReversal.Role.j)≠true) : False := by
  saturate_ch_families
  exact miss (by assumption)

#print axioms labelled_sole_payer
#print axioms shared_after_cutoff
#print axioms missed_after_cutoff
#print axioms labelled_limits
#print axioms labelled_two_sink
end LeanCH.BR.BankRefinementReplayTest
