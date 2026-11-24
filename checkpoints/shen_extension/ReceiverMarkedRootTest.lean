import checkpoints.shen_extension.ReceiverMarkedRoot

/-! Replay regression: one labelled receiver root, and guards decided from the family itself.
The cutoff is pinned by an equation; n and s are bounded, never numerals. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
namespace LeanCH.BR.ReceiverMarkedRootTest
open Lean Elab Tactic Meta CHRuleCatalog LabelledCompromiseRecipe BoundaryTightParentReach BRq2

elab "expect_goals " n:num : tactic => do
  let c := (← getGoals).length
  logInfo m!"PROBE goals={c}"
  unless c==n.getNat do throwError "expected {n.getNat} open cases, found {c}"

/-- Exactly one labelled root carries the shell size, in every case. -/
elab "expect_one_root" : tactic => do
  for g in ← getGoals do
    g.withContext do
      let mut roots : Std.HashSet Expr := {}
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          let t := (← instantiateMVars d.type).consumeMData
          if let some (_,lhs,rhs) := t.eq? then
            if rhs.isAppOf ``ReceiverLaw.shell && lhs.isAppOf ``Finset.card then
              if let some b := lhs.find? (·.isAppOfArity ``BRq2.ball 4) then
                roots := roots.insert b.getAppArgs[2]!
      logInfo m!"PROBE roots={roots.size} in {← g.getTag}"
      unless roots.size==1 do throwError "expected one labelled root, found {roots.size}"

theorem symbolic_family {n s : ℕ} {D : CH.Digraph} (_bad : Bad ⟨n,s,D⟩)
    (small : n≤30) (deg : 10≤s) (cut : cutoff ⟨n,s,D⟩=3) : True := by
  replay_ch_typed_families
  expect_goals 2
  expect_one_root
  all_goals trivial

theorem numeric_family {D : CH.Digraph} (_bad : Bad ⟨30,10,D⟩) : True := by
  replay_ch_typed_families
  expect_goals 2
  expect_one_root
  all_goals replay_ch_typed_families
  expect_goals 2
  all_goals trivial

#print axioms symbolic_family
#print axioms numeric_family
end LeanCH.BR.ReceiverMarkedRootTest
