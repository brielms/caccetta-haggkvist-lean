import checkpoints.shen_extension.CHFamilyWorklist
import checkpoints.shen_extension.FamilyLoopLedger
import checkpoints.shen_extension.GuardedFamilyRules

namespace LeanCH.BR.CHFamilyWorklist
open CHRuleCatalog
open Lean Elab Tactic

elab "expect_leaves " n:num : tactic => do
  let count := (← getGoals).length
  unless count==n.getNat do throwError "expected {n.getNat} live families, got {count}"

/-- Both exhaustively supplied alternatives must survive until the rules
that consume each new physical graph have run. -/
theorem both_children {p : Input} (mark : Input→Prop) (bad : Bad p)
    (fork : Branch ((∃c,Child p c ∧ Child c p ∧ mark c) ∨ (∃d,mark d ∧ Child p d))) :
    ∃c,mark c ∧ Bad c := by
  replay_ch_typed_families
  expect_leaves 2
  all_goals solve_by_elim [Exists.intro, And.intro]

/-- One alternative leads back to the root but also leads onward to a
forbidden child. Only the other alternative is left after the replay. -/
theorem one_survivor {p a t : Input} (mark : Input→Prop) (bad : Bad p)
    (fork : Branch ((Child p a ∧ Child a p ∧ Child a t) ∨ ∃d,mark d ∧ Child p d))
    (excluded : ¬Bad t) : ∃c,mark c ∧ Bad c := by
  replay_ch_typed_families
  expect_leaves 1
  solve_by_elim [Exists.intro, And.intro]

#print axioms both_children
#print axioms one_survivor
end LeanCH.BR.CHFamilyWorklist
