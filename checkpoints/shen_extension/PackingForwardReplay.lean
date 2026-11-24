import checkpoints.shen_extension.GuardedFamilyRules
import checkpoints.shen_extension.QuotaProjectionReplay

namespace LeanCH.BR.PackingForwardRules
open Closure.MarkedCyclePeeling Closure.FirstPacketBarrier Closure.ShortestCycleWeights Closure.SharedArcBarrier
open Lean Meta Elab Tactic

elab "read_derived_fact" : tactic => withMainContext do
  let g ← getMainGoal
  let wanted := (← instantiateMVars (← g.getType)).consumeMData
  for d in (← g.getDecl).lctx do
    let actual := (← instantiateMVars d.type).consumeMData
    if actual.getAppFn == wanted.getAppFn && actual.getAppNumArgs == wanted.getAppNumArgs &&
        (← withReducible <| actual.getAppArgs.zip wanted.getAppArgs |>.allM
          (fun (x,y) => isDefEq x y)) then
      g.assign d.toExpr
      replaceMainGoal []
      return
  throwError "catalog did not derive {wanted}"

/-- Two labels and two successive family edits. Registering each rule once
must price both arcs at all three states, independent of local proof names. -/
theorem two_edits {q n} (X : Model q n) {F : Closure.MarkedCyclePeeling.Family}
    {A B : Finset ℕ} {x y u v : ℕ} (start : F⊆family X)
    (left : graph X.D F x y=true) (right : graph X.D F u v=true)
    (first : Boundary X F A) (next : Boundary X (insert A F) B) :
    ColumnBudget X F x y ∧ ColumnBudget X F u v ∧
    ColumnBudget X (insert A F) x y ∧ ColumnBudget X (insert A F) u v ∧
    ColumnBudget X (insert B (insert A F)) x y ∧ ColumnBudget X (insert B (insert A F)) u v := by
  saturate_ch_families
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> read_derived_fact

/-- A cycle in the rule graph revisits the original proposition. A third
edge must still be applied to the intermediate child. -/
theorem child_loop {p c d : CHRuleCatalog.Input} (start : CHRuleCatalog.Bad p)
    (there : CHRuleCatalog.Child p c) (_back : CHRuleCatalog.Child c p) (onward : CHRuleCatalog.Child c d) :
    CHRuleCatalog.Bad d ∧ ¬ParentCutFrontier.Gate d.n d.s (CHRuleCatalog.cutoff d) := by
  saturate_ch_families
  constructor <;> read_derived_fact

/-- A degree-eight discovery discharges a degree-nine descendant. Both
the bounded-order theorem and its transport are retrieved from the catalog. -/
theorem degree_nine_child {p : CHRuleCatalog.Input} {D : CH.Digraph}
    (start : CHRuleCatalog.Bad p) (down : CHRuleCatalog.Child p ⟨33,9,D⟩) : False := by
  saturate_ch_families
  close_ch_family

#print axioms two_edits
#print axioms child_loop
#print axioms degree_nine_child
end LeanCH.BR.PackingForwardRules
