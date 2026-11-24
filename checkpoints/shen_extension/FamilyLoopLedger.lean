import checkpoints.shen_extension.CHForwardCatalog
import Mathlib.Logic.Relation
import Mathlib.Order.Basic

namespace LeanCH.BR.FamilyLoopLedger

/-- Each step records the actual transition and the inequality on its
two ends. The rank can be a degree, a cutoff, or a quantity on marked states. -/
def Nonincreasing {α β : Type*} [Preorder β] (edge : α→α→Prop) (rank : α→β) (a b : α) : Prop :=
  edge a b ∧ rank b≤rank a

@[aesop safe forward (immediate := [path]) (rule_sets := [CHGraphFamilies])]
theorem along_path {α β : Type*} [Preorder β] {edge : α→α→Prop} {rank : α→β} {a b}
    (path : Relation.ReflTransGen (Nonincreasing edge rank) a b) : rank b≤rank a := by
  induction path with
  | refl => exact le_rfl
  | tail _ step ih => exact step.2.trans ih

@[aesop safe forward (immediate := [fall,back]) (rule_sets := [CHGraphFamilies])]
theorem strict_loop {α β : Type*} [Preorder β] {edge : α→α→Prop} {rank : α→β} {a b}
    (fall : rank b<rank a) (back : Relation.ReflTransGen (Nonincreasing edge rank) b a) : False :=
  (not_lt_of_ge (along_path back)) fall

/-- Close all live states in one proof when every such state forces some
live successor of strictly lower rank in a well-founded order. -/
theorem excludes_by_descent {α β : Type*} (live : α→Prop) (rank : α→β)
    {lt : β→β→Prop} (well : WellFounded lt)
    (step : ∀a,live a → ∃b,live b ∧ lt (rank b) (rank a)) : ∀a,¬live a := by
  intro a
  apply (InvImage.wf rank well).induction a
  intro x recur hx
  obtain ⟨y,hy,smaller⟩ := step x hx
  exact recur y smaller hy

#print axioms strict_loop
#print axioms excludes_by_descent
end LeanCH.BR.FamilyLoopLedger
