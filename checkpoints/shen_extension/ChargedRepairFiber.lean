import checkpoints.shen_extension.CycleSlotOrbit

namespace LeanCH.BR.Closure.ChargedRepairFiber
open Finset Function CycleSlotOrbit

/-- Start at a specified recurrent state. If every state has nonnegative
total cost and this state has positive cost, some label at this very state
has a positive closed return. The individual label costs may have either sign. -/
theorem anchored {α : Type*} [Finite α] (go : α→α) (bag : α→Finset ℕ)
    (send : ∀a, ↥(bag a) ≃ ↥(bag (go a))) (cost : Slot go bag→ℝ)
    (floor : ∀a : periodicPts go,0≤∑y : ↥(bag a.val),cost ⟨a,y⟩)
    (a : periodicPts go) (strict : 0<∑y : ↥(bag a.val),cost ⟨a,y⟩) :
    ∃ y : ↥(bag a.val), ∃k,0<k ∧ (lift go bag send)^[k] ⟨a,y⟩=(⟨a,y⟩ : Slot go bag) ∧
      0<∑i∈range k,cost ((lift go bag send)^[i] ⟨a,y⟩) := by
  classical
  let _ := Fintype.ofFinite (periodicPts go)
  let step := lift go bag send
  let k := (Fintype.card (Slot go bag)).factorial
  have kp : 0<k := Nat.factorial_pos _
  have moves (n : ℕ) : ∃b : periodicPts go,∃e : ↥(bag a.val) ≃ ↥(bag b.val),
      ∀y,step^[n] ⟨a,y⟩=(⟨b,e y⟩ : Slot go bag) := by
    induction n with
    | zero => exact ⟨a,Equiv.refl _,fun _ => rfl⟩
    | succ n ih =>
      obtain ⟨b,e,act⟩ := ih
      refine ⟨base go b,e.trans (send b.val),fun y => ?_⟩
      rw [iterate_succ_apply',act]
      rfl
  have non (n : ℕ) : 0≤∑y : ↥(bag a.val),cost (step^[n] ⟨a,y⟩) := by
    obtain ⟨b,e,move⟩ := moves n
    simp_rw [move]
    exact (Equiv.sum_comp e (fun y => cost ⟨b,y⟩)).symm ▸ floor b
  have whole : 0<∑n∈range k,∑y : ↥(bag a.val),cost (step^[n] ⟨a,y⟩) :=
    sum_pos' (fun n _ => non n) ⟨0,mem_range.mpr kp,strict⟩
  rw [sum_comm] at whole
  have someLabel : ∃y : ↥(bag a.val),0<∑n∈range k,cost (step^[n] ⟨a,y⟩) := by
    by_contra! none
    exact whole.not_ge (sum_nonpos (fun y _ => none y))
  obtain ⟨y,paid⟩ := someLabel
  exact ⟨y,k,kp,isPeriodicPt_factorial_card_of_mem_periodicPts (step.injective.mem_periodicPts _),paid⟩

#print axioms anchored
end LeanCH.BR.Closure.ChargedRepairFiber
