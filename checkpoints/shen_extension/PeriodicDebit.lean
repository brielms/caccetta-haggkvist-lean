import checkpoints.shen_extension.CHForwardCatalog
import Mathlib.Tactic

namespace LeanCH.BR.PeriodicDebit
open Finset Function

theorem sum_drops {α G : Type*} [AddCommGroup G] (step : α→α) (v : α→G) (s : α) (k : ℕ) :
    ∑i∈range k,(v (step^[i] s)-v (step^[i+1] s)) = v s-v (step^[k] s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    abel

/-- A positive total debit on a return to the same labelled state
outstrips the decrease of every proposed potential on some actual step. -/
@[aesop safe forward (immediate := [back,bill]) (rule_sets := [CHGraphFamilies])]
theorem underfunded_step {α G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {step : α→α} {debit : ℕ→G} {s k} (back : step^[k] s=s)
    (bill : 0 < (range k).sum debit) :
    ∀v : α→G,∃i<k,v (step^[i] s)-v (step^[i+1] s)<debit i := by
  intro v
  by_contra! paid
  have total := sum_le_sum (fun i (h : i∈range k)=>paid i (mem_range.mp h))
  rw [sum_drops,back,sub_self] at total
  exact (not_lt_of_ge total) bill

/-- Replay on expanded costs at the physical label reached on each turn. -/
example {α : Type*} (next : α→α) (w head tail : α→ℝ) (start : α) (k : ℕ)
    (_back : next^[k] start=start)
    (_positive : 0 < ∑i∈range k, (fun a=>w a*(head a-tail a)) (next^[i] start)) :
    ∀v : α→ℝ, ∃i<k, v (next^[i] start)-v (next^[i+1] start) <
      w (next^[i] start)*(head (next^[i] start)-tail (next^[i] start)) := by
  saturate_ch_families
  assumption

#print axioms underfunded_step
end LeanCH.BR.PeriodicDebit
