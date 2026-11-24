import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace LeanCH.BR.Closure.ClosedArcDrift
open Finset

private theorem telescopes (v : ℕ→ℝ) (k : ℕ) :
    (∑i∈range k,(v (i+1)-v i))=v k-v 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ,ih]; ring

/-- On one periodic row trace the entire paid bill comes from changes in
the row weight on arrivals at heads. Its changes on other arrivals sum to
the opposite amount. -/
theorem drift (w fee : ℕ→ℝ) (head : ℕ→Bool) (k : ℕ) {q : ℝ} (qp : 0<q)
    (cw : w k=w 0) (ch : head k=head 0) (wn : ∀i∈range k,0≤w i*fee i)
    (earn : 0<∑i∈range k,w i*(q*((if head i=true then 1 else 0)-
      (if head (i+1)=true then 1 else 0))-fee i)) :
    (∑i∈range k,w i*fee i)<q*(∑i∈range k,if head (i+1)=true then w (i+1)-w i else 0) ∧
    (∃i∈range k,head (i+1)=true ∧ w i<w (i+1)) ∧
    ∃j∈range k,head (j+1)=false ∧ w (j+1)<w j := by
  classical
  let h (i : ℕ) : ℝ := if head i=true then 1 else 0
  let a (i : ℕ) := if head (i+1)=true then w (i+1)-w i else 0
  let b (i : ℕ) := if head (i+1)=false then w (i+1)-w i else 0
  let v (i : ℕ) := w i*h i
  have cv : v k=v 0 := by simp only [v,h,cw,ch]
  have tel := telescopes v k
  rw [cv,sub_self] at tel
  have terms (i) : w i*(q*(h i-h (i+1))-fee i)=
      q*a i-w i*fee i-q*(v (i+1)-v i) := by
    dsimp only [v,h,a]
    cases head (i+1) <;> cases head i <;> simp <;> ring
  change 0<∑i∈range k,w i*(q*(h i-h (i+1))-fee i) at earn
  simp_rw [terms] at earn
  rw [sum_sub_distrib,sum_sub_distrib,←mul_sum,←mul_sum,tel,mul_zero,sub_zero] at earn
  have bound : (∑i∈range k,w i*fee i)<q*∑i∈range k,a i := by linarith
  have ap : 0<∑i∈range k,a i := pos_of_mul_pos_right ((sum_nonneg wn).trans_lt bound) qp.le
  have together (i) : a i+b i=w (i+1)-w i := by cases h : head (i+1) <;> simp [a,b,h]
  have total := telescopes w k
  rw [cw,sub_self] at total
  simp_rw [←together] at total
  rw [sum_add_distrib] at total
  refine ⟨bound,?_,?_⟩
  · by_contra! no
    apply ap.not_ge
    apply sum_nonpos
    intro i hi
    dsimp only [a]
    split_ifs with yes
    · exact sub_nonpos.mpr (no i hi yes)
    · exact le_rfl
  · by_contra! no
    have bp : 0≤∑i∈range k,b i := by
      apply sum_nonneg
      intro i hi
      dsimp only [b]
      split_ifs with missed
      · exact sub_nonneg.mpr (no i hi missed)
      · exact le_rfl
    linarith

#print axioms drift
end LeanCH.BR.Closure.ClosedArcDrift
