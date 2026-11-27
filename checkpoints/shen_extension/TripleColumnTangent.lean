import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic

namespace LeanCH.BR.TripleBank
open Finset

/-- The line through the third binomial coefficient at k, with its forward
difference as slope, bounds the coefficient from below at every integer. -/
theorem choose_three_tangent (n k : ℕ) :
    k.choose 3 + n * k.choose 2 ≤ n.choose 3 + k * k.choose 2 := by
  rcases le_total n k with small | large
  · have below (j : ℕ) (nj : n ≤ j) :
        j ≤ k → j.choose 3 + n * k.choose 2 ≤ n.choose 3 + j * k.choose 2 := by
      induction j, nj using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ j _ ih =>
        intro bound
        have jk : j ≤ k := Nat.le_of_succ_le bound
        have prev := ih jk
        have slope := Nat.choose_le_choose 2 jk
        rw [Nat.choose_succ_succ j 2, Nat.succ_mul]
        change j.choose 2 + j.choose 3 + n * k.choose 2 ≤
          n.choose 3 + (j * k.choose 2 + k.choose 2)
        omega
    exact below k small le_rfl
  · induction n, large using Nat.le_induction with
    | base => exact le_rfl
    | succ n kn ih =>
      have slope := Nat.choose_le_choose 2 kn
      rw [Nat.choose_succ_succ n 2, Nat.succ_mul]
      change k.choose 3 + (n * k.choose 2 + k.choose 2) ≤
        n.choose 2 + n.choose 3 + k * k.choose 2
      omega

/-- Sum the integer tangent inequality over a finite pool of columns. -/
theorem sum_choose_three_tangent (A : Finset ℕ) (f : ℕ → ℕ) (k : ℕ) :
    A.card * k.choose 3 + (∑ w ∈ A, f w) * k.choose 2 ≤
      (∑ w ∈ A, (f w).choose 3) + A.card * (k * k.choose 2) := by
  have summed := sum_le_sum (s := A) (fun w _ => choose_three_tangent (f w) k)
  simpa only [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, sum_mul] using summed

end LeanCH.BR.TripleBank
