
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! A finite-sum consumer for the paired reach/codegree argument.
Past a uniform contraction, it counts actual closed walks through a trace. -/
namespace LeanCH.BR.DotDegreeEight
open Finset Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def frob2 (M : Matrix ι ι ℝ) : ℝ :=
  ∑ j, ∑ i, M i j ^ 2

theorem frob_mul_le {P M : Matrix ι ι ℝ} {rho : ℝ}
    (contract : ∀ x : ι→ℝ, (∑ i,(P *ᵥ x) i ^ 2) ≤ rho*(∑ i,x i ^ 2)) :
    frob2 (P*M)≤rho*frob2 M := by
  unfold frob2
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct] using contract (fun i => M i j)

theorem neg_trace_sq_le_frob (M : Matrix ι ι ℝ) :
    -Matrix.trace (M*M)≤frob2 M := by
  classical
  have each (i j : ι) : -(M i j * M j i)≤(M i j ^ 2+M j i ^ 2)/2 := by
    nlinarith [sq_nonneg (M i j + M j i)]
  have all : (∑ i, ∑ j, -(M i j * M j i))≤∑ i, ∑ j,(M i j ^ 2+M j i ^ 2)/2 :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => each i j
  simp only [sum_neg_distrib] at all
  have eq : (∑ i, ∑ j,(M i j ^ 2+M j i ^ 2)/2)=frob2 M := by
    simp_rw [div_eq_mul_inv,←sum_mul,sum_add_distrib]
    unfold frob2
    rw [show (∑ i, ∑ j,M i j ^ 2) = (∑ j, ∑ i,M i j ^ 2) by exact sum_comm]
    ring
  rw [eq] at all
  simpa only [Matrix.trace,Matrix.diag,Matrix.mul_apply] using all

theorem six_moment_bound [DecidableEq ι] {P : Matrix ι ι ℝ} {rho : ℝ} (pos : 0≤rho)
    (contract : ∀ x : ι→ℝ, (∑ i,(P *ᵥ x) i ^ 2) ≤ rho*(∑ i,x i ^ 2)) :
    -Matrix.trace (P^6)≤rho^2*frob2 P := by
  have m2 := frob_mul_le (P:=P) (M:=P) contract
  have m3 := frob_mul_le (P:=P) (M:=P*P) contract
  have a := (neg_trace_sq_le_frob (P*(P*P))).trans m3
  have b := a.trans (mul_le_mul_of_nonneg_left m2 pos)
  rw [show P^6=(P*(P*P))*(P*(P*P)) by noncomm_ring,
    show rho^2*frob2 P=rho*(rho*frob2 P) by ring]
  exact b

#print axioms six_moment_bound
end LeanCH.BR.DotDegreeEight



