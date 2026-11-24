
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightMoments_20261121

namespace LeanCH.BR.DotDegreeEight
open Finset Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The same codegree slack is used in both directions. -/
theorem contract_of_codegrees {P E : Matrix ι ι ℝ} {a b c : ℝ}
    (b0 : 0≤b) (e0 : ∀ i j, 0≤E i j) (sym : ∀ i j, E i j=E j i)
    (rows : ∀ i,(∑ j,E i j)=c)
    (gram : ∀ i j,(Pᵀ*P) i j=(if i=j then a else 0)+E i j-b)
    (x : ι→ℝ) : (∑ i,(P *ᵥ x) i ^ 2)≤(a+c)*(∑ i,x i ^ 2) := by
  classical
  have eq1 : (∑ i,(P *ᵥ x) i ^ 2)=x ⬝ᵥ ((Pᵀ*P)*ᵥ x) := by
    rw [←mulVec_mulVec,dotProduct_transpose_mulVec]
    simp only [dotProduct,pow_two]
  have expand : x ⬝ᵥ ((Pᵀ*P)*ᵥ x) =
      a*(∑ i,x i^2)+(∑ i,∑ j,E i j*x i*x j)-b*(∑ i,x i)^2 := by
    simp only [dotProduct,Matrix.mulVec]
    simp_rw [gram,sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      mul_sub,mul_add,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [←mul_sum]
    have h1 : (∑ i, x i*(a*x i))=a*(∑ i,x i^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    have h2 : (∑ i, x i * ∑ j,E i j*x j)=(∑ i,∑ j,E i j*x i*x j) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    have h3 : (∑ i, x i * (b*(∑ j,x j)))=b*(∑ i,x i)^2 := by
      rw [←sum_mul]
      ring
    rw [sum_sub_distrib,sum_add_distrib,h1,h2,h3]
  have elem (i j : ι) : 2*(E i j*x i*x j)≤E i j*(x i^2+x j^2) := by
    nlinarith only [mul_nonneg (e0 i j) (sq_nonneg (x i-x j))]
  have es := sum_le_sum (fun i (_ : i∈univ) =>
    sum_le_sum (fun j (_ : j∈univ) => elem i j))
  have eq2 : (∑ i,∑ j,E i j*(x i^2+x j^2))=2*c*(∑ i,x i^2) := by
    simp_rw [mul_add, sum_add_distrib]
    rw [show (∑ i, ∑ j, E i j * x j^2) = (∑ i, ∑ j, E i j * x i^2) by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [sym j i]]
    simp_rw [←sum_mul,rows]
    rw [←mul_sum]
    ring
  simp_rw [←mul_sum] at es
  rw [eq2] at es
  rw [eq1,expand]
  nlinarith only [es,mul_nonneg b0 (sq_nonneg (∑ i,x i))]

#print axioms contract_of_codegrees
end LeanCH.BR.DotDegreeEight


