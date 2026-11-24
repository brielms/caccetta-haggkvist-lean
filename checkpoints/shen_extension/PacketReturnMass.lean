import checkpoints.shen_extension.PacketCompression

namespace LeanCH.BR.PacketCompression
open Finset Matrix
open scoped Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A diagonal entry of A^m counts all length-m weighted returns together.
A return mass of at least one supplies a nonzero feasible certificate. -/
theorem returns {A : Matrix I I ℝ} (nn : ∀ i j, 0 ≤ A i j)
    (b : I) {m : ℕ} (hm : 0 < m) (gain : 1 ≤ (A^m) b b) :
    ∃ t : I → ℝ, Live t ∧ ∀ j, t j ≤ (t ᵥ* A) j := by
  have powers (n : ℕ) (i j : I) : 0 ≤ (A^n) i j := by
    induction n generalizing i j with
    | zero => simp only [pow_zero,Matrix.one_apply]; split <;> norm_num
    | succ n ih =>
      rw [pow_succ,Matrix.mul_apply]
      exact sum_nonneg fun l _ => mul_nonneg (ih i l) (nn l j)
  let t (n : ℕ) (j : I) := ∑ k ∈ range n, (A^k) b j
  have succ (n : ℕ) : t (n+1) = t n + (fun j => (A^n) b j) := by
    funext j; exact sum_range_succ _ _
  have step (n : ℕ) (j : I) : ((fun i => (A^n) b i) ᵥ* A) j = (A^(n+1)) b j := by
    rw [pow_succ]; rfl
  have telescope (n : ℕ) (j : I) : (t n ᵥ* A) j + (1 : Matrix I I ℝ) b j = t n j + (A^n) b j := by
    induction n with
    | zero => simp [t,vecMul,dotProduct]
    | succ n ih =>
      rw [succ,add_vecMul,Pi.add_apply,Pi.add_apply,step]
      linarith
  have live : Live (t m) := by
    refine ⟨fun j => sum_nonneg (fun k _ => powers k b j),b,?_⟩
    have h := single_le_sum (s := range m) (f := fun k => (A^k) b b)
      (fun k _ => powers k b b) (mem_range.mpr hm)
    change (A^0) b b ≤ t m b at h
    rw [pow_zero,Matrix.one_apply_eq] at h
    exact zero_lt_one.trans_le h
  refine ⟨t m,live,fun j => ?_⟩
  have total := telescope m j
  by_cases eq : b = j
  · subst j
    rw [Matrix.one_apply_eq] at total
    linarith
  · rw [Matrix.one_apply_ne eq,add_zero] at total
    linarith [powers m b j]

end LeanCH.BR.PacketCompression

#print axioms LeanCH.BR.PacketCompression.returns

