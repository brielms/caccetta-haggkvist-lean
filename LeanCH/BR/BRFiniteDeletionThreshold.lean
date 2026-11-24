import LeanCH.BR.BRFiniteInverseComparison

/-! Exact single-entry deletion certificates. Nonnegative inverse alone
does not imply that every entry reaches the deletion threshold. -/
namespace LeanCH.BR.FiniteCutInverse
open Finset Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem inverse_row_sum_pos {R H : Matrix V V ℝ} (hH : CommonInverse R H) (b : V) :
    0 < ∑ k, H b k := by
  have hl : H * excess R = 1 := mul_eq_one_comm.mp hH.right
  have hex : ∃ k, 0 < H b k := by
    by_contra hn
    push Not at hn
    have hz : ∀ k, H b k = 0 := fun k => le_antisymm (hn k) (hH.nonneg b k)
    have hh := congrArg (fun M : Matrix V V ℝ => M b b) hl
    simp [Matrix.mul_apply, hz] at hh
  obtain ⟨k, hk⟩ := hex
  exact Finset.sum_pos' (fun k _ => hH.nonneg b k) ⟨k, mem_univ k, hk⟩

theorem decrement_columns {R S H : Matrix V V ℝ} (hH : CommonInverse R H)
    (a b : V) (t : ℝ)
    (hd : ∀ x y, R x y - S x y = if x = a ∧ y = b then t else 0) (j : V) :
    ((fun k => H b k) ᵥ* S) j = (∑ k, H b k) +
      if j = b then 1 - t * H b a else 0 := by
  have hl : H * excess R = 1 := mul_eq_one_comm.mp hH.right
  have he := congrArg (fun M : Matrix V V ℝ => M b j) hl
  change ((fun k => H b k) ᵥ* excess R) j = (1 : Matrix V V ℝ) b j at he
  rw [vecMul_excess] at he
  have hh : ((fun k => H b k) ᵥ* R) j - ((fun k => H b k) ᵥ* S) j =
      if j = b then t * H b a else 0 := by
    simp only [Matrix.vecMul, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub, hd]
    by_cases hj : j = b
    · subst j; simp [mul_comm]
    · simp [hj]
  by_cases hj : j = b
  · subst j; simp only [Matrix.one_apply_eq, ite_true] at he hh ⊢; linarith
  · have hbj : b ≠ j := Ne.symm hj
    simp only [Matrix.one_apply_ne hbj, hj, ite_false] at he hh ⊢
    linarith

/-- Normalize the head's inverse row to certify the deleted matrix. -/
theorem decrement_dual_of_threshold {R S H : Matrix V V ℝ} (hH : CommonInverse R H)
    (a b : V) (t : ℝ)
    (hd : ∀ x y, R x y - S x y = if x = a ∧ y = b then t else 0)
    (ht : 1 ≤ t * H b a) :
    ∃ p : V → ℝ, (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧ ∀ j, (p ᵥ* S) j ≤ 1 := by
  let s := ∑ k, H b k
  have hs : 0 < s := inverse_row_sum_pos hH b
  refine ⟨fun k => H b k / s, fun k => div_nonneg (hH.nonneg b k) hs.le, ?_, ?_⟩
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt hs)
  · intro j
    have he : ((fun k => H b k / s) ᵥ* S) j = ((fun k => H b k) ᵥ* S) j / s := by
      simp only [Matrix.vecMul, dotProduct, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he]
    apply (div_le_one hs).mpr
    rw [decrement_columns hH a b t hd]
    change s + (if j = b then 1 - t * H b a else 0) ≤ s
    split_ifs <;> linarith

theorem decrement_dual_iff {R S H : Matrix V V ℝ} (hH : CommonInverse R H)
    (a b : V) (t : ℝ)
    (hd : ∀ x y, R x y - S x y = if x = a ∧ y = b then t else 0) :
    (∃ p : V → ℝ, (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧ ∀ j, (p ᵥ* S) j ≤ 1) ↔
      1 ≤ t * H b a := by
  constructor
  · rintro ⟨p, hp, hm, hc⟩
    apply deletion_arc_threshold hH p hp hm t a b
    intro j
    have hh : (p ᵥ* R) j - (p ᵥ* S) j = if j = b then t * p a else 0 := by
      simp only [Matrix.vecMul, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub, hd]
      by_cases hj : j = b
      · subst j; simp [mul_comm]
      · simp [hj]
    linarith [hc j]
  · exact decrement_dual_of_threshold hH a b t hd

theorem CommonInverse.relabel {U : Type*} [Fintype U] [DecidableEq U]
    {R H : Matrix V V ℝ} (hH : CommonInverse R H) (e : U ≃ V) :
    CommonInverse (fun i j => R (e i) (e j)) (fun i j => H (e i) (e j)) := by
  refine ⟨fun i j => hH.nonneg (e i) (e j), ?_⟩
  ext i j
  change (∑ k : U, (R (e i) (e k) - 1) * H (e k) (e j)) =
    (1 : Matrix U U ℝ) i j
  rw [e.sum_comp (fun k => (R (e i) k - 1) * H k (e j))]
  have he := congrArg (fun M : Matrix V V ℝ => M (e i) (e j)) hH.right
  change (∑ k : V, (R (e i) k - 1) * H k (e j)) = (1 : Matrix V V ℝ) (e i) (e j) at he
  rw [he]
  simp [Matrix.one_apply]

end LeanCH.BR.FiniteCutInverse
