import LeanCH.BR.BRFiniteCutInverse

/-! All-column recovery from a one-entry deletion certificate. -/
namespace LeanCH.BR.FiniteCutInverse
open Finset Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem one_column_bound {R H : Matrix V V ℝ} (hH : CommonInverse R H)
    (p : V → ℝ) (hm : (∑ v, p v) = 1) (t : ℝ) (b : V)
    (hc : ∀ z, (p ᵥ* R) z ≤ 1 + if z = b then t else 0) (k : V) :
    p k ≤ t * H b k := by
  rw [recovery hH p hm k]
  calc
    _ ≤ ∑ z, (if z = b then t else 0) * H z k := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_right _ (hH.nonneg z k)
      linarith [hc z]
    _ = _ := by simp

theorem deletion_tail_positive {R H : Matrix V V ℝ} (hH : CommonInverse R H)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hm : (∑ v, p v) = 1)
    (t : ℝ) (a b : V)
    (hc : ∀ z, (p ᵥ* R) z ≤ 1 + if z = b then t * p a else 0) : 0 < p a := by
  by_contra hn
  have hz : p a = 0 := le_antisymm (le_of_not_gt hn) (hp a)
  have hle : ∀ k, p k ≤ 0 := by
    intro k
    have h := one_column_bound hH p hm (t * p a) b hc k
    simpa only [hz, mul_zero, zero_mul] using h
  have hs := Finset.sum_nonpos (s := univ) (fun k _ => hle k)
  rw [hm] at hs
  norm_num at hs

theorem deletion_arc_threshold {R H : Matrix V V ℝ} (hH : CommonInverse R H)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hm : (∑ v, p v) = 1)
    (t : ℝ) (a b : V)
    (hc : ∀ z, (p ᵥ* R) z ≤ 1 + if z = b then t * p a else 0) :
    1 ≤ t * H b a := by
  have hpos := deletion_tail_positive hH p hp hm t a b hc
  have hle := one_column_bound hH p hm (t * p a) b hc a
  nlinarith

theorem bounded_deletion_dominates {R H : Matrix V V ℝ} (hH : CommonInverse R H)
    (p : V → ℝ) (hm : (∑ v, p v) = 1) (t : ℝ) (b : V)
    (hc : ∀ z, (p ᵥ* R) z ≤ 1 + if z = b then t else 0) (ht : t ≤ 1) (k : V) :
    p k ≤ H b k := by
  exact (one_column_bound hH p hm t b hc k).trans
    (by nlinarith [hH.nonneg b k])

theorem bounded_deletion_row_mass {R H : Matrix V V ℝ} (hH : CommonInverse R H)
    (p : V → ℝ) (hm : (∑ v, p v) = 1) (t : ℝ) (b : V)
    (hc : ∀ z, (p ᵥ* R) z ≤ 1 + if z = b then t else 0) (ht : t ≤ 1) :
    1 ≤ ∑ k, H b k := by
  rw [← hm]
  exact Finset.sum_le_sum (fun k _ => bounded_deletion_dominates hH p hm t b hc ht k)

theorem equalizer_inverse_row_sum {R H : Matrix V V ℝ} (hH : CommonInverse R H)
    (w : V → ℝ) (hm : (∑ v, w v) = 1) (c : ℝ)
    (hr : ∀ i, (R *ᵥ w) i = c) (k : V) :
    w k = (c - 1) * ∑ z, H k z := by
  have he : excess R *ᵥ w = fun _ => c - 1 := by
    funext i
    rw [mulVec_excess, hr i, hm]
  have hl : H * excess R = 1 := mul_eq_one_comm.mp hH.right
  have hh : H *ᵥ (excess R *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
  rw [he] at hh
  have hk := congrFun hh k
  change (∑ z, H k z * (c - 1)) = w k at hk
  rw [← Finset.sum_mul] at hk
  exact hk.symm.trans (mul_comm _ _)

end LeanCH.BR.FiniteCutInverse
