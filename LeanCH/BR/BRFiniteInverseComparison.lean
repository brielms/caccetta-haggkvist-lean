import LeanCH.BR.BRFiniteArcInverse

/-! Exact comparison of two nonnegative inverses. The two matrices and
their two inverses are kept distinct throughout. -/
namespace LeanCH.BR.FiniteCutInverse
open Finset Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem inverse_difference {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K) :
    H - K = H * (S - R) * K := by
  have hleft : H * excess R = 1 := mul_eq_one_comm.mp hH.right
  have hd : S - R = excess S - excess R := by
    ext i j
    simp only [excess, Matrix.sub_apply]
    ring
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hK.right,
    Matrix.mul_one, hleft, Matrix.one_mul]

theorem inverse_difference_apply {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K) (i j : V) :
    H i j - K i j = ∑ a, ∑ b, H i a * (S a b - R a b) * K b j := by
  have he := congrArg (fun M : Matrix V V ℝ => M i j) (inverse_difference hH hK)
  rw [Matrix.mul_assoc] at he
  simpa only [Matrix.sub_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc] using he

theorem inverse_antitone {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (hRS : ∀ a b, R a b ≤ S a b) (i j : V) : K i j ≤ H i j := by
  have hn : 0 ≤ ∑ a, ∑ b, H i a * (S a b - R a b) * K b j := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (mul_nonneg (hH.nonneg i a) (sub_nonneg.mpr (hRS a b)))
      (hK.nonneg b j)
  rw [← inverse_difference_apply hH hK i j] at hn
  linarith

theorem inverse_increment_budget {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (hRS : ∀ a b, R a b ≤ S a b) (i j a b : V) :
    H i a * (S a b - R a b) * K b j ≤ H i j - K i j := by
  rw [inverse_difference_apply hH hK i j]
  have hn : ∀ a b, 0 ≤ H i a * (S a b - R a b) * K b j :=
    fun a b => mul_nonneg (mul_nonneg (hH.nonneg i a)
      (sub_nonneg.mpr (hRS a b))) (hK.nonneg b j)
  exact (Finset.single_le_sum (s := univ) (fun b _ => hn a b) (mem_univ b)).trans
    (Finset.single_le_sum (s := univ)
      (fun a _ => Finset.sum_nonneg (fun b _ => hn a b)) (mem_univ a))

theorem inverse_zero_separation {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (hRS : ∀ a b, R a b ≤ S a b) {i j a b : V}
    (hz : H i j = 0) (hab : R a b < S a b) (hia : 0 < H i a) : K b j = 0 := by
  have hbudget := inverse_increment_budget hH hK hRS i j a b
  rw [hz, zero_sub] at hbudget
  have hpos : 0 < H i a * (S a b - R a b) := mul_pos hia (sub_pos.mpr hab)
  have hzero : K b j ≤ 0 := by nlinarith [hK.nonneg i j, hK.nonneg b j]
  exact le_antisymm hzero (hK.nonneg b j)

theorem single_increment_identity {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (a b : V) (t : ℝ)
    (hd : ∀ x y, S x y - R x y = if x = a ∧ y = b then t else 0)
    (i j : V) : H i j - K i j = t * H i a * K b j := by
  rw [inverse_difference_apply hH hK i j]
  simp only [hd]
  have he : (∑ x, ∑ y, H i x * (if x = a ∧ y = b then t else 0) * K y j) =
      H i a * t * K b j := by
    calc
      _ = ∑ x, if x = a then H i a * t * K b j else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = a
        · subst x; simp
        · simp [hx]
      _ = _ := by simp
  rw [he]
  ring

theorem single_increment_row {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (a b : V) (t : ℝ)
    (hd : ∀ x y, S x y - R x y = if x = a ∧ y = b then t else 0)
    (j : V) : (1 + t * H b a) * K b j = H b j := by
  have he := single_increment_identity hH hK a b t hd b j
  nlinarith

/-- A necessary inequality for every permitted single-entry increase.
It involves only the original inverse, but its proof requires the new
inverse to be nonnegative as well. -/
theorem single_increment_rectangle {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (a b : V) (t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ x y, S x y - R x y = if x = a ∧ y = b then t else 0)
    (i j : V) : t * H i a * H b j ≤ (1 + t * H b a) * H i j := by
  have hrow := single_increment_row hH hK a b t hd j
  have hdiff := single_increment_identity hH hK a b t hd i j
  have hden : 0 ≤ 1 + t * H b a := by nlinarith [hH.nonneg b a]
  calc
    _ = (1 + t * H b a) * (H i j - K i j) := by rw [← hrow, hdiff]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hK.nonneg i j]) hden

theorem single_increment_zero_rectangle {R S H K : Matrix V V ℝ}
    (hH : CommonInverse R H) (hK : CommonInverse S K)
    (a b : V) (t : ℝ) (ht : 0 < t)
    (hd : ∀ x y, S x y - R x y = if x = a ∧ y = b then t else 0)
    {i j : V} (hz : H i j = 0) (hia : 0 < H i a) : H b j = 0 := by
  have hh := single_increment_rectangle hH hK a b t ht.le hd i j
  rw [hz, mul_zero] at hh
  have hpos := mul_pos ht hia
  have hle : H b j ≤ 0 := by nlinarith [hH.nonneg b j]
  exact le_antisymm hle (hH.nonneg b j)

/-- Finite value comparison uses the new dual and the old primal.
The old dual need not remain an equalizer of the new matrix. -/
theorem mixed_equalizer_gain {R S : Matrix V V ℝ} (w p : V → ℝ)
    (hw : (∑ v, w v) = 1) (hp : (∑ v, p v) = 1) (c d : ℝ)
    (hr : ∀ i, (R *ᵥ w) i = c) (hc : ∀ j, (p ᵥ* S) j = d) :
    d - c = ∑ i, ∑ j, p i * (S i j - R i j) * w j := by
  have hS : (∑ i, p i * (S *ᵥ w) i) = d := by
    change p ⬝ᵥ (S *ᵥ w) = d
    rw [Matrix.dotProduct_mulVec]
    simp only [dotProduct, hc, ← Finset.mul_sum, hw, mul_one]
  have hR : (∑ i, p i * (R *ᵥ w) i) = c := by
    simp only [hr, ← Finset.sum_mul, hp, one_mul]
  have he : (∑ i, ∑ j, p i * (S i j - R i j) * w j) =
      (∑ i, p i * (S *ᵥ w) i) - ∑ i, p i * (R *ᵥ w) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_sub, sub_mul,
      Finset.sum_sub_distrib, mul_assoc]
  rw [he, hS, hR]

theorem mixed_equalizer_strict_gain {R S : Matrix V V ℝ} (w p : V → ℝ)
    (hwn : ∀ v, 0 ≤ w v) (hpn : ∀ v, 0 ≤ p v)
    (hw : (∑ v, w v) = 1) (hp : (∑ v, p v) = 1) (c d : ℝ)
    (hr : ∀ i, (R *ᵥ w) i = c) (hc : ∀ j, (p ᵥ* S) j = d)
    (hRS : ∀ i j, R i j ≤ S i j) (a b : V)
    (hpa : 0 < p a) (hwb : 0 < w b) (hab : R a b < S a b) : c < d := by
  have hnon : ∀ i j, 0 ≤ p i * (S i j - R i j) * w j := fun i j =>
    mul_nonneg (mul_nonneg (hpn i) (sub_nonneg.mpr (hRS i j))) (hwn j)
  have hpos : 0 < ∑ i, ∑ j, p i * (S i j - R i j) * w j := by
    apply Finset.sum_pos'
    · intro i _
      exact Finset.sum_nonneg (fun j _ => hnon i j)
    · refine ⟨a, mem_univ a, ?_⟩
      apply Finset.sum_pos' (fun j _ => hnon a j)
      exact ⟨b, mem_univ b, mul_pos (mul_pos hpa (sub_pos.mpr hab)) hwb⟩
  rw [← mixed_equalizer_gain w p hw hp c d hr hc] at hpos
  linarith

end LeanCH.BR.FiniteCutInverse
