import LeanCH.BR.BRFiniteTwoLawTransport
import LeanCH.BR.BRFiniteArcInverse

/-! The inverse channel is distinct from the Bayesian reverse channel.
The algebra uses a supplied right inverse and signed field data; order
assumptions enter only in the stochastic wrapper. -/
namespace LeanCH.BR.InverseTransport
open Finset Matrix TwoLawTransport
open scoped Matrix

section Algebra
variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V] [Field 𝕜]

def centered (C : Matrix V V 𝕜) : Matrix V V 𝕜 := fun i j => C i j - 1

def channel (H : Matrix V V 𝕜) (a : V → 𝕜) (c : 𝕜) : Matrix V V 𝕜 :=
  fun j i => (c - 1) * H j i / a j

theorem row_mass {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1)
    (a : V → 𝕜) (hm : ∑ i, a i = 1) (c : 𝕜)
    (hr : ∀ i, ∑ j, C i j * a j = c) (i : V) :
    (c - 1) * ∑ j, H i j = a i := by
  have hleft : H * centered C = 1 := mul_eq_one_comm.mp hH
  have he : centered C *ᵥ a = fun _ => c - 1 := by
    funext k
    simp only [centered, Matrix.mulVec, dotProduct, sub_mul, one_mul, sum_sub_distrib, hr, hm]
  have h := congrFun (show H *ᵥ (centered C *ᵥ a) = a by
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]) i
  rw [he] at h
  simpa only [Matrix.mulVec, dotProduct, ← sum_mul, mul_comm] using h

theorem column_mass {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1)
    (p : V → 𝕜) (hm : ∑ i, p i = 1) (c : 𝕜)
    (hp : ∀ j, ∑ i, p i * C i j = c) (j : V) :
    (c - 1) * ∑ i, H i j = p j := by
  have he : p ᵥ* centered C = fun _ => c - 1 := by
    funext k
    simp only [centered, Matrix.vecMul, dotProduct, mul_sub, mul_one, sum_sub_distrib, hp, hm]
  have h := congrFun (show (p ᵥ* centered C) ᵥ* H = p by
    rw [Matrix.vecMul_vecMul, hH, Matrix.vecMul_one]) j
  rw [he] at h
  simpa only [Matrix.vecMul, dotProduct, ← mul_sum] using h

theorem channel_row_sum {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1)
    (a : V → 𝕜) (ha : ∀ i, a i ≠ 0) (hm : ∑ i, a i = 1) (c : 𝕜)
    (hr : ∀ i, ∑ j, C i j * a j = c) (i : V) :
    ∑ j, channel H a c i j = 1 := by
  simp only [channel, div_eq_mul_inv, ← sum_mul, ← mul_sum,
    row_mass hH a hm c hr i, mul_inv_cancel₀ (ha i)]

theorem channel_transport {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1)
    (a p : V → 𝕜) (ha : ∀ i, a i ≠ 0) (hm : ∑ i, p i = 1) (c : 𝕜)
    (hp : ∀ j, ∑ i, p i * C i j = c) : a ᵥ* channel H a c = p := by
  funext j
  change (∑ i, a i * ((c - 1) * H i j / a i)) = p j
  calc
    _ = ∑ i, (c - 1) * H i j := by
      apply sum_congr rfl
      intro i _
      field_simp [ha i]
    _ = p j := by rw [← mul_sum, column_mass hH p hm c hp]

theorem forward_channel {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1)
    (a p : V → 𝕜) (ha : ∀ i, a i ≠ 0) (hm : ∑ i, p i = 1) (c : 𝕜)
    (hp : ∀ j, ∑ i, p i * C i j = c) (i k : V) :
    (forward C a c * channel H a c) i k =
      ((c - 1) * (if i = k then 1 else 0) + p k) / c := by
  have hi := congrArg (fun M : Matrix V V 𝕜 => M i k) hH
  change (∑ j, (C i j - 1) * H j k) = (if i = k then 1 else 0) at hi
  simp only [sub_mul, one_mul, sum_sub_distrib] at hi
  have hcol := column_mass hH p hm c hp k
  calc
    _ = ((c - 1) * ∑ j, C i j * H j k) / c := by
      simp only [Matrix.mul_apply, forward, channel, mul_sum, div_eq_mul_inv, sum_mul]
      apply sum_congr rfl
      intro j _
      field_simp [ha j]
    _ = _ := by congr 1; rw [sub_eq_iff_eq_add.mp hi, mul_add, hcol]

theorem channel_forward {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1)
    (a : V → 𝕜) (ha : ∀ i, a i ≠ 0) (hm : ∑ i, a i = 1) (c : 𝕜)
    (hr : ∀ i, ∑ j, C i j * a j = c) (i k : V) :
    (channel H a c * forward C a c) i k =
      ((c - 1) * (if i = k then 1 else 0) + a k) / c := by
  have hleft : H * centered C = 1 := mul_eq_one_comm.mp hH
  have hi := congrArg (fun M : Matrix V V 𝕜 => M i k) hleft
  change (∑ j, H i j * (C j k - 1)) = (if i = k then 1 else 0) at hi
  simp only [mul_sub, mul_one, sum_sub_distrib] at hi
  have hrow := row_mass hH a hm c hr i
  calc
    _ = ((c - 1) * (∑ j, H i j * C j k) * a k / a i) / c := by
      simp only [Matrix.mul_apply, forward, channel, mul_sum, sum_mul, div_eq_mul_inv]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [sub_eq_iff_eq_add.mp hi, mul_add, hrow]
      by_cases hik : i = k
      · subst k
        simp only [ite_true]
        congr 1
        field_simp [ha i]
      · simp only [ite_eq_right_iff.mpr (fun h => (hik h).elim), mul_zero, zero_add]
        congr 1
        field_simp [ha i]

end Algebra

section Order
variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V] [Field 𝕜]
  [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Fintype V] [DecidableEq V] in
theorem channel_nonneg (H : Matrix V V 𝕜) (a : V → 𝕜) (c : 𝕜)
    (hH : ∀ i j, 0 ≤ H i j) (ha : ∀ i, 0 ≤ a i) (hc : 1 ≤ c) (i j : V) :
    0 ≤ channel H a c i j :=
  div_nonneg (mul_nonneg (sub_nonneg.mpr hc) (hH i j)) (ha i)

theorem channel_stochastic {C H : Matrix V V 𝕜}
    (hH : centered C * H = 1) (hHn : ∀ i j, 0 ≤ H i j)
    (a : V → 𝕜) (ha : ∀ i, 0 < a i) (hm : ∑ i, a i = 1) (c : 𝕜) (hc : 1 ≤ c)
    (hr : ∀ i, ∑ j, C i j * a j = c) :
    (∀ i j, 0 ≤ channel H a c i j) ∧ (∀ i, ∑ j, channel H a c i j = 1) :=
  ⟨channel_nonneg H a c hHn (fun i => (ha i).le) hc,
    channel_row_sum hH a (fun i => (ha i).ne') hm c hr⟩

end Order
end LeanCH.BR.InverseTransport
