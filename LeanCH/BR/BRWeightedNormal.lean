import LeanCH.BR.BRWeightedPerturb

/-! Rational normal form at the feasibility threshold. No minimax or
graph-theoretic conclusion is assumed: absence of a strict positive row
weighting is an explicit hypothesis, and integer arithmetic supplies the
nonzero coordinates of the column equalizer. -/
namespace LeanCH.BR.WeightedNormal
open Finset Matrix WeightedArithmetic WeightedPerturb
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def StrictProbability (R : Matrix V V ℚ) : Prop :=
  ∃ w : V → ℚ, (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ ∀ i, 1 < (R *ᵥ w) i

theorem sum_eq_column_pair {R : Matrix V V ℚ} {p : V → ℚ}
    (hp : p ᵥ* R = fun _ => 1) (x : V → ℚ) :
    (∑ i, x i) = p ⬝ᵥ (R *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, hp]
  simp [dotProduct]

theorem strict_of_positive_direction (R : Matrix V V ℚ) (w h : V → ℚ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hzero : ∑ i, h i = 0)
    (hr : ∀ i, 1 ≤ (R *ᵥ w) i) (hh : ∀ i, 0 < (R *ᵥ h) i) : StrictProbability R := by
  obtain ⟨e, he, hkeep⟩ := finite_positive_affine Finset.univ w h (fun i _ => hw i)
  let z : V → ℚ := fun i => w i + e * h i
  refine ⟨z, fun i => hkeep e he.le le_rfl i (Finset.mem_univ _), ?_, ?_⟩
  · dsimp only [z]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hzero]
    simp
  · intro i
    have hz : z = w + e • h := rfl
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_pos he (hh i), hr i]

theorem strict_of_constant_target (R : Matrix V V ℚ) (w x : V → ℚ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hr : ∀ i, 1 ≤ (R *ᵥ w) i) (hx : R *ᵥ x = fun _ => 1)
    (hsmall : (∑ i, x i) < 1) : StrictProbability R := by
  let a : ℚ := ∑ i, x i
  let h : V → ℚ := fun i => x i - a * w i
  have hzero : ∑ i, h i = 0 := by
    dsimp only [h]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
    exact sub_self a
  let f : Option V → ℚ := fun i => match i with | none => 1 | some j => w j
  let g : Option V → ℚ := fun i => match i with | none => -a | some j => h j
  have hf : ∀ i ∈ (Finset.univ : Finset (Option V)), 0 < f i := by
    intro i hi
    cases i with
    | none => exact zero_lt_one
    | some j => exact hw j
  obtain ⟨e, he, hkeep⟩ := finite_positive_affine Finset.univ f g hf
  have hcoef : 0 < 1 - e * a := by
    have hh := hkeep e he.le le_rfl none (Finset.mem_univ _)
    change 0 < 1 + e * (-a) at hh
    nlinarith
  let z : V → ℚ := fun i => w i + e * h i
  refine ⟨z, fun i => hkeep e he.le le_rfl (some i) (Finset.mem_univ _), ?_, ?_⟩
  · dsimp only [z]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hzero]
    simp
  · intro i
    have hz : z = w + e • (x - a • w) := rfl
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hx]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hb := mul_le_mul_of_nonneg_left (hr i) hcoef.le
    change a < 1 at hsmall
    nlinarith [mul_pos he (sub_pos.mpr hsmall)]

theorem strict_of_negative_column {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ)
    (w p : V → ℚ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hr : ∀ i, 1 ≤ (rationalMatrix q A *ᵥ w) i)
    (hp : p ᵥ* rationalMatrix q A = fun _ => 1) {k : V} (hk : p k < 0) :
    StrictProbability (rationalMatrix q A) := by
  let R := rationalMatrix q A
  obtain ⟨x, hx⟩ := rational_surjective hq A (fun i => if i = k then 1 else 0)
  have hsumx : ∑ i, x i = p k := by
    rw [sum_eq_column_pair hp x, hx]
    simp [dotProduct]
  let h : V → ℚ := fun i => x i - p k * w i
  apply strict_of_positive_direction R w h hw hsum
  · dsimp only [h]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumx, hsum]
    ring
  · exact hr
  · intro i
    have hh : h = x - (p k) • w := rfl
    rw [hh, Matrix.mulVec_sub, Matrix.mulVec_smul, hx]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hpos : 0 < (R *ᵥ w) i := lt_of_lt_of_le zero_lt_one (hr i)
    have hm := mul_neg_of_neg_of_pos hk hpos
    split_ifs <;> linarith

/-- Without a strict positive counterweight, every positive feasible
probability is exactly equalized and has a positive normalized column dual.
This works for every integer matrix I+qA, q>=2. -/
theorem equalized_of_no_strict {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ)
    (w : V → ℚ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hr : ∀ i, 1 ≤ (rationalMatrix q A *ᵥ w) i)
    (hno : ¬ StrictProbability (rationalMatrix q A)) :
    (∀ i, (rationalMatrix q A *ᵥ w) i = 1) ∧
      ∃ p : V → ℚ, (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧
        p ᵥ* rationalMatrix q A = fun _ => 1 := by
  obtain ⟨p, hpT⟩ := rational_surjective hq A.transpose (fun _ => 1)
  have htranspose : rationalMatrix q A.transpose = (rationalMatrix q A).transpose := by
    ext i j
    simp [rationalMatrix, closedMatrix, Matrix.transpose_apply, eq_comm]
  have hp : p ᵥ* rationalMatrix q A = fun _ => 1 := by
    rw [htranspose, Matrix.mulVec_transpose] at hpT
    exact hpT
  have hpn : ∀ i, 0 ≤ p i := by
    intro i
    exact le_of_not_gt (fun hn => hno (strict_of_negative_column hq A w p hw hsum hr hp hn))
  have hpp : ∀ i, 0 < p i := by
    intro i
    exact lt_of_le_of_ne (hpn i) (Ne.symm (solution_coordinates_ne_zero hq A.transpose p hpT i))
  have hpair : (∑ i, p i * (rationalMatrix q A *ᵥ w) i) = 1 :=
    (sum_eq_column_pair hp w).symm.trans hsum
  have hterm : ∀ i ∈ (Finset.univ : Finset V), p i ≤ p i * (rationalMatrix q A *ᵥ w) i := by
    intro i hi
    simpa using mul_le_mul_of_nonneg_left (hr i) (hpn i)
  have hple : (∑ i, p i) ≤ 1 := by
    calc
      _ ≤ ∑ i, p i * (rationalMatrix q A *ᵥ w) i := Finset.sum_le_sum hterm
      _ = 1 := hpair
  have hpsum : (∑ i, p i) = 1 := by
    apply le_antisymm hple
    apply le_of_not_gt
    intro hlt
    obtain ⟨x, hx⟩ := rational_surjective hq A (fun _ => 1)
    have hsx : (∑ i, x i) = ∑ i, p i := by
      rw [sum_eq_column_pair hp x, hx]
      simp [dotProduct]
    exact hno (strict_of_constant_target (rationalMatrix q A) w x hw hsum hr hx (hsx ▸ hlt))
  refine ⟨?_, p, hpp, hpsum, hp⟩
  intro i
  have heq : (∑ j, p j) = ∑ j, p j * (rationalMatrix q A *ᵥ w) j := hpsum.trans hpair.symm
  have each := (Finset.sum_eq_sum_iff_of_le hterm).mp heq i (Finset.mem_univ _)
  have each' : p i * 1 = p i * (rationalMatrix q A *ᵥ w) i := by simpa using each
  exact (mul_left_cancel₀ (ne_of_gt (hpp i)) each').symm

theorem row_equalizer_unique {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ)
    {x y : V → ℚ} (hx : rationalMatrix q A *ᵥ x = fun _ => 1)
    (hy : rationalMatrix q A *ᵥ y = fun _ => 1) : x = y := by
  have hunit : IsUnit (rationalMatrix q A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (rational_det_ne_zero hq A))
  exact (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hx.trans hy.symm)

theorem column_equalizer_unique {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ)
    {x y : V → ℚ} (hx : x ᵥ* rationalMatrix q A = fun _ => 1)
    (hy : y ᵥ* rationalMatrix q A = fun _ => 1) : x = y := by
  have ht : rationalMatrix q A.transpose = (rationalMatrix q A).transpose := by
    ext i j
    simp [rationalMatrix, closedMatrix, Matrix.transpose_apply, eq_comm]
  apply row_equalizer_unique hq A.transpose
  · rw [ht, Matrix.mulVec_transpose]; exact hx
  · rw [ht, Matrix.mulVec_transpose]; exact hy

end LeanCH.BR.WeightedNormal
