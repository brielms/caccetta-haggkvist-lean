import LeanCH.BR.BRFiniteInverseDiagonal
import LeanCH.BR.BRFiniteDeletionThreshold
import LeanCH.BR.BRWeightedRealUnit

/-! An exact one-entry threshold gives a positive unit law for the actual
deleted integer matrix. No cofactor formula, girth, or IH is assumed. -/
namespace LeanCH.BR.ThresholdUnit
open Finset Matrix FiniteCutInverse WeightedArithmetic InverseDiagonal
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def inverseRowLaw (H : Matrix ι ι ℝ) (v : ι) : ι → ℝ :=
  fun i => H v i / ∑ j, H v j

theorem exact_threshold_unit {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ)
    {C S H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hS : ∀ i j, S i j = (if i = j then 1 else 0)+(q : ℝ)*(A i j : ℝ))
    (u v : ι) (hd : ∀ i j, C i j-S i j = if i=u ∧ j=v then q else 0)
    (ht : (q : ℝ)*H v u = 1) :
    (∀ i, 0 < inverseRowLaw H v i) ∧ (∑ i, inverseRowLaw H v i) = 1 ∧
    (∀ j, (inverseRowLaw H v ᵥ* S) j = 1) ∧ (Fintype.card ι : ZMod q) = 1 := by
  let p := inverseRowLaw H v
  let m := ∑ j, H v j
  have hm : 0 < m := inverse_row_sum_pos hH v
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (hH.nonneg v i) hm.le
  have hmass : ∑ i, p i = 1 := by
    simp only [p,inverseRowLaw,div_eq_mul_inv,← sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt hm)
  have hcol (j : ι) : (p ᵥ* S) j = 1 := by
    have hd' : ∀ i j, C i j-S i j = if i=u ∧ j=v then (q : ℝ) else 0 := by
      intro i j
      simpa only [Nat.cast_ite, Nat.cast_zero] using hd i j
    have he := decrement_columns hH u v (q : ℝ) hd' j
    rw [ht,sub_self] at he
    simp only [ite_self,add_zero] at he
    have hscale : (p ᵥ* S) j = ((fun k => H v k) ᵥ* S) j/m := by
      simp only [p,inverseRowLaw,Matrix.vecMul,dotProduct,div_eq_mul_inv,sum_mul,m]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hscale,he]
    exact div_self (ne_of_gt hm)
  have hformula (i : ι) : p i+(q : ℝ)*(∑ j, (A j i : ℝ)*p j) = 1 := by
    have he := hcol i
    have heq : (p ᵥ* S) i = p i+(q : ℝ)*(∑ j, (A j i : ℝ)*p j) := by
      simp only [Matrix.vecMul,dotProduct,hS,mul_add,sum_add_distrib,mul_ite,
        mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true,mul_sum]
      congr 1
      apply sum_congr rfl
      intro j hj
      ring
    rw [heq] at he
    exact he
  have hmap : ((Rat.castHom ℝ).mapMatrix (rationalMatrix q A.transpose)) *ᵥ p = fun _ => 1 := by
    funext i
    simpa [rationalMatrix,closedMatrix,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      sum_add_distrib,mul_sum,add_mul,mul_assoc,ite_mul,apply_ite] using hformula i
  have hn := WeightedSD.real_unit_coordinates_ne_zero hq A.transpose p hmap
  refine ⟨fun i => lt_of_le_of_ne (hp i) (Ne.symm (hn i)),hmass,hcol,?_⟩
  exact real_unit_card_mod hq A.transpose p hmass hformula

/-- The normalized inverse row at any exact integer threshold is positive.
The subtracted entry need not originally be a graph arc. -/
theorem integer_exact_threshold {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ)
    {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i=j then 1 else 0)+(q : ℝ)*(A i j : ℝ))
    (u v : ι) (ht : (q : ℝ)*H v u = 1) :
    (∀ i, 0 < H v i) ∧ (Fintype.card ι : ZMod q) = 1 := by
  let A' : Matrix ι ι ℤ := fun i j => A i j - if i=u ∧ j=v then 1 else 0
  let S : Matrix ι ι ℝ := fun i j => C i j - if i=u ∧ j=v then q else 0
  have hs : ∀ i j, S i j = (if i=j then 1 else 0)+(q : ℝ)*(A' i j : ℝ) := by
    intro i j
    dsimp only [S,A']
    rw [hC]
    split_ifs <;> push_cast <;> ring
  have hd : ∀ i j, C i j-S i j = if i=u ∧ j=v then q else 0 := by
    intro i j
    dsimp only [S]
    ring
  obtain ⟨hp,_,_,hmod⟩ := exact_threshold_unit hq A' hH hs u v hd ht
  refine ⟨?_,hmod⟩
  intro i
  have hh := hp i
  change 0 < H v i/(∑ j,H v j) at hh
  exact (div_pos_iff.mp hh).resolve_right (fun h =>
    (not_lt_of_ge (inverse_row_sum_pos hH v).le) h.2) |>.1

/-- Normalized inverse rows are distinct. No arithmetic or graph structure
is needed; nonnegativity guarantees the normalization is nonzero. -/
theorem inverseRowLaw_injective {C H : Matrix ι ι ℝ} (hH : CommonInverse C H) :
    Function.Injective (inverseRowLaw H) := by
  have hl : H*excess C=1 := mul_eq_one_comm.mp hH.right
  have hformula (v j : ι) : (inverseRowLaw H v ᵥ* excess C) j =
      (if v=j then 1 else 0)/(∑ k,H v k) := by
    have he := congrArg (fun M : Matrix ι ι ℝ => M v j) hl
    change (∑ k,H v k*excess C k j)=(1 : Matrix ι ι ℝ) v j at he
    have hs : (inverseRowLaw H v ᵥ* excess C) j=
        (∑ k,H v k*excess C k j)/(∑ k,H v k) := by
      simp only [inverseRowLaw,Matrix.vecMul,dotProduct,div_eq_mul_inv,sum_mul]
      apply sum_congr rfl
      intro k hk
      ring
    rw [hs,he,Matrix.one_apply]
  intro v w he
  by_contra hn
  have hh := congrArg (fun p : ι → ℝ => (p ᵥ* excess C) v) he
  rw [hformula v v,hformula w v] at hh
  simp only [ite_true,Ne.symm hn,ite_false,zero_div] at hh
  exact (ne_of_gt (one_div_pos.mpr (inverse_row_sum_pos hH v))) hh

end LeanCH.BR.ThresholdUnit
