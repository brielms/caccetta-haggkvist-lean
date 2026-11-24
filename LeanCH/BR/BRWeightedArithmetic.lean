import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Integer rigidity of I+qA for every q>=2. Generalizes the local
CH_Closure_TightRigidity_20261110 checkpoint from q=3 and uses rational weights. -/
namespace LeanCH.BR.WeightedArithmetic
open Finset Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def closedMatrix (q : ℕ) (A : Matrix V V ℤ) : Matrix V V ℤ :=
  fun i j => (if i = j then 1 else 0) + (q : ℤ) * A i j

def rationalMatrix (q : ℕ) (A : Matrix V V ℤ) : Matrix V V ℚ :=
  (Int.castRingHom ℚ).mapMatrix (closedMatrix q A)

theorem rational_mulVec_apply (q : ℕ) (A : Matrix V V ℤ) (p : V → ℚ) (i : V) :
    (rationalMatrix q A *ᵥ p) i = p i + (q : ℚ) * ∑ j, (A i j : ℚ) * p j := by
  simp [rationalMatrix, closedMatrix, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc, apply_ite, ite_mul]

theorem rational_vecMul_apply (q : ℕ) (A : Matrix V V ℤ) (p : V → ℚ) (i : V) :
    (p ᵥ* rationalMatrix q A) i = p i + (q : ℚ) * ∑ j, (A j i : ℚ) * p j := by
  have ht : rationalMatrix q A.transpose = (rationalMatrix q A).transpose := by
    ext i j
    simp [rationalMatrix, closedMatrix, Matrix.transpose_apply, eq_comm]
  calc
    _ = (rationalMatrix q A.transpose *ᵥ p) i := by rw [ht, Matrix.mulVec_transpose]
    _ = _ := by rw [rational_mulVec_apply]; rfl

theorem closedMatrix_mod (q : ℕ) (A : Matrix V V ℤ) :
    (Int.castRingHom (ZMod q)).mapMatrix (closedMatrix q A) = 1 := by
  ext i j
  have hq : (q : ZMod q) = 0 := ZMod.natCast_self q
  by_cases h : i = j
  · subst j
    simp [closedMatrix, hq]
  · simp [closedMatrix, h, hq]

theorem det_mod (q : ℕ) (A : Matrix V V ℤ) :
    ((closedMatrix q A).det : ZMod q) = 1 := by
  change (Int.castRingHom (ZMod q)) (closedMatrix q A).det = 1
  rw [RingHom.map_det, closedMatrix_mod, Matrix.det_one]

theorem det_ne_zero {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ) :
    (closedMatrix q A).det ≠ 0 := by
  letI : Fact (1 < q) := ⟨by omega⟩
  intro hz
  have h := det_mod q A
  rw [hz] at h
  exact (zero_ne_one : (0 : ZMod q) ≠ 1) (by simpa using h)

theorem rational_det_ne_zero {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ) :
    (rationalMatrix q A).det ≠ 0 := by
  rw [rationalMatrix, ← RingHom.map_det]
  change ((closedMatrix q A).det : ℚ) ≠ 0
  exact_mod_cast det_ne_zero hq A

/-- Every rational right-hand side has a solution, with no graph hypotheses. -/
theorem rational_surjective {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ) :
    Function.Surjective (rationalMatrix q A).mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (rational_det_ne_zero hq A)

theorem integer_numerators (M : Matrix V V ℤ) (p : V → ℚ)
    (hp : (Int.castRingHom ℚ).mapMatrix M *ᵥ p = fun _ => 1) :
    ∃ z : V → ℤ, ∀ i, (M.det : ℚ) * p i = (z i : ℚ) := by
  refine ⟨fun i => ∑ j, M.adjugate i j, ?_⟩
  intro i
  let N := (Int.castRingHom ℚ).mapMatrix M
  have hn : N *ᵥ p = fun _ => 1 := hp
  have h : N.det * p i = (N.adjugate *ᵥ (fun _ => 1)) i := by
    calc
      N.det * p i = ((N.adjugate * N) *ᵥ p) i := by
        simp [Matrix.adjugate_mul, Matrix.smul_mulVec]
      _ = (N.adjugate *ᵥ (N *ᵥ p)) i := by rw [Matrix.mulVec_mulVec]
      _ = (N.adjugate *ᵥ (fun _ => 1)) i := by rw [hn]
  dsimp only [N] at h
  rw [← RingHom.map_det, ← RingHom.map_adjugate] at h
  simpa [Matrix.mulVec, dotProduct] using h

/-- No integer linear form in an equality weighting is exactly 1/q. -/
theorem no_integer_linear_form_unit {q : ℕ} (hq : 2 ≤ q)
    (A : Matrix V V ℤ) (p : V → ℚ)
    (hp : rationalMatrix q A *ᵥ p = fun _ => 1) (a : V → ℤ) :
    (q : ℚ) * (∑ i, (a i : ℚ) * p i) ≠ 1 := by
  letI : Fact (1 < q) := ⟨by omega⟩
  intro heq
  obtain ⟨z, hz⟩ := integer_numerators (closedMatrix q A) p hp
  let d : ℤ := (closedMatrix q A).det
  let k : ℤ := ∑ i, a i * z i
  have hsum : (d : ℚ) * (∑ i, (a i : ℚ) * p i) = (k : ℚ) := by
    dsimp only [k]
    rw [Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Int.cast_mul]
    calc
      (d : ℚ) * ((a i : ℚ) * p i) = (a i : ℚ) * ((d : ℚ) * p i) := by ring
      _ = (a i : ℚ) * (z i : ℚ) := by rw [hz i]
  have hdQ : (d : ℚ) = q * (k : ℚ) := by
    calc
      (d : ℚ) = (d : ℚ) * (q * (∑ i, (a i : ℚ) * p i)) := by rw [heq, mul_one]
      _ = q * ((d : ℚ) * (∑ i, (a i : ℚ) * p i)) := by ring
      _ = q * (k : ℚ) := by rw [hsum]
  have hdZ : d = (q : ℤ) * k := by exact_mod_cast hdQ
  have hmod : (d : ZMod q) = 0 := by rw [hdZ]; simp
  have hone : (d : ZMod q) = 1 := det_mod q A
  exact zero_ne_one (hmod.symm.trans hone)

theorem solution_coordinates_ne_zero {q : ℕ} (hq : 2 ≤ q)
    (A : Matrix V V ℤ) (p : V → ℚ)
    (hp : rationalMatrix q A *ᵥ p = fun _ => 1) : ∀ i, p i ≠ 0 := by
  intro i hz
  have hr : p i + q * (∑ j, (A i j : ℚ) * p j) = 1 := by
    have h := congrFun hp i
    simpa [rationalMatrix, closedMatrix, Matrix.mulVec, dotProduct,
      Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc, apply_ite, ite_mul] using h
  have heq : (q : ℚ) * (∑ j, (A i j : ℚ) * p j) = 1 := by simpa [hz] using hr
  exact no_integer_linear_form_unit hq A p hp (A i) heq

end LeanCH.BR.WeightedArithmetic
