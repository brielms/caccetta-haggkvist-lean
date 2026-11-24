-- Port of CH.StrictCorrection.UnitSourceOrderCongruence.card_mod from the
-- indexed 2026-11-11 corpus. Only namespace and mapMatrix simplification adapt.
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace LeanCH.BR.WeightedOrderArithmetic

open scoped BigOperators Matrix

/-- An actual integer all-tight unit normalizer at coefficient q has
support order congruent to one modulo q. Positivity and No3 are not needed
for this arithmetic fact. A merely feasible, non-tight cover does not
satisfy the premise. -/
theorem card_mod {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (A : Matrix V V ℤ) (x : V → ℚ)
    (normal : ∀ i, x i + (q : ℚ) * (∑ j, (A i j : ℚ) * x j) = 1)
    (mass : ∑ i, x i = 1) : (Fintype.card V : ZMod q) = 1 := by
  classical
  let M : Matrix V V ℤ := fun i j => (if i = j then 1 else 0) + (q : ℤ) * A i j
  let d : ℤ := M.det
  let w : V → ℤ := M.adjugate *ᵥ (fun _ => 1)
  let f : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  let g : ℤ →+* ℚ := Int.castRingHom ℚ
  have modM : f.mapMatrix M = 1 := by
    ext i j
    change (((if i = j then 1 else 0) + (q : ℤ) * A i j : ℤ) : ZMod q) =
      if i = j then 1 else 0
    simp
  have modD : f d = 1 := by
    change f M.det = 1
    rw [f.map_det, modM, Matrix.det_one]
  have modAdj : f.mapMatrix M.adjugate = 1 := by
    rw [f.map_adjugate, modM, Matrix.adjugate_one]
  have modW (i : V) : f (w i) = 1 := by
    have h := f.map_mulVec M.adjugate (fun _ => (1 : ℤ)) i
    have hm : M.adjugate.map f = 1 := by
      simpa only [RingHom.mapMatrix_apply] using modAdj
    simpa [w, hm, Function.comp_def] using h
  have normM : (g.mapMatrix M) *ᵥ x = (fun _ => 1) := by
    ext i
    change (∑ j, (((if i = j then 1 else 0) + (q : ℤ) * A i j : ℤ) : ℚ) * x j) = 1
    simpa [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum,
      ite_mul] using normal i
  have coordinates (i : V) : (d : ℚ) * x i = (w i : ℚ) := by
    have h := congrArg (fun v : V → ℚ => ((g.mapMatrix M).adjugate *ᵥ v) i) normM
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec] at h
    have hm := g.map_mulVec M.adjugate (fun _ => (1 : ℤ)) i
    have ha : M.adjugate.map g = (g.mapMatrix M).adjugate := by
      simpa only [RingHom.mapMatrix_apply] using g.map_adjugate M
    rw [ha] at hm
    simp only [Function.comp_def, map_one] at hm
    rw [← g.map_det M] at h
    simpa [d, w, g, Pi.smul_apply, smul_eq_mul] using h.trans hm.symm
  have sumQ : (d : ℚ) = ∑ i, (w i : ℚ) := by
    calc
      (d : ℚ) = (d : ℚ) * ∑ i, x i := by rw [mass, mul_one]
      _ = ∑ i, (w i : ℚ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => coordinates i)
  have sumZ : d = ∑ i, w i := by exact_mod_cast sumQ
  have modSum := congrArg f sumZ
  rw [modD, map_sum] at modSum
  simpa only [modW, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    using modSum.symm

end LeanCH.BR.WeightedOrderArithmetic
