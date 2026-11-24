import checkpoints.shen_extension.SingleArcDoubleExchange
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace LeanCH.BR.Closure.SingleArcSwitchSign
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcFlatResponse

section Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

private def spike (a : I) (c : ℝ) (i : I) := if i=a then c else 0

/-- Add at (a,b) and (k,v), remove at (a,v) and (k,b), with coefficients
chosen to preserve the original row and column laws. At uniform weights the
four changes have the same magnitude. -/
noncomputable def switch (R : Matrix I I ℝ) (w p : I→ℝ) (t : ℝ) (a b v k : I) :=
  R + replicateCol Unit (spike a t - spike k (t*p a/p k)) *
      replicateRow Unit (spike b 1 - spike v (w b/w v))

omit [Fintype I] [DecidableEq I] in
private theorem outer_entry (u h : I→ℝ) (i j : I) :
    (replicateCol Unit u * replicateRow Unit h) i j = u i*h j := by
  simp [Matrix.mul_apply,replicateCol,replicateRow]

theorem balance (R : Matrix I I ℝ) (w p : I→ℝ) (t : ℝ) (a b v k : I)
    (wv : w v≠0) (pk : p k≠0) :
    switch R w p t a b v k *ᵥ w=R *ᵥ w ∧ p ᵥ* switch R w p t a b v k=p ᵥ* R := by
  let u := spike a t - spike k (t*p a/p k)
  let h := spike b 1 - spike v (w b/w v)
  have row : ∑j,h j*w j=0 := by
    simp [h,spike,sub_mul,sum_sub_distrib,ite_mul,wv]
  have col : ∑i,p i*u i=0 := by
    simp [u,spike,mul_sub,sum_sub_distrib,mul_ite]
    field_simp [pk]; ring
  constructor
  · ext i
    change ((R + replicateCol Unit u * replicateRow Unit h) *ᵥ w) i=_
    rw [add_mulVec,Pi.add_apply]
    change _+ (∑j, (replicateCol Unit u * replicateRow Unit h) i j*w j)=_
    simp [outer_entry,mul_assoc,←mul_sum,row]
  · ext j
    change (p ᵥ* (R + replicateCol Unit u * replicateRow Unit h)) j=_
    rw [vecMul_add,Pi.add_apply]
    change _+ (∑i, p i*(replicateCol Unit u * replicateRow Unit h) i j)=_
    simp [outer_entry,←mul_assoc,←sum_mul,col]

/-- Direct determinant test for the interior entry. No safety, smaller-order
induction, or sign assumptions about the child are used. -/
theorem determinant {R : Matrix I I ℝ} (unit : IsUnit R.det) (w p : I→ℝ)
    (t : ℝ) (a b v k : I) (wv : w v≠0) (pk : p k≠0) :
    (switch R w p t a b v k).det * (w v*p k) = R.det * test R⁻¹ w p t a b v k := by
  have det1 (B : Matrix Unit Unit ℝ) : B.det=B () () := Matrix.det_unique B
  rw [switch,det_add_replicateCol_mul_replicateRow unit,det1,Matrix.add_apply,Matrix.one_apply_eq]
  let u := spike a t - spike k (t*p a/p k)
  let h := spike b 1 - spike v (w b/w v)
  have left (i : I) : (replicateRow Unit h * R⁻¹) () i = R⁻¹ b i-(w b/w v)*R⁻¹ v i := by
    change (∑ j, h j * R⁻¹ j i)=_
    simp [h,spike,sub_mul,sum_sub_distrib,ite_mul]
  have eval : (replicateRow Unit h * R⁻¹ * replicateCol Unit u) () () =
      t*(R⁻¹ b a-(w b/w v)*R⁻¹ v a) - (t*p a/p k)*(R⁻¹ b k-(w b/w v)*R⁻¹ v k) := by
    change (∑i,(replicateRow Unit h * R⁻¹) () i * u i)=_
    simp [left,u,spike,mul_sub,sum_sub_distrib,mul_ite,mul_comm]
  change R.det*(1+(replicateRow Unit h * R⁻¹ * replicateCol Unit u) () ())*_=_
  rw [eval]; unfold test; field_simp [wv,pk]; ring

/-- A nonpositive entry occurs precisely when the balanced switch passes
through a singular matrix by the time the full insertion weight is reached. -/
theorem sign_iff {R : Matrix I I ℝ} (unit : IsUnit R.det) (w p : I→ℝ)
    (q : ℝ) (a b v k : I) (wv : 0<w v) (pk : 0<p k) :
    test R⁻¹ w p q a b v k ≤ 0 ↔
      ∃ s : ℝ, 0<s ∧ s≤1 ∧ (switch R w p (s*q) a b v k).det=0 := by
  let A := w v*p k
  let T := test R⁻¹ w p q a b v k
  have pos : 0<A := mul_pos wv pk
  have line (s : ℝ) : test R⁻¹ w p (s*q) a b v k=(1-s)*A+s*T := by
    dsimp [T,A,test]; ring
  have zero (s : ℝ) : (switch R w p (s*q) a b v k).det=0 ↔ (1-s)*A+s*T=0 := by
    have eq := determinant unit w p (s*q) a b v k wv.ne' pk.ne'
    rw [line] at eq
    constructor
    · intro h; rw [h,zero_mul] at eq; exact (mul_eq_zero.mp eq.symm).resolve_left unit.ne_zero
    · intro h; rw [h,mul_zero] at eq; exact (mul_eq_zero.mp eq).resolve_right pos.ne'
  change T≤0 ↔ _
  constructor
  · intro ht
    have pd : 0<A-T := by linarith
    refine ⟨A/(A-T),div_pos pos pd,(div_le_one pd).mpr (by linarith),(zero _).mpr ?_⟩
    field_simp [pd.ne']; ring
  · rintro ⟨s,sp,le,root⟩
    have z := (zero s).mp root
    exact nonpos_of_mul_nonpos_right (show s*T≤0 by linarith only [z,mul_nonneg (sub_nonneg.mpr le) pos.le]) sp

end Matrix

end LeanCH.BR.Closure.SingleArcSwitchSign
#print axioms LeanCH.BR.Closure.SingleArcSwitchSign.sign_iff
