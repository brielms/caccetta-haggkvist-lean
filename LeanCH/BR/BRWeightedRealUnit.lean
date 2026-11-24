import LeanCH.BR.BRWeightedArcInverse

/-! Real unit solutions inherit the checked rational nonzero-coordinate law. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix WeightedArithmetic
open scoped Matrix

theorem real_unit_coordinates_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ) (p : ι → ℝ)
    (hp : ((Rat.castHom ℝ).mapMatrix (rationalMatrix q A)) *ᵥ p = fun _ => 1) :
    ∀ i, p i ≠ 0 := by
  obtain ⟨r,hr⟩ := rational_surjective hq A (fun _ => 1)
  let R : Matrix ι ι ℝ := (Rat.castHom ℝ).mapMatrix (rationalMatrix q A)
  have hdet : R.det ≠ 0 := by
    dsimp only [R]
    rw [← RingHom.map_det]
    change ((rationalMatrix q A).det : ℝ) ≠ 0
    exact_mod_cast rational_det_ne_zero hq A
  have hu : IsUnit R := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrR : R *ᵥ (fun i => (r i : ℝ)) = fun _ => 1 := by
    funext i
    have hh := congrFun hr i
    change (∑ j, rationalMatrix q A i j * r j) = 1 at hh
    change (∑ j, (rationalMatrix q A i j : ℝ) * (r j : ℝ)) = 1
    exact_mod_cast hh
  have heq : (fun i => (r i : ℝ)) = p :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hu) (hrR.trans hp.symm)
  intro i hi
  have hz : (r i : ℝ) = 0 := (congrFun heq i).trans hi
  exact solution_coordinates_ne_zero hq A r hr i (by exact_mod_cast hz)

theorem real_unit_columns_positive {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} (p : ℕ → ℝ) (hp : ∀ x ∈ V, 0 ≤ p x)
    (hc : ∀ x ∈ V, realCol q D V p x = 1) : ∀ x ∈ V, 0 < p x := by
  let A := adjacencyMatrix D V
  have ht : rationalMatrix q A.transpose = (rationalMatrix q A).transpose := by
    ext i j
    simp [rationalMatrix,closedMatrix,Matrix.transpose_apply,eq_comm]
  have he : ((Rat.castHom ℝ).mapMatrix (rationalMatrix q A.transpose)) *ᵥ
      (fun i : V => p i) = fun _ => 1 := by
    rw [ht]
    funext i
    change (∑ j : V, (rationalMatrix q A j i : ℝ)*p j) = 1
    simp_rw [mul_comm]
    change ((fun j : V => p j) ᵥ* realMatrix q D V) i = 1
    exact (realMatrix_col q D V p i).trans (hc i i.property)
  have hn := real_unit_coordinates_ne_zero hq A.transpose (fun i : V => p i) he
  intro x hx
  exact lt_of_le_of_ne (hp x hx) (Ne.symm (hn ⟨x,hx⟩))

end LeanCH.BR.WeightedSD
