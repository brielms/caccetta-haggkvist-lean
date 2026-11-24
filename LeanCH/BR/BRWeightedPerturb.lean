import LeanCH.BR.BRWeightedArithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-! A zero-coordinate column violation over a balanced equality core can
be perturbed to strictly positive weights with every extended row >1. -/
namespace LeanCH.BR.WeightedPerturb
open Finset Matrix WeightedArithmetic
open scoped Matrix

theorem finite_positive_affine {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f g : ι → ℚ) (hf : ∀ i ∈ S, 0 < f i) :
    ∃ e : ℚ, 0 < e ∧ ∀ t : ℚ, 0 ≤ t → t ≤ e → ∀ i ∈ S, 0 < f i + t * g i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨e, he, hkeep⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨d, hd, hsmall⟩ := exists_pos_mul_lt (hf a (Finset.mem_insert_self _ _)) |g a|
    refine ⟨min e d, lt_min he hd, ?_⟩
    intro t ht hte i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have htd : t ≤ d := hte.trans (min_le_right _ _)
      have hab := mul_le_mul_of_nonneg_left htd (abs_nonneg (g i))
      have hgb := neg_abs_le (g i)
      have hmul := mul_le_mul_of_nonneg_left hgb ht
      nlinarith
    · exact hkeep t ht (hte.trans (min_le_left _ _)) i hi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The matrix theorem is constructive over the rationals. The two vectors
a,b encode the new vertex's outgoing and incoming incidences in graph use.
No cycle claim is made here; graph safety is a separate statement. -/
theorem lift_zero_vertex {q : ℕ} (hq : 2 ≤ q) (A : Matrix V V ℤ)
    (w : V → ℚ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hr : rationalMatrix q A *ᵥ w = fun _ => 1)
    (hc : w ᵥ* rationalMatrix q A = fun _ => 1)
    (a b : V → ℤ)
    (ha : 1 ≤ (q : ℚ) * ∑ i, (a i : ℚ) * w i)
    (hb : 1 < (q : ℚ) * ∑ i, (b i : ℚ) * w i) :
    ∃ (p : V → ℚ) (t : ℚ), (∀ i, 0 < p i) ∧ 0 < t ∧ (∑ i, p i) + t = 1 ∧
      (∀ i, 1 < (rationalMatrix q A *ᵥ p) i + (q : ℚ) * (b i : ℚ) * t) ∧
      1 < t + (q : ℚ) * ∑ i, (a i : ℚ) * p i := by
  let delta : ℚ := (q : ℚ) * (∑ i, (b i : ℚ) * w i) - 1
  have hd : 0 < delta := by dsimp [delta]; linarith
  have hao : 1 < (q : ℚ) * ∑ i, (a i : ℚ) * w i :=
    lt_of_le_of_ne ha (Ne.symm (no_integer_linear_form_unit hq A w hr a))
  obtain ⟨h, hsolve⟩ := rational_surjective hq A (fun i => delta - (q : ℚ) * (b i : ℚ))
  have hmass : ∑ i, h i = -1 := by
    have hpair : w ⬝ᵥ (rationalMatrix q A *ᵥ h) = ∑ i, h i := by
      rw [Matrix.dotProduct_mulVec, hc]
      simp [dotProduct]
    rw [hsolve] at hpair
    have heval : w ⬝ᵥ (fun i => delta - (q : ℚ) * (b i : ℚ)) =
        delta * (∑ i, w i) - (q : ℚ) * ∑ i, (b i : ℚ) * w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heval, hsum] at hpair
    dsimp only [delta] at hpair
    linarith
  let f : Option V → ℚ := fun i => match i with
    | none => (q : ℚ) * (∑ j, (a j : ℚ) * w j) - 1
    | some j => w j
  let g : Option V → ℚ := fun i => match i with
    | none => 1 + (q : ℚ) * (∑ j, (a j : ℚ) * h j)
    | some j => h j
  have hf : ∀ i ∈ (Finset.univ : Finset (Option V)), 0 < f i := by
    intro i hi
    cases i with
    | none => dsimp [f]; linarith
    | some j => exact hw j
  obtain ⟨e, he, hkeep⟩ := finite_positive_affine Finset.univ f g hf
  let p : V → ℚ := fun i => w i + e * h i
  refine ⟨p, e, ?_, he, ?_, ?_, ?_⟩
  · intro i
    exact hkeep e he.le le_rfl (some i) (Finset.mem_univ _)
  · dsimp only [p]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hmass]
    ring
  · intro i
    have hp : p = w + e • h := rfl
    rw [hp, Matrix.mulVec_add, Matrix.mulVec_smul, hr, hsolve]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_pos he hd]
  · have hroot := hkeep e he.le le_rfl none (Finset.mem_univ _)
    change 0 < (q : ℚ) * (∑ j, (a j : ℚ) * w j) - 1 +
      e * (1 + (q : ℚ) * ∑ j, (a j : ℚ) * h j) at hroot
    have hs : (∑ i, (a i : ℚ) * p i) =
        (∑ i, (a i : ℚ) * w i) + e * ∑ i, (a i : ℚ) * h i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [p]
      ring
    rw [hs]
    nlinarith

end LeanCH.BR.WeightedPerturb
