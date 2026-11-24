import LeanCH.BR.BRWeightedNormal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Rational form of the corpus finite-ratio inverse argument. Full support
is an explicit matrix hypothesis here; the graph bridge derives it from
proper induced self-duality. No minimax theorem is needed. -/
namespace LeanCH.BR.WeightedStrictNormal
open Finset Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def Full (B : Matrix V V ℚ) : Prop :=
  ∀ w : V → ℚ, (∀ i, 0 ≤ w i) → (∀ i, (B *ᵥ w) i < 0) → ∀ i, 0 < w i

theorem inverse_order (B : Matrix V V ℚ) (full : Full B)
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i) (bad : ∀ i, (B *ᵥ w) i < 0)
    (x : V → ℚ) (hx : ∀ i, 0 ≤ (B *ᵥ x) i) : ∀ i, x i ≤ 0 := by
  have wp := full w hw bad
  intro a
  by_contra ha
  have xa : 0 < x a := lt_of_not_ge ha
  obtain ⟨k, _, hmax⟩ := exists_max_image (univ : Finset V)
    (fun i => x i / w i) ⟨a, mem_univ a⟩
  let r := x k / w k
  have rp : 0 < r := (div_pos xa (wp a)).trans_le (hmax a (mem_univ a))
  let y : V → ℚ := r • w - x
  have yn (i : V) : 0 ≤ y i := by
    exact sub_nonneg.mpr ((div_le_iff₀ (wp i)).mp (hmax i (mem_univ i)))
  have yz : y k = 0 := by
    change r * w k - x k = 0
    dsimp [r]
    field_simp [ne_of_gt (wp k)]
    ring
  have ybad (i : V) : (B *ᵥ y) i < 0 := by
    rw [show y = r • w - x from rfl, Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [mul_neg_of_pos_of_neg rp (bad i), hx i]
  have hp := full y yn ybad k
  linarith

theorem mulVec_injective (B : Matrix V V ℚ) (full : Full B)
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i) (bad : ∀ i, (B *ᵥ w) i < 0) :
    Function.Injective (B *ᵥ ·) := by
  intro x y he
  change B *ᵥ x = B *ᵥ y at he
  have hxy : B *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
  have hyx : B *ᵥ (y - x) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
  have hn := inverse_order B full w hw bad (x - y) (fun i => by rw [hxy]; exact le_rfl)
  have hp := inverse_order B full w hw bad (y - x) (fun i => by rw [hyx]; exact le_rfl)
  funext i
  have hn' := hn i
  have hp' := hp i
  change x i - y i ≤ 0 at hn'
  change y i - x i ≤ 0 at hp'
  linarith

theorem matrix_isUnit (B : Matrix V V ℚ) (full : Full B)
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i) (bad : ∀ i, (B *ᵥ w) i < 0) : IsUnit B :=
  Matrix.mulVec_injective_iff_isUnit.mp (mulVec_injective B full w hw bad)

theorem inverse_nonpos (B : Matrix V V ℚ) (full : Full B)
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i) (bad : ∀ i, (B *ᵥ w) i < 0) :
    ∀ i j, B⁻¹ i j ≤ 0 := by
  have unit := matrix_isUnit B full w hw bad
  have inv := B.mul_nonsing_inv (B.isUnit_iff_isUnit_det.mp unit)
  intro i j
  apply inverse_order B full w hw bad (fun v => B⁻¹ v j) _ i
  intro v
  change 0 ≤ (B * B⁻¹) v j
  rw [inv]
  by_cases h : v = j <;> simp [Matrix.one_apply, h]

theorem reverse_positive (B : Matrix V V ℚ) (full : Full B)
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i) (bad : ∀ i, (B *ᵥ w) i < 0)
    (p : V → ℚ) (pb : ∀ i, (p ᵥ* B) i < 0) : ∀ i, 0 < p i := by
  have unit := matrix_isUnit B full w hw bad
  have inv := B.mul_nonsing_inv (B.isUnit_iff_isUnit_det.mp unit)
  have sign := inverse_nonpos B full w hw bad
  intro u
  have hn : ∃ v, B⁻¹ v u < 0 := by
    by_contra h
    push Not at h
    have hz (v : V) : B⁻¹ v u = 0 := le_antisymm (sign v u) (h v)
    have he := congrArg (fun A : Matrix V V ℚ => A u u) inv
    simp [Matrix.mul_apply, hz] at he
  have he : ((p ᵥ* B) ᵥ* B⁻¹) u = p u := by
    rw [Matrix.vecMul_vecMul, inv, Matrix.vecMul_one]
  rw [← he]
  apply sum_pos'
  · intro v _
    exact mul_nonneg_of_nonpos_of_nonpos (pb v).le (sign v u)
  · obtain ⟨v, hv⟩ := hn
    exact ⟨v, mem_univ v, mul_pos_of_neg_of_neg (pb v) hv⟩

theorem negative_equalizers (B : Matrix V V ℚ) (full : Full B)
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i) (bad : ∀ i, (B *ᵥ w) i < 0) :
    ∃ x p : V → ℚ, (∀ i, 0 < x i) ∧ (∀ i, 0 < p i) ∧
      B *ᵥ x = (fun _ => -1) ∧ p ᵥ* B = (fun _ => -1) ∧
      (∑ i, x i) = ∑ i, p i := by
  have unit := matrix_isUnit B full w hw bad
  obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr unit) (fun _ => -1)
  have xn : ∀ i, 0 ≤ x i := by
    have h := inverse_order B full w hw bad (-x) (by
      intro i
      rw [Matrix.mulVec_neg, hx]
      norm_num)
    intro i
    have hi := h i
    change -x i ≤ 0 at hi
    linarith
  have xp : ∀ i, 0 < x i := full x xn (fun i => by rw [hx]; norm_num)
  let p : V → ℚ := (fun _ => -1) ᵥ* B⁻¹
  have hp : p ᵥ* B = (fun _ => -1) := by
    dsimp only [p]
    rw [Matrix.vecMul_vecMul, B.nonsing_inv_mul (B.isUnit_iff_isUnit_det.mp unit),
      Matrix.vecMul_one]
  have pp := reverse_positive B full w hw bad p (fun i => by rw [hp]; norm_num)
  refine ⟨x, p, xp, pp, hx, hp, ?_⟩
  have hpair := Matrix.dotProduct_mulVec p B x
  rw [hx, hp] at hpair
  simpa [dotProduct, Finset.sum_neg_distrib] using hpair.symm

def deficit (R : Matrix V V ℚ) : Matrix V V ℚ := fun i j => 1 - R i j

theorem deficit_mulVec (R : Matrix V V ℚ) (w : V → ℚ) (i : V) :
    (deficit R *ᵥ w) i = (∑ j, w j) - (R *ᵥ w) i := by
  simp [deficit, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

theorem deficit_vecMul (R : Matrix V V ℚ) (p : V → ℚ) (i : V) :
    (p ᵥ* deficit R) i = (∑ j, p j) - (p ᵥ* R) i := by
  simp [deficit, Matrix.vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]

/-- A rational strict row witness with unavoidable full support yields
positive probabilities equalizing rows and columns at the same value >1. -/
theorem strict_normal_form [Nonempty V] (R : Matrix V V ℚ) (full : Full (deficit R))
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i)
    (bad : ∀ i, (∑ j, w j) < (R *ᵥ w) i) :
    ∃ x p : V → ℚ, ∃ c : ℚ, 1 < c ∧ (∀ i, 0 < x i) ∧ (∀ i, 0 < p i) ∧
      (∑ i, x i) = 1 ∧ (∑ i, p i) = 1 ∧
      (∀ i, (R *ᵥ x) i = c) ∧ (∀ i, (p ᵥ* R) i = c) := by
  have hb : ∀ i, (deficit R *ᵥ w) i < 0 := by
    intro i
    rw [deficit_mulVec]
    linarith [bad i]
  obtain ⟨x, p, hx, hp, hr, hc, hm⟩ := negative_equalizers (deficit R) full w hw hb
  let t : ℚ := ∑ i, x i
  have ht : 0 < t := Finset.sum_pos (fun i _ => hx i) Finset.univ_nonempty
  let z : V → ℚ := t⁻¹ • x
  let r : V → ℚ := t⁻¹ • p
  have htz : ∑ i, z i = 1 := by
    change (∑ i, t⁻¹ * x i) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt ht)
  have htr : ∑ i, r i = 1 := by
    change (∑ i, t⁻¹ * p i) = 1
    rw [← Finset.mul_sum, ← hm]
    exact inv_mul_cancel₀ (ne_of_gt ht)
  refine ⟨z, r, 1 + t⁻¹, by linarith [inv_pos.mpr ht],
    (fun i => mul_pos (inv_pos.mpr ht) (hx i)),
    (fun i => mul_pos (inv_pos.mpr ht) (hp i)), htz, htr, ?_, ?_⟩
  · intro i
    have hi := congrFun hr i
    rw [deficit_mulVec] at hi
    have hz : R *ᵥ z = t⁻¹ • (R *ᵥ x) := Matrix.mulVec_smul R t⁻¹ x
    rw [hz]
    simp only [Pi.smul_apply, smul_eq_mul]
    change t - (R *ᵥ x) i = -1 at hi
    have he : (R *ᵥ x) i = t + 1 := by linarith
    rw [he, mul_add, inv_mul_cancel₀ (ne_of_gt ht), mul_one]
  · intro i
    have hi := congrFun hc i
    rw [deficit_vecMul, ← hm] at hi
    have hz : r ᵥ* R = t⁻¹ • (p ᵥ* R) := Matrix.smul_vecMul t⁻¹ p R
    rw [hz]
    simp only [Pi.smul_apply, smul_eq_mul]
    change t - (p ᵥ* R) i = -1 at hi
    have he : (p ᵥ* R) i = t + 1 := by linarith
    rw [he, mul_add, inv_mul_cancel₀ (ne_of_gt ht), mul_one]

end LeanCH.BR.WeightedStrictNormal
