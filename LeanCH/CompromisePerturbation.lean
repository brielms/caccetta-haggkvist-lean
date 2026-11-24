module

public import LeanCH.CompromiseInverse

set_option linter.style.header false

/-! Exact single-entry perturbation of an inverse-nonpositive matrix.
Below the threshold a*(-M^{-1})_{j,i}=1 an explicit nonnegative
counterweight survives; at or above it an explicit left certificate
exists. No graph or conjecture is assumed in this module. -/

open Finset CH.CompromiseGame CH.CompromiseInverse
public section

namespace CH.CompromisePerturbation

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def raiseEntry (M : V → V → ℝ) (i j : V) (a : ℝ) (v u : V) : ℝ :=
  M v u + if v = i ∧ u = j then a else 0

theorem row_raise (M : V → V → ℝ) (i j : V) (a : ℝ) (w : V → ℝ) (v : V) :
    row (raiseEntry M i j a) w v = row M w v + if v = i then a * w j else 0 := by
  by_cases h : v = i <;> simp [row, raiseEntry, h, add_mul, sum_add_distrib]

theorem col_raise (M : V → V → ℝ) (i j : V) (a : ℝ) (p : V → ℝ) (u : V) :
    col (raiseEntry M i j a) p u = col M p u + if u = j then a * p i else 0 := by
  by_cases h : u = j <;> simp [col, raiseEntry, h, mul_add, sum_add_distrib, mul_comm]

omit [DecidableEq V] in
theorem row_add (M : V → V → ℝ) (x y : V → ℝ) (v : V) :
    row M (fun u => x u + y u) v = row M x v + row M y v := by
  simp [row, mul_add, sum_add_distrib]

/-- A single column solving Mq=-e_i repairs the changed row exactly. -/
theorem survive_below (M : V → V → ℝ) (i j : V) (a : ℝ) (ha : 0 ≤ a)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (column : ∀ v, row M q v = if v = i then -1 else 0)
    (below : a * q j < 1) :
    ∃ y : V → ℝ, (∀ v, 0 ≤ y v) ∧ ∀ v, row (raiseEntry M i j a) y v < 0 := by
  let b := a * w j / (1 - a * q j)
  have denom : 0 < 1 - a * q j := by linarith
  have bn : 0 ≤ b := div_nonneg (mul_nonneg ha (hw j)) denom.le
  have be : b * (1 - a * q j) = a * w j := by
    exact div_mul_cancel₀ _ (ne_of_gt denom)
  let y := fun v => w v + b * q v
  refine ⟨y, fun v => add_nonneg (hw v) (mul_nonneg bn (hq v)), ?_⟩
  intro v
  rw [row_raise]
  change row M (fun u => w u + b * q u) v + (if v = i then a * y j else 0) < 0
  rw [row_add, row_scale, column]
  by_cases h : v = i
  · simp only [h, ite_true, mul_neg_one]
    dsimp [y]
    nlinarith [bad i]
  · simpa [h] using bad v

omit [DecidableEq V] in
theorem good_of_left (M : V → V → ℝ) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (positive : ∃ v, 0 < p v) (cols : ∀ u, 0 ≤ col M p u)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) : ∃ v, 0 ≤ row M w v := by
  classical
  by_contra h
  push Not at h
  have hn : payoff M w p < 0 := by
    apply sum_neg'
    · intro v _
      exact mul_nonpos_of_nonneg_of_nonpos (hp v) (h v).le
    · obtain ⟨v, hv⟩ := positive
      exact ⟨v, mem_univ v, mul_neg_of_pos_of_neg hv (h v)⟩
  have hnn : 0 ≤ payoff M w p := by
    rw [payoff_transpose]
    exact sum_nonneg (fun u _ => mul_nonneg (hw u) (cols u))
  linarith

/-- A row solving p^T M=-e_j^T becomes a left certificate at the threshold. -/
theorem certificate_above (M : V → V → ℝ) (i j : V) (a : ℝ) (ha : 0 ≤ a)
    (p : V → ℝ)
    (rowEq : ∀ u, col M p u = if u = j then -1 else 0)
    (above : 1 ≤ a * p i) :
    (∃ v, 0 < p v) ∧ ∀ u, 0 ≤ col (raiseEntry M i j a) p u := by
  have pi : 0 < p i := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt h)
    linarith
  refine ⟨⟨i, pi⟩, ?_⟩
  intro u
  rw [col_raise, rowEq]
  by_cases h : u = j
  · simp only [h, ite_true]
    linarith
  · simp [h]

@[expose] noncomputable def negativeInverse (M : Matrix V V ℝ) : Matrix V V ℝ := -(M⁻¹)

theorem negativeInverse_nonneg (M : Matrix V V ℝ)
    (sign : ∀ v u, M⁻¹ v u ≤ 0) : ∀ v u, 0 ≤ negativeInverse M v u := by
  intro v u
  exact neg_nonneg.mpr (sign v u)

theorem inverse_column (M : Matrix V V ℝ) (unit : IsUnit M) (i v : V) :
    row M (fun u => negativeInverse M u i) v = if v = i then -1 else 0 := by
  have he := M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp unit)
  change (M * (-(M⁻¹))) v i = _
  rw [Matrix.mul_neg, he]
  by_cases h : v = i <;> simp [h]

theorem inverse_row (M : Matrix V V ℝ) (unit : IsUnit M) (j u : V) :
    col M (fun v => negativeInverse M j v) u = if u = j then -1 else 0 := by
  have he := M.nonsing_inv_mul (M.isUnit_iff_isUnit_det.mp unit)
  change ((-(M⁻¹)) * M) j u = _
  rw [Matrix.neg_mul, he]
  by_cases h : u = j
  · subst u
    simp
  · simp [h, Ne.symm h]

theorem inverse_row_mass (M : Matrix V V ℝ) (unit : IsUnit M)
    (w : V → ℝ) (eta : ℝ) (rows : ∀ v, row M w v = -eta) (v : V) :
    eta * (∑ u, negativeInverse M v u) = w v := by
  have h := payoff_transpose M w (fun u => negativeInverse M v u)
  simp only [payoff, rows, inverse_row M unit] at h
  simp [mul_ite, ← sum_mul] at h
  nlinarith

theorem inverse_col_mass (M : Matrix V V ℝ) (unit : IsUnit M)
    (p : V → ℝ) (eta : ℝ) (cols : ∀ u, col M p u = -eta) (v : V) :
    eta * (∑ u, negativeInverse M u v) = p v := by
  have h := payoff_transpose M (fun u => negativeInverse M u v) p
  simp only [payoff, inverse_column M unit, cols] at h
  simp [mul_ite, ← sum_mul] at h
  nlinarith

/-- Complete threshold for repairing a single matrix entry. -/
theorem threshold_iff (M : Matrix V V ℝ) (unit : IsUnit M)
    (sign : ∀ v u, M⁻¹ v u ≤ 0)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, row M w0 v < 0)
    (i j : V) (a : ℝ) (ha : 0 ≤ a) :
    (∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ row (raiseEntry M i j a) w v) ↔
      1 ≤ a * negativeInverse M j i := by
  have qn := negativeInverse_nonneg M sign
  constructor
  · intro good
    by_contra h
    obtain ⟨y, hy, hb⟩ := survive_below M i j a ha w0 hw0 bad0
      (fun v => negativeInverse M v i) (fun v => qn v i)
      (inverse_column M unit i) (lt_of_not_ge h)
    obtain ⟨v, hv⟩ := good y hy
    linarith [hb v]
  · intro h
    have cert := certificate_above M i j a ha (fun v => negativeInverse M j v)
      (inverse_row M unit j) h
    exact good_of_left _ _ (qn j) cert.1 cert.2

end CH.CompromisePerturbation

#print axioms CH.CompromisePerturbation.survive_below
#print axioms CH.CompromisePerturbation.certificate_above
#print axioms CH.CompromisePerturbation.threshold_iff
