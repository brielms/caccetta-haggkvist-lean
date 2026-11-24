module

public import LeanCH.CompromisePerturbation

set_option linter.style.header false

/-! Repairing a signed change in one matrix row. The changed row may
have both positive and negative entries, so this retains lost endpoints
instead of bounding only the single positive entry. -/

open Finset CH.CompromiseGame CH.CompromiseInverse CH.CompromisePerturbation
public section

namespace CH.CompromiseRowRepair

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def pairing (h x : V → ℝ) : ℝ := ∑ u, h u * x u

@[expose] def shiftRow (M : V → V → ℝ) (i : V) (h : V → ℝ) (v u : V) : ℝ :=
  M v u + if v = i then h u else 0

theorem row_shift (M : V → V → ℝ) (i : V) (h x : V → ℝ) (v : V) :
    row (shiftRow M i h) x v = row M x v + if v = i then pairing h x else 0 := by
  by_cases hv : v = i <;> simp [row, shiftRow, pairing, hv, add_mul, sum_add_distrib]

omit [DecidableEq V] in
theorem pairing_add_scale (h w q : V → ℝ) (b : ℝ) :
    pairing h (fun v => w v + b * q v) = pairing h w + b * pairing h q := by
  simp only [pairing, mul_add, sum_add_distrib, mul_left_comm, mul_sum]

/-- Even a signed row change is repairable when its gain on the
nonnegative inverse column is below one. -/
theorem survive_signed_row (M : V → V → ℝ) (i : V) (h : V → ℝ)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (column : ∀ v, row M q v = if v = i then -1 else 0)
    (below : pairing h q < 1) :
    ∃ y : V → ℝ, (∀ v, 0 ≤ y v) ∧ ∀ v, row (shiftRow M i h) y v < 0 := by
  let b := max (pairing h w) 0 / (1 - pairing h q)
  have denom : 0 < 1 - pairing h q := by linarith
  have bn : 0 ≤ b := div_nonneg (le_max_right _ _) denom.le
  have be : b * (1 - pairing h q) = max (pairing h w) 0 :=
    div_mul_cancel₀ _ (ne_of_gt denom)
  let y := fun v => w v + b * q v
  refine ⟨y, fun v => add_nonneg (hw v) (mul_nonneg bn (hq v)), ?_⟩
  intro v
  rw [row_shift]
  change row M (fun u => w u + b * q u) v +
    (if v = i then pairing h (fun u => w u + b * q u) else 0) < 0
  rw [row_add, row_scale, column, pairing_add_scale]
  by_cases hv : v = i
  · simp only [ite_eq_left hv]
    have hwmax : pairing h w ≤ max (pairing h w) 0 := le_max_left _ _
    nlinarith [bad v]
  · simpa [hv] using bad v

/-- A matrix bounded by the signed row change cannot be good for all
nonnegative weights unless the inverse-column gain reaches one. -/
theorem threshold_of_good (M N : V → V → ℝ) (i : V) (h : V → ℝ)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (column : ∀ v, row M q v = if v = i then -1 else 0)
    (bound : ∀ v u, N v u ≤ shiftRow M i h v u)
    (good : ∀ y : V → ℝ, (∀ v, 0 ≤ y v) → ∃ v, 0 ≤ row N y v) :
    1 ≤ pairing h q := by
  by_contra hn
  obtain ⟨y, hy, hb⟩ := survive_signed_row M i h w hw bad q hq column (lt_of_not_ge hn)
  obtain ⟨v, hv⟩ := good y hy
  have he : row N y v ≤ row (shiftRow M i h) y v :=
    sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (bound v u) (hy u))
  linarith [hb v]

end CH.CompromiseRowRepair

#print axioms CH.CompromiseRowRepair.survive_signed_row
#print axioms CH.CompromiseRowRepair.threshold_of_good
