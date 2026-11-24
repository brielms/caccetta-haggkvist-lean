import LeanCH.BR.BRsubSat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Homogeneous rational self-duality, including zero weights.
These statements concern arbitrary finite hosts and every cutoff q. -/
namespace LeanCH.BR.WeightedSD
open scoped BigOperators

def mass (V : Finset ℕ) (w : ℕ → ℚ) : ℚ := ∑ v ∈ V, w v
def outW (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (v : ℕ) : ℚ :=
  ∑ u ∈ V, if D v u = true then w u else 0
def inW (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (v : ℕ) : ℚ :=
  ∑ u ∈ V, if D u v = true then w u else 0
def row (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (v : ℕ) : ℚ :=
  w v + q * outW D V w v
def col (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (v : ℕ) : ℚ :=
  w v + q * inW D V w v

/-- Homogeneous form: no division by total mass or positivity of each weight
is assumed. In particular every zero-weight vertex remains in the conclusion. -/
def SelfDual (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ w : ℕ → ℚ, (∀ v ∈ V, 0 ≤ w v) →
    (∀ v ∈ V, mass V w ≤ row q D V w v) →
    ∀ v ∈ V, col q D V w v ≤ mass V w

theorem weighted_balance (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) :
    (∑ v ∈ V, w v * outW D V w v) = ∑ v ∈ V, w v * inW D V w v := by
  simp only [outW, inW, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> ring

theorem row_col_balance (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) :
    (∑ v ∈ V, w v * row q D V w v) = ∑ v ∈ V, w v * col q D V w v := by
  calc
    _ = (∑ v ∈ V, w v * w v) + q * ∑ v ∈ V, w v * outW D V w v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [row]
      ring
    _ = (∑ v ∈ V, w v * w v) + q * ∑ v ∈ V, w v * inW D V w v := by
      rw [weighted_balance]
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [col]
      ring

theorem mass_nonneg {V : Finset ℕ} {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v) :
    0 ≤ mass V w := Finset.sum_nonneg hw

theorem mass_zero_weights {V : Finset ℕ} {w : ℕ → ℚ}
    (hw : ∀ v ∈ V, 0 ≤ w v) (hz : mass V w = 0) : ∀ v ∈ V, w v = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg hw).mp hz

/-- Self-duality supplies a small row for every nonnegative weighting, not
just weightings already feasible at the total-mass threshold. -/
theorem exists_small_row {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hSD : SelfDual q D V) (hV : V.Nonempty) (w : ℕ → ℚ)
    (hw : ∀ v ∈ V, 0 ≤ w v) : ∃ v ∈ V, row q D V w v ≤ mass V w := by
  by_cases hz : mass V w = 0
  · obtain ⟨v, hv⟩ := hV
    have hzero := mass_zero_weights hw hz
    refine ⟨v, hv, ?_⟩
    have ho : outW D V w v = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      simp [hzero u hu]
    simp [row, hzero v hv, ho, hz]
  · by_contra hn
    push_neg at hn
    have hr : ∀ v ∈ V, mass V w ≤ row q D V w v := fun v hv => (hn v hv).le
    have hc := hSD w hw hr
    have hpos : ∃ v ∈ V, 0 < w v := by
      by_contra hp
      push_neg at hp
      apply hz
      exact Finset.sum_eq_zero (fun v hv => le_antisymm (hp v hv) (hw v hv))
    obtain ⟨v, hv, hvp⟩ := hpos
    have hlo : (∑ u ∈ V, w u * mass V w) < ∑ u ∈ V, w u * row q D V w u := by
      apply Finset.sum_lt_sum
      · intro u hu
        exact mul_le_mul_of_nonneg_left (hr u hu) (hw u hu)
      · exact ⟨v, hv, mul_lt_mul_of_pos_left (hn v hv) hvp⟩
    have hhi : (∑ u ∈ V, w u * col q D V w u) ≤ ∑ u ∈ V, w u * mass V w := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hc u hu) (hw u hu)
    rw [row_col_balance] at hlo
    exact (not_lt_of_ge hhi) hlo

/-- Feasibility plus self-duality forces every positive-weight row tight.
Zero-weight rows need not be tight and are deliberately excluded here. -/
theorem positive_row_eq {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hSD : SelfDual q D V) {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    {v : ℕ} (hv : v ∈ V) (hvp : 0 < w v) : row q D V w v = mass V w := by
  have hc := hSD w hw hr
  have hlo : ∀ u ∈ V, w u * mass V w ≤ w u * row q D V w u := by
    intro u hu
    exact mul_le_mul_of_nonneg_left (hr u hu) (hw u hu)
  have hhi : (∑ u ∈ V, w u * row q D V w u) ≤ ∑ u ∈ V, w u * mass V w := by
    rw [row_col_balance]
    exact Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hc u hu) (hw u hu))
  have heq := le_antisymm (Finset.sum_le_sum hlo) hhi
  have each := (Finset.sum_eq_sum_iff_of_le hlo).mp heq v hv
  exact (mul_left_cancel₀ (ne_of_gt hvp) each).symm

end LeanCH.BR.WeightedSD
