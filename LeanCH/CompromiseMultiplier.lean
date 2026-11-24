module

public import LeanCH.CompromiseWeighted

set_option linter.style.header false

/-! Nonnegative multipliers for weighted compromise. These are sufficient
conditions, not assertions that every graph has such a multiplier. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted
public section

namespace CH.CompromiseMultiplier

variable {V : Type*} [Fintype V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def headAverage (w f : V → ℝ) (v : V) : ℝ :=
  ∑ a ∈ outN adj v, w a * f a

theorem multiplier_balance (w f : V → ℝ) :
    ∑ v, w v * headAverage adj w f v =
      ∑ v, w v * (f v * inWeight adj w v) := by
  have h := weighted_double_count adj w (fun v => w v * f v)
  change (∑ v, w v * headAverage adj w f v) =
    ∑ v, (w v * f v) * inWeight adj w v at h
  simpa only [mul_assoc] using h

/-- A head-average certificate can have zero entries. Its positive weighted
support contains a geometric-compromise vertex. -/
theorem geometric_of_multiplier (w s f : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, 0 ≤ s v) (hf : ∀ v, 0 ≤ f v)
    (support : ∃ v, 0 < w v * f v)
    (cert : ∀ v, (outWeight adj w v) ^ 2 * f v ≤
      s v * headAverage adj w f v) :
    ∃ v, 0 < w v * f v ∧
      (outWeight adj w v) ^ 2 ≤ inWeight adj w v * s v := by
  by_contra hn
  have bad (v : V) (hv : 0 < w v * f v) :
      inWeight adj w v * s v < (outWeight adj w v) ^ 2 := by
    have : ¬ (outWeight adj w v) ^ 2 ≤ inWeight adj w v * s v :=
      fun h => hn ⟨v, hv, h⟩
    linarith
  have weak (v : V) : w v * (f v * inWeight adj w v) ≤
      w v * headAverage adj w f v := by
    have hh : 0 ≤ headAverage adj w f v :=
      sum_nonneg (fun a _ => mul_nonneg (hw a) (hf a))
    by_cases hp : 0 < w v * f v
    · have fp : 0 < f v := by
        by_contra h
        have hz : f v = 0 := by linarith [hf v]
        simp [hz] at hp
      have hb := mul_lt_mul_of_pos_right (bad v hp) fp
      have hc := cert v
      have hi : f v * inWeight adj w v < headAverage adj w f v := by
        by_contra h
        have hr : headAverage adj w f v ≤ f v * inWeight adj w v := by linarith
        have hm := mul_le_mul_of_nonneg_left hr (hs v)
        nlinarith
      exact mul_le_mul_of_nonneg_left hi.le (hw v)
    · have hz : w v * f v = 0 := by nlinarith [mul_nonneg (hw v) (hf v)]
      rw [← mul_assoc, hz, zero_mul]
      exact mul_nonneg (hw v) hh
  obtain ⟨v, hv⟩ := support
  have wp : 0 < w v := by
    by_contra h
    have hz : w v = 0 := by linarith [hw v]
    simp [hz] at hv
  have fp : 0 < f v := by
    by_contra h
    have hz : f v = 0 := by linarith [hf v]
    simp [hz] at hv
  have hb := mul_lt_mul_of_pos_right (bad v hv) fp
  have hi : f v * inWeight adj w v < headAverage adj w f v := by
    by_contra h
    have hr : headAverage adj w f v ≤ f v * inWeight adj w v := by linarith
    have hm := mul_le_mul_of_nonneg_left hr (hs v)
    have hc := cert v
    nlinarith
  have hsum := sum_lt_sum (fun a (_ : a ∈ (univ : Finset V)) => weak a)
    ⟨v, mem_univ _, mul_lt_mul_of_pos_left hi wp⟩
  have heq := multiplier_balance adj w f
  linarith

/-- The additive certificate is weaker than demanding a lower bound on every
head separately. The conclusion is again on the positive weighted support. -/
theorem compromise_of_multiplier (w s f : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hf : ∀ v, 0 ≤ f v)
    (support : ∃ v, 0 < w v * f v)
    (cert : ∀ v, (2 * outWeight adj w v - s v) * f v ≤ headAverage adj w f v) :
    ∃ v, 0 < w v * f v ∧
      2 * outWeight adj w v ≤ inWeight adj w v + s v := by
  by_contra hn
  have strict (v : V) (hv : 0 < w v * f v) :
      w v * (f v * inWeight adj w v) < w v * headAverage adj w f v := by
    have hb : inWeight adj w v < 2 * outWeight adj w v - s v := by
      have hh : ¬ 2 * outWeight adj w v ≤ inWeight adj w v + s v :=
        fun h => hn ⟨v, hv, h⟩
      linarith
    have h1 := mul_lt_mul_of_pos_left hb hv
    have h2 := mul_le_mul_of_nonneg_left (cert v) (hw v)
    nlinarith
  have weak (v : V) : w v * (f v * inWeight adj w v) ≤
      w v * headAverage adj w f v := by
    by_cases hp : 0 < w v * f v
    · exact (strict v hp).le
    · have hz : w v * f v = 0 := by nlinarith [mul_nonneg (hw v) (hf v)]
      rw [← mul_assoc, hz, zero_mul]
      exact mul_nonneg (hw v) (sum_nonneg (fun a _ => mul_nonneg (hw a) (hf a)))
  obtain ⟨v, hv⟩ := support
  have hsum := sum_lt_sum (fun a (_ : a ∈ (univ : Finset V)) => weak a)
    ⟨v, mem_univ _, strict v hv⟩
  have heq := multiplier_balance adj w f
  linarith

end CH.CompromiseMultiplier

#print axioms CH.CompromiseMultiplier.multiplier_balance
#print axioms CH.CompromiseMultiplier.geometric_of_multiplier
#print axioms CH.CompromiseMultiplier.compromise_of_multiplier
