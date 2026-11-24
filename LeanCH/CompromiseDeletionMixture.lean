module

public import LeanCH.CompromiseTwoDeletions

set_option linter.style.header false

/-! Simultaneous mixtures of genuine vertex-deletion certificates.
The balance condition is an explicit input. A strict counterweight
contracts every row of the normalized retained-slack matrix. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseCertificateCone CH.CompromisePerturbation
public section

namespace CH.CompromiseDeletionMixture

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def mixture (r : V → V → ℝ) (a : V → ℝ) (v : V) : ℝ :=
  ∑ j, a j * r j v

omit [DecidableEq V] in
theorem mixture_column (M : V → V → ℝ) (r : V → V → ℝ) (a : V → ℝ) (u : V) :
    col M (mixture r a) u = ∑ j, a j * col M (r j) u := by
  simp only [col, mixture, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

variable (adj : V → V → Prop) [DecidableRel adj]

/-- Every omitted column is paid simultaneously, using one common
nonnegative coefficient vector for the actual induced certificates. -/
theorem mixture_fair (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (a : V → ℝ) (an : ∀ j, 0 ≤ a j) (ap : ∃ j, 0 < a j)
    (balance : ∀ u, a u * (-col (coefficient adj) (r u) u) ≤
      ∑ j ∈ univ.erase u, a j * col (coefficient adj) (r j) u) :
    Fair adj (mixture r a) := by
  have pn (v : V) : 0 ≤ mixture r a v :=
    sum_nonneg (fun j _ => mul_nonneg (an j) ((fair j).1 v))
  have positive : ∃ v, 0 < mixture r a v := by
    obtain ⟨j, hj⟩ := ap
    obtain ⟨v, _, hv⟩ := (fair j).2.2.1
    have lower : a j * r j v ≤ mixture r a v :=
      single_le_sum (fun k _ => mul_nonneg (an k) ((fair k).1 v)) (mem_univ j)
    exact ⟨v, (mul_pos hj hv).trans_le lower⟩
  refine ⟨pn, positive, ?_⟩
  intro u
  have split := sum_erase_add (univ : Finset V)
    (fun j => a j * col (coefficient adj) (r j) u) (mem_univ u)
  have nonneg : 0 ≤ col (coefficient adj) (mixture r a) u := by
    rw [mixture_column]
    nlinarith [balance u]
  rw [col_coefficient] at nonneg
  dsimp [slack] at nonneg
  linarith

theorem mixture_compromise (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (a : V → ℝ) (an : ∀ j, 0 ≤ a j) (ap : ∃ j, 0 < a j)
    (balance : ∀ u, a u * (-col (coefficient adj) (r u) u) ≤
      ∑ j ∈ univ.erase u, a j * col (coefficient adj) (r j) u)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) : ∃ v, 0 ≤ surplus adj w v := by
  obtain ⟨v, _, hv⟩ := compromise_of_fair adj (mixture r a) w
    (mixture_fair adj r fair a an ap balance) hw
  refine ⟨v, ?_⟩
  dsimp [surplus]
  linarith

@[expose] noncomputable def feedback (r : V → V → ℝ) (j u : V) : ℝ :=
  if u = j then 0 else col (coefficient adj) (r j) u / (-col (coefficient adj) (r j) j)

theorem feedback_nonnegative (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (negative : ∀ j, col (coefficient adj) (r j) j < 0) (j u : V) :
    0 ≤ feedback adj r j u := by
  unfold feedback
  split_ifs with h
  · rfl
  · exact div_nonneg (retained_column adj j (r j) (fair j) u h) (neg_pos.mpr (negative j)).le

/-- The normalized balance vector gives an explicit common mixture.
Its coefficients are divided by their own omitted deficits. -/
theorem feedback_mixture_fair (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (negative : ∀ j, col (coefficient adj) (r j) j < 0)
    (b : V → ℝ) (prob : b ∈ simplex)
    (balance : ∀ u, b u ≤ col (feedback adj r) b u) :
    Fair adj (mixture r (fun j => b j / (-col (coefficient adj) (r j) j))) := by
  have tp (j : V) : 0 < -col (coefficient adj) (r j) j := neg_pos.mpr (negative j)
  apply mixture_fair adj r fair _ (fun j => div_nonneg (prob.1 j) (tp j).le)
  · obtain ⟨j, hj⟩ := simplex_has_positive prob
    exact ⟨j, div_pos hj (tp j)⟩
  · intro u
    rw [div_mul_cancel₀ _ (ne_of_gt (tp u))]
    have split := sum_erase_add (univ : Finset V)
      (fun j => b j * feedback adj r j u) (mem_univ u)
    have diagonal : feedback adj r u u = 0 := by simp only [feedback, ite_true]
    rw [diagonal, mul_zero, add_zero] at split
    have normalized : (∑ j ∈ univ.erase u,
        b j / (-col (coefficient adj) (r j) j) * col (coefficient adj) (r j) u) =
        col (feedback adj r) b u := by
      rw [col, ← split]
      apply sum_congr rfl
      intro j hj
      rw [feedback, ite_eq_right (Ne.symm (mem_erase.mp hj).1)]
      ring
    rw [normalized]
    exact balance u

/-- An exact finite-dimensional alternative for this fixed family.
Failure of a simultaneous balance is equivalent to a positive common
contraction weight. No graph counterweight is concluded from it. -/
theorem feedback_balance_iff [Nonempty V] (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (negative : ∀ j, col (coefficient adj) (r j) j < 0) :
    (∃ b ∈ simplex, ∀ u, b u ≤ col (feedback adj r) b u) ↔
      ¬ ∃ w ∈ simplex, (∀ u, 0 < w u) ∧
        ∀ j, row (feedback adj r) w j < w j := by
  let H (j u : V) : ℝ := feedback adj r j u - if u = j then 1 else 0
  have hr (w : V → ℝ) (j : V) : row H w j = row (feedback adj r) w j - w j := by
    simp [row, H, sub_mul, sum_sub_distrib, ite_mul]
  have hc (b : V → ℝ) (u : V) : col H b u = col (feedback adj r) b u - b u := by
    simp [col, H, mul_sub, sum_sub_distrib, mul_ite]
  constructor
  · rintro ⟨b, hb, balance⟩ ⟨w, hw, _, contraction⟩
    apply (fair_iff_no_bad H).mp ⟨b, hb, ?_⟩ ⟨w, hw, ?_⟩
    · intro u
      rw [hc]
      exact sub_nonneg.mpr (balance u)
    · intro j
      rw [hr]
      exact sub_neg.mpr (contraction j)
  · intro noContraction
    have noBad : ¬ ∃ w ∈ simplex, ∀ j, row H w j < 0 := by
      rintro ⟨w, hw, bad⟩
      have contraction (j : V) : row (feedback adj r) w j < w j := by
        have h := bad j
        rw [hr] at h
        exact sub_neg.mp h
      apply noContraction
      refine ⟨w, hw, ?_, contraction⟩
      intro u
      have nonnegative : 0 ≤ row (feedback adj r) w u :=
        sum_nonneg (fun j _ =>
          mul_nonneg (feedback_nonnegative adj r fair negative u j) (hw.1 j))
      exact nonnegative.trans_lt (contraction u)
    obtain ⟨b, hb, balance⟩ := (fair_iff_no_bad H).mpr noBad
    refine ⟨b, hb, ?_⟩
    intro u
    have h := balance u
    rw [hc] at h
    exact sub_nonneg.mp h

/-- One strict counterweight supplies the same strict contraction
weight for every actual deletion certificate in the family. -/
theorem feedback_contraction (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0) (j : V) :
    0 < w j ∧ 0 < -col (coefficient adj) (r j) j ∧
      (∑ u, feedback adj r j u * w u) < w j := by
  obtain ⟨wp, neg, _⟩ := singleton_fair_budget adj w hw bad j (r j) (fair j)
  rw [← col_coefficient] at neg
  have tp : 0 < -col (coefficient adj) (r j) j := neg_pos.mpr neg
  have payoffNegative : payoff (coefficient adj) w (r j) < 0 := by
    apply sum_neg'
    · intro v _
      rw [row_coefficient]
      exact mul_nonpos_of_nonneg_of_nonpos ((fair j).1 v) (bad v).le
    · obtain ⟨v, _, hv⟩ := (fair j).2.2.1
      refine ⟨v, mem_univ v, ?_⟩
      rw [row_coefficient]
      exact mul_neg_of_pos_of_neg hv (bad v)
  rw [payoff_transpose] at payoffNegative
  have split := sum_erase_add (univ : Finset V)
    (fun u => w u * col (coefficient adj) (r j) u) (mem_univ j)
  have raw : (∑ u ∈ univ.erase j, w u * col (coefficient adj) (r j) u) <
      w j * (-col (coefficient adj) (r j) j) := by nlinarith
  have normalized : (∑ u, feedback adj r j u * w u) =
      (∑ u ∈ univ.erase j, w u * col (coefficient adj) (r j) u) /
        (-col (coefficient adj) (r j) j) := by
    have erase := sum_erase_add (univ : Finset V)
      (fun u => feedback adj r j u * w u) (mem_univ j)
    have diagonal : feedback adj r j j = 0 := by simp only [feedback, ite_true]
    rw [diagonal, zero_mul, add_zero] at erase
    rw [← erase, sum_div]
    apply sum_congr rfl
    intro u hu
    rw [feedback, ite_eq_right (mem_erase.mp hu).1]
    ring
  refine ⟨wp, tp, ?_⟩
  rw [normalized]
  exact (div_lt_iff₀ tp).mpr raw

theorem flat_positive_feedback_edge (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j)) (j u : V)
    (flat : localSlack adj (r j) (univ.erase j) u = 0)
    (positive : 0 < feedback adj r j u) : adj j u := by
  by_contra noEdge
  have empty := gained_singleton_empty adj j u noEdge
  have ident := fair_deletion_identity adj (r j) (univ.erase j) (fair j).2.1 u
  rw [flat, empty] at ident
  simp only [mass, sum_empty, add_zero] at ident
  have zero : col (coefficient adj) (r j) u = 0 := by rw [col_coefficient, ident]
  simp only [feedback, zero, zero_div, ite_self] at positive
  linarith

end CH.CompromiseDeletionMixture

#print axioms CH.CompromiseDeletionMixture.mixture_fair
#print axioms CH.CompromiseDeletionMixture.mixture_compromise
#print axioms CH.CompromiseDeletionMixture.feedback_mixture_fair
#print axioms CH.CompromiseDeletionMixture.feedback_balance_iff
#print axioms CH.CompromiseDeletionMixture.feedback_contraction
#print axioms CH.CompromiseDeletionMixture.flat_positive_feedback_edge
