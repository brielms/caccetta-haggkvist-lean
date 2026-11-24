module

public import LeanCH.CompromiseSingleTarget

set_option linter.style.header false

/-! An actual deletion certificate propagates inverse-column ratio
bounds from every retained row to the deleted diagonal. At positive
diagonal, each coordinate admits a suitable active feedback target.
The target may depend on the coordinate; no uniform target is asserted. -/

open Finset CH.CompromiseGame CH.CompromiseInverse CH.CompromisePerturbation
open CH.CompromiseCertificateCone CH.CompromiseCritical CH.CompromiseArcMinimal
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseZeroDiagonal
public section

namespace CH.CompromiseInverseRatios

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ratio_propagation (M : Matrix V V ℝ) (unit : IsUnit M)
    (j k : V) (r : V → ℝ) (rn : ∀ v, 0 ≤ r v) (rj : r j = 0)
    (retained : ∀ u, u ≠ j → 0 ≤ col M r u) (omitted : col M r j < 0)
    (a : ℝ) (an : 0 ≤ a)
    (bound : ∀ u, u ≠ j → negativeInverse M u j ≤ a * negativeInverse M u k) :
    negativeInverse M j j ≤ a * negativeInverse M j k := by
  let S := (univ : Finset V).erase j
  have recoverJ := inverse_recovery M unit r j
  have recoverK := inverse_recovery M unit r k
  have splitJ := sum_erase_add (univ : Finset V)
    (fun u => col M r u * negativeInverse M u j) (mem_univ j)
  have splitK := sum_erase_add (univ : Finset V)
    (fun u => col M r u * negativeInverse M u k) (mem_univ j)
  have diagonal : (∑ u ∈ S, col M r u * negativeInverse M u j) =
      (-col M r j) * negativeInverse M j j := by
    rw [rj] at recoverJ
    dsimp [S]
    linarith
  have capacity : (∑ u ∈ S, col M r u * negativeInverse M u k) ≤
      (-col M r j) * negativeInverse M j k := by
    dsimp [S]
    linarith [rn k]
  have compare : (∑ u ∈ S, col M r u * negativeInverse M u j) ≤
      a * ∑ u ∈ S, col M r u * negativeInverse M u k := by
    rw [mul_sum]
    apply sum_le_sum
    intro u hu
    have uj := (mem_erase.mp hu).1
    have term := mul_le_mul_of_nonneg_left (bound u uj) (retained u uj)
    nlinarith
  have combined : (-col M r j) * negativeInverse M j j ≤
      (-col M r j) * (a * negativeInverse M j k) := by
    calc
      _ = ∑ u ∈ S, col M r u * negativeInverse M u j := diagonal.symm
      _ ≤ a * ∑ u ∈ S, col M r u * negativeInverse M u k := compare
      _ ≤ a * ((-col M r j) * negativeInverse M j k) :=
        mul_le_mul_of_nonneg_left capacity an
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (neg_pos.mpr omitted)).mp combined

theorem deletedLeft_ratio_propagation (M : Matrix V V ℝ) (unit : IsUnit M)
    (deleted : DeletedLeft M) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (bad : ∀ v, row M w v < 0) (j k : V) (a : ℝ) (an : 0 ≤ a)
    (bound : ∀ u, u ≠ j → negativeInverse M u j ≤ a * negativeInverse M u k) :
    negativeInverse M j j ≤ a * negativeInverse M j k := by
  obtain ⟨p, hp, pj, cols⟩ := deleted j
  have omitted : col M p j < 0 := by
    by_contra hn
    have allcols (u : V) : 0 ≤ col M p u := by
      by_cases uj : u = j
      · simpa only [uj] using le_of_not_gt hn
      · exact cols u uj
    have nonnegative : 0 ≤ payoff M w p := by
      erw [payoff_transpose]
      exact sum_nonneg (fun u _ => mul_nonneg (hw u) (allcols u))
    linarith [payoff_neg M w p hp bad]
  exact ratio_propagation M unit j k p hp.1 pj cols omitted a an bound

variable (adj : V → V → Prop) [DecidableRel adj]

theorem graph_ratio_propagation (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j k : V) (a : ℝ) (an : 0 ≤ a)
    (bound : ∀ u, u ≠ j → Q adj u j ≤ a * Q adj u k) :
    Q adj j j ≤ a * Q adj j k := by
  obtain ⟨unit, _⟩ := graph_inverse_nonpos adj deleted w hw bad
  obtain ⟨r, fair⟩ := deleted j
  have tp := (deleted_domination adj deleted w hw bad j r fair).1
  exact ratio_propagation (CH.CompromiseInverse.matrix adj) unit j k r fair.1
    (fair.2.1 j (by simp)) (retained_column adj j r fair)
    (by change col (coefficient adj) r j < 0; linarith) a an bound

theorem graph_ratio_witness (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j k : V) (a : ℝ) (an : 0 ≤ a) (exceeds : a * Q adj j k < Q adj j j) :
    ∃ u, u ≠ j ∧ a * Q adj u k < Q adj u j := by
  by_contra missing
  have bound (u : V) (uj : u ≠ j) : Q adj u j ≤ a * Q adj u k := by
    by_contra hn
    exact missing ⟨u, uj, lt_of_not_ge hn⟩
  have propagated := graph_ratio_propagation adj deleted w hw bad j k a an bound
  linarith

/-- Each coordinate can be paid by some positive retained-slack target
which hits the omitted inverse column. A single target working for all
coordinates is a strictly different assertion. -/
theorem active_target_at_coordinate (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j k : V) (qp : 0 < Q adj j j)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r)
    (omitted : col (coefficient adj) r j < 0) :
    ∃ u, u ≠ j ∧ 0 < col (coefficient adj) r u ∧ 0 < Q adj u j ∧
      Q adj j j * Q adj u k ≤ Q adj u j * Q adj j k := by
  let S := (univ : Finset V).erase j
  let c := col (coefficient adj) r
  let t := -c j
  have tp : 0 < t := neg_pos.mpr omitted
  have diagonal := retained_slack_diagonal_identity adj unit j r (fair.2.1 j (by simp))
  change (∑ u ∈ S, c u * Q adj u j) = t * Q adj j j at diagonal
  have massPositive : 0 < ∑ u ∈ S, c u * Q adj u j := by rw [diagonal]; exact mul_pos tp qp
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
  change r k = -∑ u, c u * Q adj u k at recover
  have split := sum_erase_add (univ : Finset V) (fun u => c u * Q adj u k) (mem_univ j)
  have capacity : (∑ u ∈ S, c u * Q adj u k) ≤ t * Q adj j k := by
    dsimp [S, t]
    linarith [fair.1 k]
  have cn (u : V) (hu : u ∈ S) : 0 ≤ c u := retained_column adj j r fair u (mem_erase.mp hu).1
  have nonnegative : 0 ≤ ∑ u ∈ S, c u *
      (Q adj u j * Q adj j k - Q adj j j * Q adj u k) := by
    have identity : (∑ u ∈ S, c u *
        (Q adj u j * Q adj j k - Q adj j j * Q adj u k)) =
        (∑ u ∈ S, c u * Q adj u j) * Q adj j k -
          Q adj j j * (∑ u ∈ S, c u * Q adj u k) := by
      simp only [mul_sub, sum_sub_distrib, sum_mul, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    rw [identity, diagonal]
    have scaled := mul_le_mul_of_nonneg_left capacity qp.le
    nlinarith
  by_contra missing
  have badTerm (u : V) (hu : u ∈ S) (cp : 0 < c u) (up : 0 < Q adj u j) :
      c u * (Q adj u j * Q adj j k - Q adj j j * Q adj u k) < 0 := by
    have reverse : Q adj u j * Q adj j k < Q adj j j * Q adj u k := by
      by_contra hn
      exact missing ⟨u, (mem_erase.mp hu).1, cp, up, le_of_not_gt hn⟩
    exact mul_neg_of_pos_of_neg cp (sub_neg.mpr reverse)
  have weak (u : V) (hu : u ∈ S) :
      c u * (Q adj u j * Q adj j k - Q adj j j * Q adj u k) ≤ 0 := by
    by_cases cp : 0 < c u
    · by_cases up : 0 < Q adj u j
      · exact (badTerm u hu cp up).le
      · have uz : Q adj u j = 0 := le_antisymm (le_of_not_gt up) (qn u j)
        rw [uz, zero_mul, zero_sub]
        exact mul_nonpos_of_nonneg_of_nonpos cp.le (neg_nonpos.mpr (mul_nonneg qp.le (qn u k)))
    · have cz : c u = 0 := le_antisymm (le_of_not_gt cp) (cn u hu)
      rw [cz, zero_mul]
  have one : ∃ u ∈ S, 0 < c u * Q adj u j := by
    by_contra hn
    push Not at hn
    have nonpos := sum_nonpos hn
    linarith
  obtain ⟨u, hu, product⟩ := one
  have cp : 0 < c u := by nlinarith [cn u hu, qn u j]
  have up : 0 < Q adj u j := by nlinarith [cn u hu, qn u j]
  have negative := sum_neg' weak ⟨u, hu, badTerm u hu cp up⟩
  linarith

end CH.CompromiseInverseRatios

#print axioms CH.CompromiseInverseRatios.ratio_propagation
#print axioms CH.CompromiseInverseRatios.deletedLeft_ratio_propagation
#print axioms CH.CompromiseInverseRatios.graph_ratio_propagation
#print axioms CH.CompromiseInverseRatios.graph_ratio_witness
#print axioms CH.CompromiseInverseRatios.active_target_at_coordinate
