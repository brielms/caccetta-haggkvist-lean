module

public import LeanCH.CompromiseDeletionMixture
public import LeanCH.CompromiseZeroDiagonal

set_option linter.style.header false

/-! Positive retained slack can only move down the inclusion order of
inverse-row supports. Abstract nonnegative feedback with that property
can balance only inside a class of identical supports. No balance is
asserted for a graph counterexample. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseCertificateCone CH.CompromiseDeletionMixture CH.CompromiseZeroDiagonal
public section

namespace CH.CompromiseFeedbackSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] noncomputable def rowSupport (Q : V → V → ℝ) (j : V) : Finset V :=
  univ.filter (fun k => 0 < Q j k)

omit [DecidableEq V] in
theorem mem_rowSupport (Q : V → V → ℝ) (j k : V) :
    k ∈ rowSupport Q j ↔ 0 < Q j k := by
  classical
  simp only [rowSupport, mem_filter, mem_univ, true_and]

omit [DecidableEq V] in
/-- A general finite nonnegative-matrix reduction, independent of graph
counterexamples or inverse assumptions. A balanced vector can be cut
down to one class of identical supports without losing any column. -/
theorem balance_localizes (S : V → Finset V) (B : V → V → ℝ)
    (nonnegative : ∀ j u, 0 ≤ B j u)
    (down : ∀ j u, 0 < B j u → S u ⊆ S j)
    (b : V → ℝ) (bn : ∀ u, 0 ≤ b u) (bp : ∃ u, 0 < b u)
    (balance : ∀ u, b u ≤ col B b u) :
    ∃ j, ∃ c : V → ℝ, (∀ u, 0 ≤ c u) ∧ 0 < c j ∧
      (∀ u, S u ≠ S j → c u = 0) ∧ ∀ u, c u ≤ col B c u := by
  classical
  let P := univ.filter (fun u => 0 < b u)
  have pne : P.Nonempty := by
    obtain ⟨u, hu⟩ := bp
    exact ⟨u, by simp [P, hu]⟩
  obtain ⟨j, hj, largest⟩ := exists_max_image P (fun u => (S u).card) pne
  have bj : 0 < b j := (mem_filter.mp hj).2
  let c (u : V) := if S u = S j then b u else 0
  have cn (u : V) : 0 ≤ c u := by
    dsimp [c]
    split_ifs
    · exact bn u
    · rfl
  refine ⟨j, c, cn, by simpa only [c, ite_true] using bj, ?_, ?_⟩
  · intro u hu
    simp only [c, ite_eq_right hu]
  · intro u
    by_cases same : S u = S j
    · have column : col B c u = col B b u := by
        apply sum_congr rfl
        intro a _
        by_cases ba : 0 < b a
        · by_cases edge : 0 < B a u
          · have sub : S u ⊆ S a := down a u edge
            have card : (S a).card ≤ (S u).card := by
              rw [same]
              exact largest a (by simp [P, ba])
            have equal : S a = S j := (eq_of_subset_of_card_le sub card).symm.trans same
            simp only [c, ite_eq_left equal]
          · have zero : B a u = 0 := le_antisymm (le_of_not_gt edge) (nonnegative a u)
            simp only [zero, mul_zero]
        · have zero : b a = 0 := le_antisymm (le_of_not_gt ba) (bn a)
          simp only [c, zero, ite_self, zero_mul]
      simpa only [c, ite_eq_left same, column] using balance u
    · have zero : c u = 0 := by simp only [c, ite_eq_right same]
      rw [zero]
      exact sum_nonneg (fun a _ => mul_nonneg (cn a) (nonnegative a u))

omit [DecidableEq V] in
/-- If all support labels are distinct and feedback has zero diagonal,
there is no nonzero nonnegative balanced vector. -/
theorem distinct_supports_no_balance (S : V → Finset V) (B : V → V → ℝ)
    (nonnegative : ∀ j u, 0 ≤ B j u) (diagonal : ∀ j, B j j = 0)
    (down : ∀ j u, 0 < B j u → S u ⊆ S j) (distinct : Function.Injective S) :
    ¬ ∃ b : V → ℝ, (∀ u, 0 ≤ b u) ∧ (∃ u, 0 < b u) ∧ ∀ u, b u ≤ col B b u := by
  classical
  rintro ⟨b, bn, bp, balance⟩
  obtain ⟨j, c, _, cp, support, balanced⟩ := balance_localizes S B nonnegative down b bn bp balance
  have zero : col B c j = 0 := by
    apply sum_eq_zero
    intro a _
    by_cases aj : a = j
    · subst a
      rw [diagonal, mul_zero]
    · rw [support a (fun h => aj (distinct h)), zero_mul]
  have h := balanced j
  rw [zero] at h
  linarith

variable (adj : V → V → Prop) [DecidableRel adj]

/-- The inverse recovery identity propagates every zero of the source
row to every retained column with positive original slack. -/
theorem positive_slack_support (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r)
    (u : V) (uj : u ≠ j) (positive : 0 < col (coefficient adj) r u) :
    rowSupport (Q adj) u ⊆ rowSupport (Q adj) j := by
  intro k hk
  erw [mem_rowSupport] at hk ⊢
  by_contra hn
  have zero : Q adj j k = 0 := le_antisymm (le_of_not_gt hn) (qn j k)
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
  change r k = -∑ a, col (coefficient adj) r a * Q adj a k at recover
  have split := sum_erase_add (univ : Finset V)
    (fun a => col (coefficient adj) r a * Q adj a k) (mem_univ j)
  rw [zero, mul_zero, add_zero] at split
  have term := single_le_sum (s := univ.erase j)
    (fun a ha => mul_nonneg (retained_column adj j r fair a (mem_erase.mp ha).1) (qn a k))
    (show u ∈ univ.erase j by simp [uj])
  have product := mul_pos positive hk
  linarith [fair.1 k]

theorem feedback_support (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (negative : ∀ j, col (coefficient adj) (r j) j < 0)
    (j u : V) (positive : 0 < feedback adj r j u) :
    rowSupport (Q adj) u ⊆ rowSupport (Q adj) j := by
  have uj : u ≠ j := by intro h; simp only [feedback, h, ite_true] at positive; linarith
  rw [feedback, ite_eq_right uj] at positive
  have tp : 0 < -col (coefficient adj) (r j) j := neg_pos.mpr (negative j)
  have cp : 0 < col (coefficient adj) (r j) u := by
    simpa only [zero_mul] using (lt_div_iff₀ tp).mp positive
  exact positive_slack_support adj unit qn j (r j) (fair j) u uj cp

theorem feedback_balance_localizes (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (r : V → V → ℝ)
    (fair : ∀ j, FairOn adj (univ.erase j) (r j))
    (negative : ∀ j, col (coefficient adj) (r j) j < 0)
    (b : V → ℝ) (bn : ∀ u, 0 ≤ b u) (bp : ∃ u, 0 < b u)
    (balance : ∀ u, b u ≤ col (feedback adj r) b u) :
    ∃ j, ∃ c : V → ℝ, (∀ u, 0 ≤ c u) ∧ 0 < c j ∧
      (∀ u, rowSupport (Q adj) u ≠ rowSupport (Q adj) j → c u = 0) ∧
      ∀ u, c u ≤ col (feedback adj r) c u :=
  balance_localizes (rowSupport (Q adj)) (feedback adj r)
    (feedback_nonnegative adj r fair negative)
    (feedback_support adj unit qn r fair negative) b bn bp balance

/-- At a row whose support contains no other inverse-row support,
every actual deletion certificate lies on the same inverse ray. -/
theorem isolated_minimal_support_ray (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V)
    (minimal : ∀ u, rowSupport (Q adj) u ⊆ rowSupport (Q adj) j → u = j)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r) :
    (∀ u, u ≠ j → col (coefficient adj) r u = 0) ∧
      ∀ k, r k = (-col (coefficient adj) r j) * Q adj j k := by
  have tight (u : V) (uj : u ≠ j) : col (coefficient adj) r u = 0 := by
    apply le_antisymm _ (retained_column adj j r fair u uj)
    by_contra hn
    have inclusion := positive_slack_support adj unit qn j r fair u uj (lt_of_not_ge hn)
    exact uj (minimal u inclusion)
  refine ⟨tight, ?_⟩
  intro k
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
  change r k = -∑ a, col (coefficient adj) r a * Q adj a k at recover
  have split := sum_erase_add (univ : Finset V)
    (fun a => col (coefficient adj) r a * Q adj a k) (mem_univ j)
  have erased : (∑ a ∈ univ.erase j, col (coefficient adj) r a * Q adj a k) = 0 := by
    apply sum_eq_zero
    intro a ha
    rw [tight a (mem_erase.mp ha).1, zero_mul]
  rw [erased, zero_add] at split
  rw [← split] at recover
  linarith

theorem distinct_inverse_supports_zero_diagonal [Nonempty V]
    (deleted : DeletedFair adj) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (bad : ∀ v, surplus adj w v < 0)
    (distinct : Function.Injective (rowSupport (Q adj))) :
    ∃ j, Q adj j j = 0 ∧ ∀ r : V → ℝ, FairOn adj (univ.erase j) r →
      ∀ u, u ≠ j → col (coefficient adj) r u = 0 := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  obtain ⟨j, _, smallest⟩ := exists_min_image univ
    (fun u => (rowSupport (Q adj) u).card) univ_nonempty
  have minimal (u : V) (sub : rowSupport (Q adj) u ⊆ rowSupport (Q adj) j) : u = j := by
    exact distinct (eq_of_subset_of_card_le sub (smallest u (mem_univ u)))
  obtain ⟨r, fair⟩ := deleted j
  have ray := (isolated_minimal_support_ray adj unit qn j minimal r fair).2 j
  have tp := (deleted_domination adj deleted w hw bad j r fair).1
  have rj : r j = 0 := fair.2.1 j (by simp)
  have zero : Q adj j j = 0 := by rw [rj] at ray; nlinarith [qn j j]
  exact ⟨j, zero, fun r fair => (isolated_minimal_support_ray adj unit qn j minimal r fair).1⟩

/-- At a smallest inverse-row support, a private path forces every
actual deletion certificate to have positive feedback to a distinct
vertex with exactly the same support. -/
theorem private_middle_minimal_support_feedback (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (smallest : ∀ u, (rowSupport (Q adj) j).card ≤ (rowSupport (Q adj) u).card)
    (i : V) (edge : adj i j) (lost : (CH.CompromiseLostArc.lostSecond adj i j).Nonempty)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r) :
    ∃ u, u ≠ j ∧ rowSupport (Q adj) u = rowSupport (Q adj) j ∧
      0 < col (coefficient adj) r u ∧ 0 < Q adj u j := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  obtain ⟨u, uj, positive, quj⟩ := private_path_forces_retained_slack adj noLoop
    deleted minimal w hw bad i j edge lost r fair
  have sub := positive_slack_support adj unit qn j r fair u uj positive
  exact ⟨u, uj, eq_of_subset_of_card_le sub (smallest u), positive, quj⟩

/-- If every vertex is the middle of some private two-step path, then
a weighted minimal counterexample has two distinct inverse rows with
identical supports. Zero patterns alone cannot distinguish those rows. -/
theorem private_middles_force_repeated_support [Nonempty V]
    (noLoop : ∀ v, ¬ adj v v) (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (privateMiddle : ∀ j, ∃ i, adj i j ∧ (CH.CompromiseLostArc.lostSecond adj i j).Nonempty) :
    ∃ j u, j ≠ u ∧ rowSupport (Q adj) j = rowSupport (Q adj) u := by
  obtain ⟨j, _, smallest⟩ := exists_min_image univ
    (fun u => (rowSupport (Q adj) u).card) univ_nonempty
  obtain ⟨i, edge, lost⟩ := privateMiddle j
  obtain ⟨r, fair⟩ := deleted j
  obtain ⟨u, uj, equal, _, _⟩ := private_middle_minimal_support_feedback adj noLoop
    deleted minimal w hw bad j (fun u => smallest u (mem_univ u)) i edge lost r fair
  exact ⟨j, u, Ne.symm uj, equal.symm⟩

end CH.CompromiseFeedbackSupport

#print axioms CH.CompromiseFeedbackSupport.balance_localizes
#print axioms CH.CompromiseFeedbackSupport.distinct_supports_no_balance
#print axioms CH.CompromiseFeedbackSupport.positive_slack_support
#print axioms CH.CompromiseFeedbackSupport.feedback_support
#print axioms CH.CompromiseFeedbackSupport.feedback_balance_localizes
#print axioms CH.CompromiseFeedbackSupport.isolated_minimal_support_ray
#print axioms CH.CompromiseFeedbackSupport.distinct_inverse_supports_zero_diagonal
#print axioms CH.CompromiseFeedbackSupport.private_middle_minimal_support_feedback
#print axioms CH.CompromiseFeedbackSupport.private_middles_force_repeated_support
