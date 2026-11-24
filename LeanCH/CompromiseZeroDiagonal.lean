module

public import LeanCH.CompromiseDiagonalLoss
public import LeanCH.CompromiseCertificateCone

set_option linter.style.header false

/-! Every zero inverse diagonal gives a genuine zero-slack probability
certificate of the corresponding vertex deletion. All other certificates
of that deletion are tight at the positive entries of its inverse column. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseFair
open CH.CompromiseEndpointDeletion CH.CompromiseCertificateCone
open CH.CompromiseDiagonalLoss CH.CompromiseColumnCoupling CH.CompromiseLostArc
public section

namespace CH.CompromiseZeroDiagonal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem inverse_row_total_positive (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) : 0 < ∑ v, Q adj j v := by
  have positive : ∃ v, 0 < Q adj j v := by
    by_contra hn
    push Not at hn
    have zero (v : V) : Q adj j v = 0 := le_antisymm (hn v) (qn j v)
    have inv := inverse_row (CH.CompromiseInverse.matrix adj) unit j j
    change col (coefficient adj) (fun v => Q adj j v) j = _ at inv
    simp only [col, zero, zero_mul, sum_const_zero, ite_true] at inv
    norm_num at inv
  obtain ⟨v, hv⟩ := positive
  exact sum_pos' (fun u _ => qn j u) ⟨v, mem_univ v, hv⟩

theorem zero_diagonal_certificate (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (zero : Q adj j j = 0) :
    (0 < ∑ v, Q adj j v) ∧
      (∀ v, CH.CompromiseSubset.localSecond adj (univ.erase j) v =
        second adj v ∩ univ.erase j) ∧
      ∃ p ∈ simplex, FairOn adj (univ.erase j) p ∧
        (∀ v, p v = Q adj j v / ∑ u, Q adj j u) ∧
        ∀ u, u ≠ j → localSlack adj p (univ.erase j) u = 0 := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have tp := inverse_row_total_positive adj unit qn j
  have noLoss := zero_diagonal_vertex_losses adj noLoop deleted minimal w hw bad j zero
  let p : V → ℝ := fun v => Q adj j v / ∑ u, Q adj j u
  have hp : p ∈ simplex := by
    refine ⟨fun v => div_nonneg (qn j v) tp.le, ?_⟩
    dsimp [p]
    rw [← sum_div, div_self (ne_of_gt tp)]
  have pj : p j = 0 := by simp only [p, zero, zero_div]
  have cols (u : V) (uj : u ≠ j) : col (coefficient adj) p u = 0 := by
    have inv := inverse_row (CH.CompromiseInverse.matrix adj) unit j u
    change col (coefficient adj) (fun v => Q adj j v) u = _ at inv
    have scale : col (coefficient adj) p u =
        col (coefficient adj) (fun v => Q adj j v) u / ∑ v, Q adj j v := by
      simp only [col, p, div_mul_eq_mul_div, sum_div]
    rw [scale, inv, ite_eq_right uj, zero_div]
  obtain ⟨fair, slacks⟩ := zero_slack_fair_on adj j p hp pj cols noLoss
  exact ⟨tp, local_second_eq_of_no_loss adj j noLoss, p, hp, fair, fun _ => rfl, slacks⟩

/-- The omitted coordinate accounts exactly for all retained slack.
This identity does not require the inverse diagonal to vanish. -/
theorem retained_slack_diagonal_identity (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (r : V → ℝ) (rj : r j = 0) :
    (∑ u ∈ univ.erase j, col (coefficient adj) r u * Q adj u j) =
      (-col (coefficient adj) r j) * Q adj j j := by
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r j
  change r j = -∑ u, col (coefficient adj) r u * Q adj u j at recover
  have split := sum_erase_add (univ : Finset V)
    (fun u => col (coefficient adj) r u * Q adj u j) (mem_univ j)
  rw [rj] at recover
  linarith

/-- A genuine private two-step path through j forces positive original
retained slack in every certificate of D-j. This need not be positive
induced slack: some or all can be regained path mass. -/
theorem private_path_forces_retained_slack (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j : V) (edge : adj i j) (loss : (lostSecond adj i j).Nonempty)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r) :
    ∃ u, u ≠ j ∧ 0 < col (coefficient adj) r u ∧ 0 < Q adj u j := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have charge := lost_count_le_nine_diagonal adj noLoop deleted minimal w hw bad i j edge
  have count : (0 : ℝ) < (lostSecond adj i j).card := by exact_mod_cast card_pos.mpr loss
  have qp : 0 < Q adj j j := by linarith
  have tp := (deleted_domination adj deleted w hw bad j r fair).1
  have identity := retained_slack_diagonal_identity adj unit j r (fair.2.1 j (by simp))
  have positive : 0 < ∑ u ∈ univ.erase j, col (coefficient adj) r u * Q adj u j := by
    rw [identity]
    exact mul_pos tp qp
  have witness : ∃ u ∈ univ.erase j, 0 < col (coefficient adj) r u * Q adj u j := by
    by_contra hn
    push Not at hn
    have nonpos := sum_nonpos (s := univ.erase j) hn
    linarith
  obtain ⟨u, hu, product⟩ := witness
  have uj : u ≠ j := (mem_erase.mp hu).1
  have cn := retained_column adj j r fair u uj
  refine ⟨u, uj, ?_, ?_⟩ <;> nlinarith [qn u j]

/-- For any actual certificate of D-j, positive entries in inverse
column j force the corresponding retained original slacks to vanish. -/
theorem positive_column_tight (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (zero : Q adj j j = 0)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r)
    (u : V) (uj : u ≠ j) (positive : 0 < Q adj u j) :
    col (coefficient adj) r u = 0 := by
  have rj : r j = 0 := fair.2.1 j (by simp)
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r j
  change r j = -∑ v, col (coefficient adj) r v * Q adj v j at recover
  have split := sum_erase_add (univ : Finset V)
    (fun v => col (coefficient adj) r v * Q adj v j) (mem_univ j)
  rw [zero, mul_zero, add_zero] at split
  have total : (∑ v ∈ univ.erase j, col (coefficient adj) r v * Q adj v j) = 0 := by
    rw [rj] at recover
    linarith
  have nonneg (v : V) (hv : v ∈ univ.erase j) :
      0 ≤ col (coefficient adj) r v * Q adj v j :=
    mul_nonneg (retained_column adj j r fair v (mem_erase.mp hv).1) (qn v j)
  have term := single_le_sum nonneg (show u ∈ univ.erase j by simp [uj])
  rw [total] at term
  have cn := retained_column adj j r fair u uj
  nlinarith

theorem outgoing_columns_tight (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (zero : Q adj j j = 0) (r : V → ℝ)
    (fair : FairOn adj (univ.erase j) r) (u : V) (edge : adj j u) :
    col (coefficient adj) r u = 0 ∧ localSlack adj r (univ.erase j) u = 0 := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have uj : u ≠ j := by intro h; exact noLoop j (by simpa only [h] using edge)
  have charge := arc_lower adj deleted minimal w hw bad j u edge
  have tight := positive_column_tight adj unit qn j zero r fair u uj (by linarith)
  refine ⟨tight, ?_⟩
  have identity := fair_deletion_identity adj r (univ.erase j) fair.2.1 u
  have nonneg := fair.2.2.2 u (by simp [uj])
  have gained := weight_nonneg r fair.1 (gainedIn adj (univ.erase j) u)
  rw [col_coefficient] at tight
  dsimp [localSlack]
  dsimp [localSlack] at identity
  linarith

/-- The support separation proved at the atom floor already suffices
to recover its certificate ray. It is not an independent extra
constraint on this same deletion. -/
theorem support_separation_fair_ray (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V)
    (separation : ∀ u, u ≠ j → ∃ v, Q adj j v = 0 ∧ 0 < Q adj u v)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r) :
    ∀ k, r k = (-col (coefficient adj) r j) * Q adj j k := by
  have tight (u : V) (uj : u ≠ j) : col (coefficient adj) r u = 0 := by
    obtain ⟨v, zero, positive⟩ := separation u uj
    have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r v
    change r v = -∑ a, col (coefficient adj) r a * Q adj a v at recover
    have split := sum_erase_add (univ : Finset V)
      (fun a => col (coefficient adj) r a * Q adj a v) (mem_univ j)
    rw [zero, mul_zero, add_zero] at split
    have nonneg (a : V) (ha : a ∈ univ.erase j) :
        0 ≤ col (coefficient adj) r a * Q adj a v :=
      mul_nonneg (retained_column adj j r fair a (mem_erase.mp ha).1) (qn a v)
    have term := single_le_sum nonneg (show u ∈ univ.erase j by simp [uj])
    have cn := retained_column adj j r fair u uj
    nlinarith [fair.1 v]
  intro k
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
  change r k = -∑ a, col (coefficient adj) r a * Q adj a k at recover
  have split := sum_erase_add (univ : Finset V)
    (fun a => col (coefficient adj) r a * Q adj a k) (mem_univ j)
  have total : (∑ a ∈ univ.erase j, col (coefficient adj) r a * Q adj a k) = 0 := by
    apply sum_eq_zero
    intro a ha
    rw [tight a (mem_erase.mp ha).1, zero_mul]
  rw [total, zero_add] at split
  rw [← split] at recover
  linarith

end CH.CompromiseZeroDiagonal

#print axioms CH.CompromiseZeroDiagonal.zero_diagonal_certificate
#print axioms CH.CompromiseZeroDiagonal.retained_slack_diagonal_identity
#print axioms CH.CompromiseZeroDiagonal.private_path_forces_retained_slack
#print axioms CH.CompromiseZeroDiagonal.positive_column_tight
#print axioms CH.CompromiseZeroDiagonal.outgoing_columns_tight
#print axioms CH.CompromiseZeroDiagonal.support_separation_fair_ray
