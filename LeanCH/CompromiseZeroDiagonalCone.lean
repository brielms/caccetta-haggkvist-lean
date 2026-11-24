module

public import LeanCH.CompromiseFeedbackSupport
public import LeanCH.CompromiseEndpointSupport
public import LeanCH.CompromiseTailCut

set_option linter.style.header false

/-! At a zero inverse diagonal, actual deletion certificates are
exactly nonnegative inverse-row residuals with omitted deficit one.
The positive-feedback support condition is both necessary and sufficient.
This characterizes one deletion; it does not supply a balanced mixture. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseCertificateCone CH.CompromiseDeletionMixture CH.CompromiseZeroDiagonal
open CH.CompromiseFeedbackSupport CH.CompromiseEndpointSupport CH.CompromiseDiagonalLoss
open CH.CompromiseTailCut
public section

namespace CH.CompromiseZeroDiagonalCone

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] noncomputable def residual (j : V) (b : V → ℝ) (k : V) : ℝ :=
  Q adj j k - ∑ u, b u * Q adj u k

theorem residual_columns (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (b : V → ℝ) (k : V) :
    col (coefficient adj) (residual adj j b) k = (if k = j then -1 else 0) + b k := by
  have inv (u : V) : col (coefficient adj) (fun v => Q adj u v) k =
      if k = u then -1 else 0 := inverse_row (CH.CompromiseInverse.matrix adj) unit u k
  have combined : col (coefficient adj) (mixture (fun u v => Q adj u v) b) k = -b k := by
    rw [mixture_column]
    simp only [inv]
    simp [mul_ite]
  calc
    _ = col (coefficient adj) (fun v => Q adj j v) k -
        col (coefficient adj) (mixture (fun u v => Q adj u v) b) k := by
      simp only [col, residual, mixture, sub_mul, sum_sub_distrib]
    _ = _ := by rw [inv, combined]; ring

/-- All inequalities concern the same chosen coefficient vector b.
The residual is an actual certificate of the induced deletion. -/
theorem residual_certificate (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (zero : Q adj j j = 0)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅)
    (b : V → ℝ) (bn : ∀ u, 0 ≤ b u) (bj : b j = 0)
    (packing : ∀ k, (∑ u, b u * Q adj u k) ≤ Q adj j k) :
    FairOn adj (univ.erase j) (residual adj j b) ∧
      ∀ k, col (coefficient adj) (residual adj j b) k =
        (if k = j then -1 else 0) + b k := by
  have rn (k : V) : 0 ≤ residual adj j b k := sub_nonneg.mpr (packing k)
  have rj : residual adj j b j = 0 := by
    apply le_antisymm _ (rn j)
    dsimp [residual]
    rw [zero, zero_sub]
    exact neg_nonpos.mpr (sum_nonneg (fun u _ => mul_nonneg (bn u) (qn u j)))
  have cj : col (coefficient adj) (residual adj j b) j = -1 := by
    rw [residual_columns adj unit, ite_eq_left (by rfl), bj, add_zero]
  have positive : ∃ k, 0 < residual adj j b k := by
    by_contra hn
    push Not at hn
    have rz (k : V) : residual adj j b k = 0 := le_antisymm (hn k) (rn k)
    have cz : col (coefficient adj) (residual adj j b) j = 0 := by simp only [col, rz,
      zero_mul, sum_const_zero]
    linarith
  have cols (k : V) (kj : k ≠ j) : 0 ≤ col (coefficient adj) (residual adj j b) k := by
    rw [residual_columns adj unit, ite_eq_right kj, zero_add]
    exact bn k
  exact ⟨fair_on_of_columns_no_loss adj j _ rn positive rj cols noLoss,
    residual_columns adj unit j b⟩

/-- Exact feasible feedback cone at a loss-free zero diagonal, with
omitted deficit normalized to one. There is no extra certificate choice
hidden on the left side. -/
theorem cone_iff (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (zero : Q adj j j = 0)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅)
    (b : V → ℝ) (bj : b j = 0) :
    ((∀ u, 0 ≤ b u) ∧ ∀ k, (∑ u, b u * Q adj u k) ≤ Q adj j k) ↔
      ∃ r : V → ℝ, FairOn adj (univ.erase j) r ∧
        ∀ k, col (coefficient adj) r k = (if k = j then -1 else 0) + b k := by
  constructor
  · rintro ⟨bn, packing⟩
    exact ⟨residual adj j b,
      residual_certificate adj unit qn j zero noLoss b bn bj packing⟩
  · rintro ⟨r, fair, columns⟩
    refine ⟨?_, ?_⟩
    · intro u
      by_cases uj : u = j
      · simpa only [uj, bj] using (le_refl (0 : ℝ))
      · have h := retained_column adj j r fair u uj
        simpa only [columns, ite_eq_right uj, zero_add] using h
    · intro k
      have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
      change r k = -∑ u, col (coefficient adj) r u * Q adj u k at recover
      have identity : (∑ u, col (coefficient adj) r u * Q adj u k) =
          -Q adj j k + ∑ u, b u * Q adj u k := by
        simp only [columns, add_mul, sum_add_distrib]
        simp [ite_mul]
      rw [identity] at recover
      linarith [fair.1 k]

theorem minimal_cone_iff (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (zero : Q adj j j = 0) (b : V → ℝ) (bj : b j = 0) :
    ((∀ u, 0 ≤ b u) ∧ ∀ k, (∑ u, b u * Q adj u k) ≤ Q adj j k) ↔
      ∃ r : V → ℝ, FairOn adj (univ.erase j) r ∧
        ∀ k, col (coefficient adj) r k = (if k = j then -1 else 0) + b k := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  exact cone_iff adj unit (negativeInverse_nonneg _ sign) j zero
    (zero_diagonal_vertex_losses adj noLoop deleted minimal w hw bad j zero) b bj

/-- Every normalized actual certificate obeys each inverse-entry
capacity, including when its other retained slacks are also positive. -/
theorem normalized_entry_bound (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (r : V → ℝ)
    (fair : FairOn adj (univ.erase j) r) (normalized : col (coefficient adj) r j = -1)
    (u : V) (uj : u ≠ j) (k : V) :
    col (coefficient adj) r u * Q adj u k ≤ Q adj j k := by
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
  change r k = -∑ a, col (coefficient adj) r a * Q adj a k at recover
  have split := sum_erase_add (univ : Finset V)
    (fun a => col (coefficient adj) r a * Q adj a k) (mem_univ j)
  rw [normalized, neg_one_mul] at split
  have term := single_le_sum (s := univ.erase j)
    (fun a ha => mul_nonneg (retained_column adj j r fair a (mem_erase.mp ha).1) (qn a k))
    (show u ∈ univ.erase j by simp [uj])
  linarith [fair.1 k]

/-- Every permitted single-target rate is attained, with all other
retained slacks exactly zero. No other actual certificate can exceed
the same coordinatewise inverse bounds. -/
theorem single_target_capacity_iff (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (zero : Q adj j j = 0)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅) (u : V) (uj : u ≠ j)
    (e : ℝ) (en : 0 ≤ e) :
    (∀ k, e * Q adj u k ≤ Q adj j k) ↔
      ∃ r : V → ℝ, FairOn adj (univ.erase j) r ∧
        col (coefficient adj) r j = -1 ∧ col (coefficient adj) r u = e ∧
        ∀ k, k ≠ j → k ≠ u → col (coefficient adj) r k = 0 := by
  constructor
  · intro bound
    let b (k : V) : ℝ := if k = u then e else 0
    have bn (k : V) : 0 ≤ b k := by dsimp [b]; split_ifs <;> linarith
    have bj : b j = 0 := by simp only [b, ite_eq_right (Ne.symm uj)]
    have packing (k : V) : (∑ a, b a * Q adj a k) ≤ Q adj j k := by
      simpa only [b, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] using bound k
    obtain ⟨fair, columns⟩ := residual_certificate adj unit qn j zero noLoss b bn bj packing
    refine ⟨residual adj j b, fair, ?_, ?_, ?_⟩
    · rw [columns, ite_eq_left (by rfl), bj, add_zero]
    · simp only [columns, ite_eq_right uj, zero_add, b, ite_true]
    · intro k kj ku
      simp only [columns, ite_eq_right kj, zero_add, b, ite_eq_right ku]
  · rintro ⟨r, fair, normalized, target, _⟩ k
    have bound := normalized_entry_bound adj unit qn j r fair normalized u uj k
    rwa [target] at bound

/-- A positive slack at u is attainable by an actual certificate of
D-j exactly when inverse row u fits in the support of inverse row j.
This converse is special to the loss-free zero-diagonal case. -/
theorem positive_slack_iff (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (zero : Q adj j j = 0)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅) (u : V) (uj : u ≠ j) :
    rowSupport (Q adj) u ⊆ rowSupport (Q adj) j ↔
      ∃ r : V → ℝ, FairOn adj (univ.erase j) r ∧
        col (coefficient adj) r j = -1 ∧ 0 < col (coefficient adj) r u := by
  constructor
  · intro inclusion
    have support (k : V) (positive : 0 < Q adj u k) : 0 < Q adj j k := by
      exact (mem_rowSupport _ j k).mp (inclusion ((mem_rowSupport _ u k).mpr positive))
    obtain ⟨e, ep, bound⟩ := positive_scale_below (fun k => Q adj j k)
      (fun k => Q adj u k) (qn j) (qn u) support
    obtain ⟨r, fair, normalized, target, _⟩ :=
      (single_target_capacity_iff adj unit qn j zero noLoss u uj e ep.le).mp bound
    exact ⟨r, fair, normalized, by rwa [target]⟩
  · rintro ⟨r, fair, _, positive⟩
    exact positive_slack_support adj unit qn j r fair u uj positive

/-- Vertices with the same inverse-row support and zero diagonals
have an entirely zero principal inverse block. -/
theorem common_support_zero_block (qn : ∀ v u, 0 ≤ Q adj v u)
    (C : Finset V)
    (same : ∀ a ∈ C, ∀ b ∈ C, rowSupport (Q adj) a = rowSupport (Q adj) b)
    (zero : ∀ a ∈ C, Q adj a a = 0) :
    ∀ a ∈ C, ∀ b ∈ C, Q adj a b = 0 := by
  intro a ha b hb
  apply le_antisymm _ (qn a b)
  by_contra hn
  have member : b ∈ rowSupport (Q adj) a := (mem_rowSupport _ a b).mpr (lt_of_not_ge hn)
  rw [same a ha b hb] at member
  have positive := (mem_rowSupport _ b b).mp member
  rw [zero b hb] at positive
  linarith

/-- Cutting heads contained in one zero-diagonal support class cannot
lose an old second endpoint, even collectively. Whole-cut goodness is
supplied explicitly by weighted proper-subgraph minimality. -/
theorem common_support_cut_loss_free (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedSubgraphMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (proper : B ≠ outN adj i)
    (same : ∀ a ∈ removedHeads adj i B, ∀ b ∈ removedHeads adj i B,
      rowSupport (Q adj) a = rowSupport (Q adj) b)
    (zero : ∀ a ∈ removedHeads adj i B, Q adj a a = 0) :
    lostEndpoints adj i B = ∅ := by
  obtain ⟨_, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  exact zero_block_losses_empty adj noDigon deleted minimal w hw bad i B subset proper
    (common_support_zero_block adj qn (removedHeads adj i B) same zero)

end CH.CompromiseZeroDiagonalCone

#print axioms CH.CompromiseZeroDiagonalCone.residual_columns
#print axioms CH.CompromiseZeroDiagonalCone.residual_certificate
#print axioms CH.CompromiseZeroDiagonalCone.cone_iff
#print axioms CH.CompromiseZeroDiagonalCone.minimal_cone_iff
#print axioms CH.CompromiseZeroDiagonalCone.normalized_entry_bound
#print axioms CH.CompromiseZeroDiagonalCone.single_target_capacity_iff
#print axioms CH.CompromiseZeroDiagonalCone.positive_slack_iff
#print axioms CH.CompromiseZeroDiagonalCone.common_support_zero_block
#print axioms CH.CompromiseZeroDiagonalCone.common_support_cut_loss_free
