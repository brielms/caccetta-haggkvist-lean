module

public import LeanCH.CompromiseLostArc

set_option linter.style.header false

/-! A deleted-graph certificate constrains every inverse column.
The nonnegative loss matrix retains all decreases outside the changed
tail row as well. This is a necessary condition, not a closure theorem. -/

open Finset CH.CompromiseGame CH.CompromiseInverse CH.CompromisePerturbation
open CH.CompromiseRowRepair CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseArcMinimal
open CH.CompromiseLostArc
public section

namespace CH.CompromiseColumnCoupling

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def loss (M N : V → V → ℝ) (i : V) (h : V → ℝ) (v u : V) : ℝ :=
  shiftRow M i h v u - N v u

omit [Fintype V] in
theorem loss_nonnegative (M N : V → V → ℝ) (i : V) (h : V → ℝ)
    (bound : ∀ v u, N v u ≤ shiftRow M i h v u) :
    ∀ v u, 0 ≤ loss M N i h v u := fun v u => sub_nonneg.mpr (bound v u)

theorem payoff_shift (M : V → V → ℝ) (i : V) (h x p : V → ℝ) :
    payoff (shiftRow M i h) x p = payoff M x p + p i * pairing h x := by
  simp [payoff, row_shift, mul_add, sum_add_distrib, mul_ite]

theorem payoff_loss (M N : V → V → ℝ) (i : V) (h x p : V → ℝ) :
    payoff (loss M N i h) x p =
      payoff (shiftRow M i h) x p - payoff N x p := by
  simp [payoff, row, loss, sub_mul, sum_sub_distrib, mul_sub]

omit [DecidableEq V] in
theorem payoff_nonnegative (L : V → V → ℝ) (ln : ∀ v u, 0 ≤ L v u)
    (x p : V → ℝ) (xn : ∀ v, 0 ≤ x v) (pn : ∀ v, 0 ≤ p v) :
    0 ≤ payoff L x p := by
  exact sum_nonneg (fun v _ => mul_nonneg (pn v)
    (sum_nonneg (fun u _ => mul_nonneg (ln v u) (xn u))))

/-- The certificate and every original inverse column obey one joint
inequality, including the nonnegative loss at all other rows. -/
theorem transport (M : Matrix V V ℝ) (unit : IsUnit M)
    (qn : ∀ v u, 0 ≤ negativeInverse M v u)
    (N : V → V → ℝ) (i : V) (h p : V → ℝ)
    (cols : ∀ u, 0 ≤ col N p u) (k : V) :
    p k + payoff (loss M N i h) (fun u => negativeInverse M u k) p ≤
      p i * pairing h (fun u => negativeInverse M u k) := by
  have hn : 0 ≤ payoff N (fun u => negativeInverse M u k) p := by
    rw [payoff_transpose]
    exact sum_nonneg (fun u _ => mul_nonneg (qn u k) (cols u))
  have hm : payoff M (fun u => negativeInverse M u k) p = -p k := by
    simp [payoff, inverse_column M unit, mul_ite]
  erw [payoff_loss, payoff_shift, hm]
  linarith

theorem certificate_tail_positive (M : Matrix V V ℝ) (unit : IsUnit M)
    (qn : ∀ v u, 0 ≤ negativeInverse M v u)
    (N : V → V → ℝ) (i : V) (h p : V → ℝ) (hp : p ∈ simplex)
    (bound : ∀ v u, N v u ≤ shiftRow M i h v u)
    (cols : ∀ u, 0 ≤ col N p u) : 0 < p i := by
  by_contra hn
  have hz : p i = 0 := le_antisymm (le_of_not_gt hn) (hp.1 i)
  obtain ⟨k, hk⟩ := simplex_has_positive hp
  have ht := transport M unit qn N i h p cols k
  have hl := payoff_nonnegative _ (loss_nonnegative M N i h bound)
    (fun u => negativeInverse M u k) p (fun u => qn u k) hp.1
  rw [hz, zero_mul] at ht
  linarith

variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def arcLoss (i j : V) : V → V → ℝ :=
  loss (coefficient adj) (coefficient (CH.ArcMinimal.eraseArc adj i j))
    i (changeRow adj i j)

theorem arc_loss_nonnegative (noLoop : ∀ v, ¬ adj v v) (i j : V) (edge : adj i j) :
    ∀ v u, 0 ≤ arcLoss adj i j v u := by
  have hne : i ≠ j := by intro hh; subst j; exact noLoop i edge
  exact loss_nonnegative _ _ i _ (coefficient_bound adj i j hne edge)

/-- One probability certificate simultaneously constrains all columns;
its mass at the deleted tail is strictly positive. -/
theorem deleted_certificate_coupling (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i j : V) (edge : adj i j) :
    ∃ p ∈ simplex,
      (∀ u, 0 ≤ col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p u) ∧
      0 < p i ∧ ∀ k,
      p k + payoff (arcLoss adj i j) (fun u => Q adj u k) p ≤
        p i * ((2 + newHead adj i j) * Q adj j k -
          mass (fun u => Q adj u k) (lostSecond adj i j)) := by
  let : Nonempty V := ⟨i⟩
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w0 hw0 bad0
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have hne : i ≠ j := by intro hh; subst j; exact noLoop i edge
  have nobad : ¬ ∃ y ∈ simplex, ∀ v,
      row (coefficient (CH.ArcMinimal.eraseArc adj i j)) y v < 0 := by
    rintro ⟨y, hy, hb⟩
    obtain ⟨v, hv⟩ := minimal i j edge y hy.1
    have hh := hb v
    rw [row_coefficient] at hh
    linarith
  obtain ⟨p, hp, cols⟩ := (fair_iff_no_bad _).mpr nobad
  have pp := certificate_tail_positive (CH.CompromiseInverse.matrix adj) unit qn
    (coefficient (CH.ArcMinimal.eraseArc adj i j)) i (changeRow adj i j) p hp
    (coefficient_bound adj i j hne edge) cols
  refine ⟨p, hp, cols, pp, ?_⟩
  intro k
  have ht := transport (CH.CompromiseInverse.matrix adj) unit qn
    (coefficient (CH.ArcMinimal.eraseArc adj i j)) i (changeRow adj i j) p cols k
  change p k + payoff (arcLoss adj i j) (fun u => Q adj u k) p ≤
    p i * pairing (changeRow adj i j) (fun u => Q adj u k) at ht
  rwa [change_pairing] at ht

/-- The old diagonal charge extends to nonnegative cross-column charges.
The stronger joint certificate inequality above retains their coupling. -/
theorem all_column_charge (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i j : V) (edge : adj i j) (k : V) :
    (if k = i then (1 : ℝ) else 0) +
        mass (fun u => Q adj u k) (lostSecond adj i j) ≤
      (2 + newHead adj i j) * Q adj j k := by
  obtain ⟨p, hp, _, pp, ht⟩ :=
    deleted_certificate_coupling adj noLoop deleted minimal w0 hw0 bad0 i j edge
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w0 hw0 bad0).2
  have hl := payoff_nonnegative _ (arc_loss_nonnegative adj noLoop i j edge)
    (fun u => Q adj u k) p (fun u => qn u k) hp.1
  have hc := ht k
  by_cases hk : k = i
  · subst k
    simp only [ite_true]
    nlinarith
  · simp only [ite_eq_right hk]
    have pn := hp.1 k
    nlinarith

end CH.CompromiseColumnCoupling

#print axioms CH.CompromiseColumnCoupling.transport
#print axioms CH.CompromiseColumnCoupling.deleted_certificate_coupling
#print axioms CH.CompromiseColumnCoupling.all_column_charge
