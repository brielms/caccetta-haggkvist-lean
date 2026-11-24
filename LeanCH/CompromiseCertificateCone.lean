module

public import LeanCH.CompromiseEndpointDeletion

set_option linter.style.header false

/-! Every genuine deleted-vertex certificate is bounded by a positive
multiple of the corresponding inverse row. Retained slack accounts
exactly for the nonnegative difference. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseCertificateCharge
public section

namespace CH.CompromiseCertificateCone

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem inverse_recovery (M : Matrix V V ℝ) (unit : IsUnit M) (r : V → ℝ) (k : V) :
    r k = -∑ u, col M r u * negativeInverse M u k := by
  have he : (∑ u, col M r u * negativeInverse M u k) = -r k := by
    calc
      _ = payoff M (fun u => negativeInverse M u k) r := by
        erw [payoff_transpose]
        apply sum_congr rfl
        intro u _
        ring
      _ = -r k := by simp [payoff, inverse_column M unit, mul_ite]
  linarith

theorem inverse_domination (M : Matrix V V ℝ) (unit : IsUnit M)
    (qn : ∀ v u, 0 ≤ negativeInverse M v u) (j : V) (r : V → ℝ)
    (cols : ∀ u, u ≠ j → 0 ≤ col M r u) (k : V) :
    r k ≤ (-col M r j) * negativeInverse M j k := by
  have recover := inverse_recovery M unit r k
  have hs := sum_erase_add (univ : Finset V)
    (fun u => col M r u * negativeInverse M u k) (mem_univ j)
  have nonneg : 0 ≤ ∑ u ∈ univ.erase j, col M r u * negativeInverse M u k :=
    sum_nonneg (fun u hu => mul_nonneg (cols u (mem_erase.mp hu).1) (qn u k))
  linarith

variable (adj : V → V → Prop) [DecidableRel adj]

theorem retained_column (j : V) (r : V → ℝ) (hr : FairOn adj (univ.erase j) r)
    (u : V) (hu : u ≠ j) : 0 ≤ col (coefficient adj) r u := by
  have h := retained_row adj (univ.erase j) r hr u (by simp [hu])
  rw [col_coefficient]
  dsimp [slack]
  linarith

theorem deleted_domination (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (r : V → ℝ) (hr : FairOn adj (univ.erase j) r) :
    0 < -col (coefficient adj) r j ∧
      ∀ k, r k ≤ (-col (coefficient adj) r j) * Q adj j k := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have neg := (singleton_fair_budget adj w hw bad j r hr).2.1
  rw [← col_coefficient] at neg
  refine ⟨neg_pos.mpr neg, ?_⟩
  intro k
  exact inverse_domination (CH.CompromiseInverse.matrix adj) unit
    (negativeInverse_nonneg _ sign) j r (retained_column adj j r hr) k

/-- The CH upper matrix gives a homogeneous bound from just the one
column inequality; other columns need not be fair. -/
theorem closed_in_at (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (r : V → ℝ) (rn : ∀ v, 0 ≤ r v) (u : V)
    (fair : 0 ≤ col (coefficient adj) r u) :
    r u + 3 * inWeight adj r u ≤ ∑ v, r v := by
  have h : col (coefficient adj) r u ≤ col (CH.LinearProgram.matrix adj) r u :=
    sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left
      (coefficient_le_ch adj noDigon noTri v u) (rn v))
  rw [CH.LinearProgram.col_matrix] at h
  linarith

theorem tail_at (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (r : V → ℝ) (rn : ∀ v, 0 ≤ r v) (i u : V) (edge : adj i u)
    (fair : 0 ≤ col (coefficient adj) r u) :
    3 * r i + r u ≤ ∑ v, r v := by
  have h := closed_in_at adj noDigon noTri r rn u fair
  have hi : r i ≤ inWeight adj r u :=
    single_le_sum (fun v _ => rn v) ((mem_inN adj u i).mpr edge)
  linarith

theorem residual_column (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (r : V → ℝ) :
    col (coefficient adj)
      (fun v => (-col (coefficient adj) r j) * Q adj j v - r v) j = 0 := by
  have inv := inverse_row (CH.CompromiseInverse.matrix adj) unit j j
  change col (coefficient adj) (fun v => Q adj j v) j = _ at inv
  simp only [ite_true] at inv
  have he : col (coefficient adj)
      (fun v => (-col (coefficient adj) r j) * Q adj j v - r v) j =
      (-col (coefficient adj) r j) * col (coefficient adj) (fun v => Q adj j v) j -
        col (coefficient adj) r j := by
    simp only [col, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
  rw [he, inv]
  ring

omit [DecidableEq V] in
theorem equality_of_domination_total (p r : V → ℝ) (bound : ∀ v, r v ≤ p v)
    (total : ∑ v, r v = ∑ v, p v) : ∀ v, r v = p v := by
  have hn (v : V) : 0 ≤ p v - r v := sub_nonneg.mpr (bound v)
  have hs : ∑ v, (p v - r v) = 0 := by rw [sum_sub_distrib, total, sub_self]
  intro v
  have hh : p v - r v ≤ ∑ u, (p u - r u) := single_le_sum (fun u _ => hn u) (mem_univ v)
  linarith [bound v]

end CH.CompromiseCertificateCone

#print axioms CH.CompromiseCertificateCone.inverse_recovery
#print axioms CH.CompromiseCertificateCone.deleted_domination
#print axioms CH.CompromiseCertificateCone.closed_in_at
#print axioms CH.CompromiseCertificateCone.residual_column
