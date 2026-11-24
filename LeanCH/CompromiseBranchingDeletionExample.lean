module

public import LeanCH.CompromiseSingleTarget

set_option linter.style.header false

/-! A fixed six-vertex theta graph satisfies weighted K*, but every
actual certificate of deletion 0 has two positive retained slacks.
Thus even allowing the certificate to vary cannot make this deletion
have a single feedback target. No graph search is used. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseCertificateCone CH.CompromiseSingleTarget CH.CompromiseLostArc
open CH.CompromiseDeletionCone
open CH.CompromisePerturbation CH.CompromiseArcMinimal
public section

namespace CH.CompromiseBranchingDeletionExample

abbrev Vertex := Fin 6

@[expose] def edge (v u : Vertex) : Prop :=
  (v = 0 ∧ (u = 1 ∨ u = 2)) ∨ (v = 1 ∧ u = 3) ∨
  (v = 2 ∧ u = 4) ∨ ((v = 3 ∨ v = 4) ∧ u = 5) ∨ (v = 5 ∧ u = 0)

instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

@[expose] def secondTable : Vertex → Finset Vertex := ![{3, 4}, {5}, {5}, {0}, {0}, {1, 2}]

@[expose] def coefficients : Matrix Vertex Vertex ℝ :=
  !![0, -2, -2, 1, 1, 1;
     1, 0, 0, -2, 0, 1;
     1, 0, 0, 0, -2, 1;
     1, 1, 0, 0, 0, -2;
     1, 0, 1, 0, 0, -2;
     -2, 1, 1, 1, 1, 0]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem independent_heads : ∀ v a b, edge v a → edge v b → ¬ edge a b := by decide

theorem strongly_connected (v u : Vertex) : Relation.ReflTransGen edge v u := by
  have e01 : Relation.ReflTransGen edge 0 1 := .single (by decide)
  have e02 : Relation.ReflTransGen edge 0 2 := .single (by decide)
  have e13 : Relation.ReflTransGen edge 1 3 := .single (by decide)
  have e24 : Relation.ReflTransGen edge 2 4 := .single (by decide)
  have e35 : Relation.ReflTransGen edge 3 5 := .single (by decide)
  have e45 : Relation.ReflTransGen edge 4 5 := .single (by decide)
  have e50 : Relation.ReflTransGen edge 5 0 := .single (by decide)
  have toZero : ∀ a : Vertex, Relation.ReflTransGen edge a 0 := by
    intro a
    fin_cases a
    · exact .refl
    · exact e13.trans (e35.trans e50)
    · exact e24.trans (e45.trans e50)
    · exact e35.trans e50
    · exact e45.trans e50
    · exact e50
  have fromZero : ∀ a : Vertex, Relation.ReflTransGen edge 0 a := by
    intro a
    fin_cases a
    · exact .refl
    · exact e01
    · exact e02
    · exact e01.trans e13
    · exact e02.trans e24
    · exact e01.trans (e13.trans e35)
  exact (toZero v).trans (fromZero u)

theorem seconds : ∀ v, second edge v = secondTable v := by
  simp only [Finset.ext_iff, mem_second]
  decide

theorem coefficient_values (v u : Vertex) : coefficient edge v u = coefficients v u := by
  simp only [coefficient, CH.CompromisePacking.capacity, seconds]
  fin_cases v <;> fin_cases u <;> norm_num [secondTable, coefficients, edge]

theorem matrix_invertible : IsUnit (CH.CompromiseInverse.matrix edge) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y equal
  have rows (v : Vertex) : row (coefficient edge) x v = row (coefficient edge) y v :=
    congrFun equal v
  have r0 := rows 0
  have r1 := rows 1
  have r2 := rows 2
  have r3 := rows 3
  have r4 := rows 4
  have r5 := rows 5
  simp only [row, coefficient_values] at r0 r1 r2 r3 r4 r5
  norm_num [coefficients, Fin.sum_univ_succ] at r0 r1 r2 r3 r4 r5
  funext v
  fin_cases v
  · change x 0 = y 0
    linarith
  · change x 1 = y 1
    linarith
  · change x 2 = y 2
    linarith
  · change x 3 = y 3
    linarith
  · change x 4 = y 4
    linarith
  · change x 5 = y 5
    linarith

/-- This example does not satisfy the nonnegative-inverse condition
of a minimal counterexample. Its role is to refute a universal
single-target-certificate assertion for triangle-free graphs. -/
theorem negative_inverse_diagonal : Q edge 0 0 = -5 / 7 := by
  let q : Vertex → ℝ := ![-5 / 7, -11 / 14, -11 / 14, -4 / 7, -4 / 7, -6 / 7]
  have columns (k : Vertex) : col (coefficient edge) q k = if k = 0 then -1 else 0 := by
    simp only [col, coefficient_values]
    fin_cases k <;> norm_num [coefficients, q, Fin.sum_univ_succ]
  have recover := inverse_recovery (CH.CompromiseInverse.matrix edge) matrix_invertible q 0
  change q 0 = -∑ u, col (coefficient edge) q u * Q edge u 0 at recover
  simp only [columns, ite_mul, neg_one_mul, zero_mul, sum_ite_eq', mem_univ,
    ite_true, neg_neg] at recover
  rw [← recover]
  norm_num [q]

theorem private_ends : lostSecond edge 5 0 = {1, 2} := by
  simp only [lostSecond, Finset.ext_iff, mem_sdiff, mem_second, CH.ArcMinimal.eraseArc]
  decide

/-- The deletion cone is nonempty: its terminal vertex gives a
genuine induced fair probability. -/
theorem deleted_certificate : FairOn edge (univ.erase 0) (point 5) := by
  refine ⟨(point_mem 5).1, ?_, ⟨5, by decide, by norm_num [point]⟩, ?_⟩
  · intro v hv
    have equal : v = 0 := by simpa using hv
    simp only [point, equal]
    norm_num
  · intro u hu
    have zero : mass (point 5) (inN edge u ∩ univ.erase 0) = 0 := by
      apply sum_eq_zero
      intro v hv
      by_cases v5 : v = 5
      · subst v
        have eu := (mem_inN edge u 5).mp (mem_inter.mp hv).1
        have u0 : u = 0 := by simpa [edge] using eu
        exact ((mem_erase.mp hu).1 u0).elim
      · simp only [point, ite_eq_right v5]
    rw [zero, mul_zero]
    exact add_nonneg (weight_nonneg _ (point_mem 5).1 _) (weight_nonneg _ (point_mem 5).1 _)

theorem columns (r : Vertex → ℝ) :
    col (coefficient edge) r 0 = r 1 + r 2 + r 3 + r 4 - 2 * r 5 ∧
    col (coefficient edge) r 3 = r 0 - 2 * r 1 + r 5 ∧
    col (coefficient edge) r 4 = r 0 - 2 * r 2 + r 5 ∧
    col (coefficient edge) r 5 = r 0 + r 1 + r 2 - 2 * r 3 - 2 * r 4 := by
  simp only [col, coefficient_values]
  norm_num [coefficients, Fin.sum_univ_succ]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- These conclusions hold for every genuine induced certificate,
not merely for a chosen probability or a selected extreme point. -/
theorem every_certificate_branches (r : Vertex → ℝ)
    (fair : FairOn edge (univ.erase 0) r) :
    0 < r 5 ∧ col (coefficient edge) r 0 < 0 ∧
      0 < col (coefficient edge) r 1 ∧ 0 < col (coefficient edge) r 2 ∧
      -col (coefficient edge) r 0 ≤ 2 * col (coefficient edge) r 1 ∧
      -col (coefficient edge) r 0 ≤ 2 * col (coefficient edge) r 2 := by
  have r0 := fair.2.1 0 (by simp)
  obtain ⟨c0, c3, c4, c5⟩ := columns r
  have n3 := retained_column edge 0 r fair 3 (by decide)
  have n4 := retained_column edge 0 r fair 4 (by decide)
  have n5 := retained_column edge 0 r fair 5 (by decide)
  rw [c3, r0] at n3
  rw [c4, r0] at n4
  rw [c5, r0] at n5
  have positive : 0 < r 5 := by
    by_contra hn
    have z5 : r 5 = 0 := le_antisymm (le_of_not_gt hn) (fair.1 5)
    have z1 : r 1 = 0 := by linarith [fair.1 1]
    have z2 : r 2 = 0 := by linarith [fair.1 2]
    have z3 : r 3 = 0 := by linarith [fair.1 3, fair.1 4]
    have z4 : r 4 = 0 := by linarith [fair.1 3, fair.1 4]
    have zero (v : Vertex) : r v = 0 := by fin_cases v <;> assumption
    obtain ⟨v, _, hv⟩ := fair.2.2.1
    rw [zero] at hv
    linarith
  have first := private_endpoint_slack_bound edge 0 r fair 5 (by decide) 1
    (by rw [private_ends]; decide)
  have second := private_endpoint_slack_bound edge 0 r fair 5 (by decide) 2
    (by rw [private_ends]; decide)
  refine ⟨positive, ?_, positive.trans_le first, positive.trans_le second, ?_, ?_⟩
  · rw [c0]
    linarith
  · rw [c0]
    linarith [fair.1 1, fair.1 2, fair.1 3, fair.1 4]
  · rw [c0]
    linarith [fair.1 1, fair.1 2, fair.1 3, fair.1 4]

theorem no_single_target (r : Vertex → ℝ) (fair : FairOn edge (univ.erase 0) r)
    (u : Vertex) : ∃ k, k ≠ 0 ∧ k ≠ u ∧ 0 < col (coefficient edge) r k := by
  obtain ⟨_, _, positive1, positive2, _, _⟩ := every_certificate_branches r fair
  by_cases u1 : u = 1
  · exact ⟨2, by decide, by rw [u1]; decide, positive2⟩
  · exact ⟨1, by decide, Ne.symm u1, positive1⟩

@[expose] noncomputable def branchRates : Vertex → ℝ := ![0, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 0]

theorem branch_rates_admissible : Admissible edge 0 branchRates := by
  apply (admissible_iff edge matrix_invertible 0 branchRates (by norm_num [branchRates])).mpr
  refine ⟨fun v => point 5 v / 2,
    fair_div_positive edge 0 (point 5) deleted_certificate 2 (by norm_num), ?_⟩
  intro k
  simp only [col, point, ite_div, zero_div, ite_mul, zero_mul, sum_ite_eq',
    mem_univ, ite_true, coefficient_values]
  fin_cases k <;> norm_num [coefficients, branchRates]

theorem every_admissible_branches (b : Vertex → ℝ) (bj : b 0 = 0)
    (feasible : Admissible edge 0 b) : 0 < b 1 ∧ 0 < b 2 := by
  obtain ⟨fair, columns⟩ := admissible_certificate edge matrix_invertible 0 b bj feasible
  obtain ⟨_, _, h1, h2, _, _⟩ := every_certificate_branches _ fair
  simpa only [columns, ite_eq_right (by decide : (1 : Vertex) ≠ 0),
    ite_eq_right (by decide : (2 : Vertex) ≠ 0), zero_add] using And.intro h1 h2

@[expose] def certificate : Vertex → ℝ := ![4, 4, 4, 3, 3, 6]

theorem certificate_fair : Fair edge certificate := by
  have nonnegative : ∀ v, 0 ≤ certificate v := by intro v; fin_cases v <;> norm_num [certificate]
  refine ⟨nonnegative, ⟨0, by norm_num [certificate]⟩, ?_⟩
  intro u
  have column : 0 ≤ col (coefficient edge) certificate u := by
    simp only [col, coefficient_values]
    fin_cases u <;> norm_num [coefficients, certificate, Fin.sum_univ_succ]
  rw [col_coefficient] at column
  dsimp [slack] at column
  linarith

theorem compromise_all_weights (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 ≤ surplus edge w v := by
  obtain ⟨v, _, hv⟩ := compromise_of_fair edge certificate w certificate_fair hw
  exact ⟨v, by dsimp [surplus]; linarith⟩

end CH.CompromiseBranchingDeletionExample

#print axioms CH.CompromiseBranchingDeletionExample.oriented_triangle_free
#print axioms CH.CompromiseBranchingDeletionExample.strongly_connected
#print axioms CH.CompromiseBranchingDeletionExample.matrix_invertible
#print axioms CH.CompromiseBranchingDeletionExample.negative_inverse_diagonal
#print axioms CH.CompromiseBranchingDeletionExample.deleted_certificate
#print axioms CH.CompromiseBranchingDeletionExample.every_certificate_branches
#print axioms CH.CompromiseBranchingDeletionExample.no_single_target
#print axioms CH.CompromiseBranchingDeletionExample.branch_rates_admissible
#print axioms CH.CompromiseBranchingDeletionExample.every_admissible_branches
#print axioms CH.CompromiseBranchingDeletionExample.certificate_fair
#print axioms CH.CompromiseBranchingDeletionExample.compromise_all_weights
