module

public import LeanCH.CompromiseSharedPaths
public import LeanCH.CompromiseApex

set_option linter.style.header false

/-! One fixed five-vertex example. It defeats a proposed local-column
closure criterion, not K*: the graph satisfies K* for every weighting.
The adjacency and explicit inverse are hand specified; no graph search
or enumeration is used to discover the example. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation
public section

namespace CH.CompromiseLocalColumnExample

abbrev Vertex := Fin 5

@[expose] def edge (v u : Vertex) : Prop :=
  (v = 0 ∧ (u = 1 ∨ u = 2)) ∨ (v = 1 ∧ u = 2) ∨
  (v = 2 ∧ u = 3) ∨ (v = 3 ∧ u = 4) ∨ (v = 4 ∧ (u = 0 ∨ u = 1))

instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

@[expose] noncomputable def q (v : Vertex) : ℝ := if v = 0 then 0 else 1 / 2

@[expose] def coefficients : Matrix Vertex Vertex ℝ :=
  !![0, -2, -2, 1, 1;
     1, 0, -2, 1, 1;
     1, 1, 0, -2, 1;
     1, 1, 1, 0, -2;
     -2, -2, 1, 1, 0]

@[expose] noncomputable def inverseWitness : Matrix Vertex Vertex ℝ :=
  !![0, 1, 1, 1, 1;
     -1/2, 0, -1/2, -1/2, -1/2;
     -1/2, 1, 9/10, 7/10, 13/10;
     -1/2, 1, 1/10, 3/10, 7/10;
     -1/2, 1, 7/10, 1/10, 9/10]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem matrix_eq : CH.CompromiseInverse.matrix edge = coefficients := by
  ext v u
  fin_cases v <;> fin_cases u <;>
    norm_num [CH.CompromiseInverse.matrix, coefficient, CH.CompromisePacking.capacity,
      coefficients, edge, Fin.exists_fin_succ]

theorem right_inverse : CH.CompromiseInverse.matrix edge * inverseWitness = 1 := by
  rw [matrix_eq]
  ext v u
  fin_cases v <;> fin_cases u <;>
    norm_num [coefficients, inverseWitness, Matrix.mul_apply, Fin.sum_univ_succ]

theorem matrix_unit : IsUnit (CH.CompromiseInverse.matrix edge) :=
  (CH.CompromiseInverse.matrix edge).isUnit_iff_isUnit_det.mpr
    (Matrix.isUnit_det_of_right_inverse right_inverse)

theorem inverse_eq : (CH.CompromiseInverse.matrix edge)⁻¹ = inverseWitness := by
  let M : Matrix Vertex Vertex ℝ := CH.CompromiseInverse.matrix edge
  have hleft : M⁻¹ * M = 1 := M.nonsing_inv_mul (M.isUnit_iff_isUnit_det.mp matrix_unit)
  change M⁻¹ = inverseWitness
  calc
    _ = M⁻¹ * 1 := by simp
    _ = M⁻¹ * (M * inverseWitness) := by rw [right_inverse]
    _ = inverseWitness := by rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]

theorem column_zero : ∀ v : Vertex,
    negativeInverse (CH.CompromiseInverse.matrix edge) v 0 = q v := by
  intro v
  rw [negativeInverse, inverse_eq]
  fin_cases v <;> norm_num [inverseWitness, q]

theorem q_nonnegative : ∀ v : Vertex, 0 ≤ q v := by
  intro v
  unfold q
  split_ifs <;> norm_num

theorem one_bad_row (v : Vertex) : surplus edge q v = if v = 0 then -1 else 0 := by
  have h := inverse_column (CH.CompromiseInverse.matrix edge) matrix_unit 0 v
  simp only [column_zero] at h
  change row (coefficient edge) q v = _ at h
  rwa [row_coefficient] at h

theorem positive_inverse_entry : (CH.CompromiseInverse.matrix edge)⁻¹ 0 1 = 1 := by
  rw [inverse_eq]
  norm_num [inverseWitness]

@[expose] def retain (T : Finset Vertex) (v u : Vertex) : Prop :=
  edge v u ∧ (v ≠ 0 ∨ u ∈ T)

instance (T : Finset Vertex) : DecidableRel (retain T) := fun v u => by
  unfold retain
  infer_instance

theorem retain_empty : surplus (retain ∅) q 0 = 1 / 2 := by
  rw [← row_coefficient]
  norm_num [row, coefficient, CH.CompromisePacking.capacity, retain, edge, q,
    Fin.sum_univ_succ, Fin.exists_fin_succ]

theorem retain_one : surplus (retain {1}) q 0 = 0 := by
  rw [← row_coefficient]
  norm_num [row, coefficient, CH.CompromisePacking.capacity, retain, edge, q,
    Fin.sum_univ_succ, Fin.exists_fin_succ]

theorem retain_two : surplus (retain {2}) q 0 = 0 := by
  rw [← row_coefficient]
  norm_num [row, coefficient, CH.CompromisePacking.capacity, retain, edge, q,
    Fin.sum_univ_succ, Fin.exists_fin_succ]

/-- Every proper retained outgoing set repairs the unique bad row. -/
theorem all_proper_tail_deletions (T : Finset Vertex) (subset : T ⊆ {1, 2})
    (proper : T ≠ {1, 2}) : 0 ≤ surplus (retain T) q 0 := by
  have he : ({1, 2} : Finset Vertex).powerset = {∅, {1}, {2}, {1, 2}} := by decide
  have ht := mem_powerset.mpr subset
  rw [he] at ht
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hh
  · rw [retain_empty]
    norm_num
  · rw [retain_one]
  · rw [retain_two]
  · exact (proper hh).elim

theorem all_apex : ∀ v : Vertex, ∃ a, CH.CompromiseApex.IsApex edge v a := by
  unfold CH.CompromiseApex.IsApex
  decide

/-- The example is known-good for every nonnegative weighting. -/
theorem compromise_all_weights (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 ≤ surplus edge w v := by
  obtain ⟨v, hv⟩ := CH.CompromiseApex.compromise_apex edge w hw oriented_triangle_free.2.1
    (fun v _ => all_apex v)
  refine ⟨v, ?_⟩
  dsimp [surplus]
  linarith

end CH.CompromiseLocalColumnExample

#print axioms CH.CompromiseLocalColumnExample.matrix_unit
#print axioms CH.CompromiseLocalColumnExample.column_zero
#print axioms CH.CompromiseLocalColumnExample.one_bad_row
#print axioms CH.CompromiseLocalColumnExample.positive_inverse_entry
#print axioms CH.CompromiseLocalColumnExample.all_proper_tail_deletions
#print axioms CH.CompromiseLocalColumnExample.compromise_all_weights
