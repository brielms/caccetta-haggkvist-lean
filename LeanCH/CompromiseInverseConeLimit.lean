module

public import LeanCH.CompromiseInverseRatios

set_option linter.style.header false

/-! A fixed matrix obstruction to deducing single-target feedback from
inverse nonnegativity and one nonempty principal deletion cone alone.
Every diagonal is zero and the negative inverse is strictly positive.
Deletion 0 forces three positive targets. Deletion 1 has no certificate,
so this is not a model of DeletedFair or a graph counterexample. -/

open Finset CH.CompromiseGame CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseCritical
open scoped Matrix
public section

namespace CH.CompromiseInverseConeLimit

abbrev Vertex := Fin 5

@[expose] noncomputable def M : Matrix Vertex Vertex ℝ :=
  !![0, -2 / 3, -2 / 3, -2 / 3, 2;
     1 / 2, 0, -1 / 3, 1 / 3, -1 / 3;
     1 / 2, 1 / 3, 0, -1 / 3, -1 / 3;
     1 / 2, -1 / 3, 1 / 3, 0, -1 / 3;
     -2, 1 / 3, 1 / 3, 1 / 3, 0]

@[expose] noncomputable def inverseTable : Matrix Vertex Vertex ℝ :=
  !![1, 2, 2, 2, 2;
     2, 4, 3, 5, 3;
     2, 5, 4, 3, 3;
     2, 3, 5, 4, 3;
     3 / 2, 4, 4, 4, 3]

theorem right_inverse : M * (-inverseTable) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M, inverseTable, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem left_inverse : (-inverseTable) * M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M, inverseTable, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem matrix_invertible : IsUnit M :=
  ⟨⟨M, -inverseTable, right_inverse, left_inverse⟩, rfl⟩

theorem negative_inverse : negativeInverse M = inverseTable := by
  have identity : M⁻¹ = -inverseTable := Matrix.inv_eq_right_inv right_inverse
  ext i j
  change -(M⁻¹ i j) = inverseTable i j
  rw [identity]
  simp only [Matrix.neg_apply, neg_neg]

theorem inverse_positive (i j : Vertex) : 0 < negativeInverse M i j := by
  rw [negative_inverse]
  fin_cases i <;> fin_cases j <;> norm_num [inverseTable]

theorem zero_diagonal (i : Vertex) : M i i = 0 := by
  fin_cases i <;> norm_num [M]

@[expose] def CoreFair (j : Vertex) (r : Vertex → ℝ) : Prop :=
  (∀ v, 0 ≤ r v) ∧ r j = 0 ∧ (∃ v, 0 < r v) ∧
    ∀ u, u ≠ j → 0 ≤ col M r u

theorem point_column (j k : Vertex) : col M (point j) k = M j k := by
  simp only [col, point, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

theorem deletion_zero_nonempty : CoreFair 0 (point 4) := by
  refine ⟨(point_mem 4).1, by norm_num [point], ⟨4, by norm_num [point]⟩, ?_⟩
  intro u hu
  rw [point_column]
  fin_cases u <;> norm_num [M]
  exact hu rfl

theorem zero_deletion_ray (r : Vertex → ℝ) (fair : CoreFair 0 r) :
    0 < r 4 ∧ ∀ v, r v = r 4 * point 4 v := by
  have c4 := fair.2.2.2 4 (by decide)
  norm_num [col, M, Fin.sum_univ_succ, fair.2.1] at c4
  have z1 : r 1 = 0 := by linarith [fair.1 1, fair.1 2, fair.1 3]
  have z2 : r 2 = 0 := by linarith [fair.1 1, fair.1 2, fair.1 3]
  have z3 : r 3 = 0 := by linarith [fair.1 1, fair.1 2, fair.1 3]
  have formula (v : Vertex) : r v = r 4 * point 4 v := by
    fin_cases v <;> simp [point, fair.2.1, z1, z2, z3]
  have positive : 0 < r 4 := by
    obtain ⟨v, hv⟩ := fair.2.2.1
    rw [formula] at hv
    have hn : 0 ≤ point 4 v := (point_mem 4).1 v
    nlinarith
  exact ⟨positive, formula⟩

theorem zero_deletion_columns (r : Vertex → ℝ) (fair : CoreFair 0 r) (k : Vertex) :
    col M r k = r 4 * M 4 k := by
  have formula := (zero_deletion_ray r fair).2
  calc
    col M r k = col M (fun v => r 4 * point 4 v) k :=
      congrArg (fun f => col M f k) (funext formula)
    _ = r 4 * col M (point 4) k := by simp only [col, mul_assoc, mul_sum]
    _ = _ := by rw [point_column]

/-- The three positive branches are forced for every certificate, not
just for one chosen solution of a linear system. -/
theorem three_targets (r : Vertex → ℝ) (fair : CoreFair 0 r) :
    col M r 0 < 0 ∧ 0 < col M r 1 ∧ 0 < col M r 2 ∧ 0 < col M r 3 := by
  have rp := (zero_deletion_ray r fair).1
  simp only [zero_deletion_columns r fair]
  norm_num [M]
  exact rp

theorem no_single_target (r : Vertex → ℝ) (fair : CoreFair 0 r) (u : Vertex) :
    ∃ k, k ≠ 0 ∧ k ≠ u ∧ 0 < col M r k := by
  obtain ⟨_, p1, p2, _⟩ := three_targets r fair
  by_cases u1 : u = 1
  · exact ⟨2, by decide, by rw [u1]; decide, p2⟩
  · exact ⟨1, by decide, Ne.symm u1, p1⟩

theorem normalized_certificate_unique (r : Vertex → ℝ) (fair : CoreFair 0 r)
    (normalized : col M r 0 = -1) : r = fun v => point 4 v / 2 := by
  have equation := zero_deletion_columns r fair 0
  rw [normalized] at equation
  norm_num [M] at equation
  have value : r 4 = 1 / 2 := by linarith
  funext v
  rw [(zero_deletion_ray r fair).2, value]
  ring

@[expose] noncomputable def rates : Vertex → ℝ := ![0, 1 / 6, 1 / 6, 1 / 6, 0]

theorem exact_normalized_columns (r : Vertex → ℝ) (fair : CoreFair 0 r)
    (normalized : col M r 0 = -1) (k : Vertex) :
    col M r k = (if k = 0 then -1 else 0) + rates k := by
  rw [normalized_certificate_unique r fair normalized]
  simp only [col, point, ite_div, zero_div, ite_mul, zero_mul, sum_ite_eq',
    mem_univ, ite_true]
  fin_cases k <;> norm_num [M, rates]

theorem inverse_packing_residual (k : Vertex) :
    inverseTable 0 k - ∑ u, rates u * inverseTable u k = point 4 k / 2 := by
  fin_cases k <;> norm_num [inverseTable, rates, point, Fin.sum_univ_succ]

@[expose] noncomputable def badWeight : Vertex → ℝ := ![9, 17, 17, 17, 33 / 2]

theorem strictly_bad (v : Vertex) : 0 < badWeight v ∧ row M badWeight v = -1 := by
  fin_cases v <;> norm_num [row, M, badWeight, Fin.sum_univ_succ]

/-- The missing global hypothesis is substantive: this different
principal deletion has no fair measure at all. -/
theorem deletion_one_empty (r : Vertex → ℝ) : ¬ CoreFair 1 r := by
  intro fair
  have c0 := fair.2.2.2 0 (by decide)
  have c2 := fair.2.2.2 2 (by decide)
  have c3 := fair.2.2.2 3 (by decide)
  have c4 := fair.2.2.2 4 (by decide)
  norm_num [col, M, Fin.sum_univ_succ, fair.2.1] at c0 c2 c3 c4
  have z0 : r 0 = 0 := by linarith [fair.1 0, fair.1 2]
  have z2 : r 2 = 0 := by linarith [fair.1 2, fair.1 3, fair.1 4]
  have z3 : r 3 = 0 := by linarith [fair.1 2, fair.1 3, fair.1 4]
  have z4 : r 4 = 0 := by linarith [fair.1 2, fair.1 3, fair.1 4]
  have z1 : r 1 = 0 := fair.2.1
  have zero (v : Vertex) : r v = 0 := by
    fin_cases v <;> assumption
  obtain ⟨v, hv⟩ := fair.2.2.1
  rw [zero] at hv
  linarith

theorem not_deletedLeft : ¬ DeletedLeft M := by
  intro deleted
  obtain ⟨p, hp, zero, cols⟩ := deleted 1
  exact deletion_one_empty p ⟨hp.1, zero, simplex_has_positive hp, cols⟩

theorem ratio_obstruction :
    (∀ u : Vertex, u ≠ 1 → inverseTable u 1 ≤ (5 / 4) * inverseTable u 2) ∧
      (5 / 4) * inverseTable 1 2 < inverseTable 1 1 := by
  constructor
  · intro u hu
    fin_cases u <;> norm_num [inverseTable]
    exact hu rfl
  · norm_num [inverseTable]

/-- The new general ratio restriction independently excludes the
matrix from the all-deletions hypothesis. -/
theorem not_deletedLeft_by_ratio : ¬ DeletedLeft M := by
  intro deleted
  have propagated := CH.CompromiseInverseRatios.deletedLeft_ratio_propagation M
    matrix_invertible deleted badWeight (fun v => (strictly_bad v).1.le)
    (fun v => by rw [(strictly_bad v).2]; norm_num) 1 2 (5 / 4) (by norm_num)
    (by simpa only [negative_inverse] using ratio_obstruction.1)
  rw [negative_inverse] at propagated
  linarith [ratio_obstruction.2]

/-- Each coordinate separately admits a target from the actual feedback
support. The choice must depend on the coordinate. -/
theorem coordinatewise_target (k : Vertex) :
    ∃ u, u ≠ 0 ∧ 0 < rates u ∧
      inverseTable 0 0 * inverseTable u k ≤ inverseTable u 0 * inverseTable 0 k := by
  fin_cases k
  · exact ⟨1, by decide, by norm_num [rates], by norm_num [inverseTable]⟩
  · exact ⟨1, by decide, by norm_num [rates], by norm_num [inverseTable]⟩
  · exact ⟨1, by decide, by norm_num [rates], by norm_num [inverseTable]⟩
  · exact ⟨2, by decide, by norm_num [rates], by norm_num [inverseTable]⟩
  · exact ⟨1, by decide, by norm_num [rates], by norm_num [inverseTable]⟩

theorem no_uniform_target : ¬ ∃ u, u ≠ 0 ∧ ∀ k,
    inverseTable 0 0 * inverseTable u k ≤ inverseTable u 0 * inverseTable 0 k := by
  rintro ⟨u, hu, bound⟩
  fin_cases u
  · exact hu rfl
  · have h := bound 3
    norm_num [inverseTable] at h
  · have h := bound 1
    norm_num [inverseTable] at h
  · have h := bound 2
    norm_num [inverseTable] at h
  · have h := bound 1
    norm_num [inverseTable] at h

/-- Fractional entries make this a matrix diagnostic, not even the
coefficient matrix of an arbitrary finite directed graph. -/
theorem not_graph_coefficient (adj : Vertex → Vertex → Prop) [DecidableRel adj] :
    M ≠ coefficient adj := by
  intro same
  have entry := congrFun (congrFun same 0) 1
  norm_num [M, coefficient, CH.CompromisePacking.capacity] at entry
  split_ifs at entry <;> norm_num at entry

end CH.CompromiseInverseConeLimit

#print axioms CH.CompromiseInverseConeLimit.matrix_invertible
#print axioms CH.CompromiseInverseConeLimit.inverse_positive
#print axioms CH.CompromiseInverseConeLimit.zero_diagonal
#print axioms CH.CompromiseInverseConeLimit.zero_deletion_ray
#print axioms CH.CompromiseInverseConeLimit.no_single_target
#print axioms CH.CompromiseInverseConeLimit.exact_normalized_columns
#print axioms CH.CompromiseInverseConeLimit.inverse_packing_residual
#print axioms CH.CompromiseInverseConeLimit.strictly_bad
#print axioms CH.CompromiseInverseConeLimit.not_deletedLeft
#print axioms CH.CompromiseInverseConeLimit.not_deletedLeft_by_ratio
#print axioms CH.CompromiseInverseConeLimit.coordinatewise_target
#print axioms CH.CompromiseInverseConeLimit.no_uniform_target
#print axioms CH.CompromiseInverseConeLimit.not_graph_coefficient
