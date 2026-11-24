module

public import LeanCH.CompromiseRegainedSlack

set_option linter.style.header false

/-! A hand-specified seven-vertex graph. Deleting vertex 6 leaves a
directed six-cycle with a flat fair probability. Restoring 6 produces
positive retained slack entirely from regained private paths, despite
a negative omitted slack. The full graph satisfies weighted K*. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromisePerturbation CH.CompromiseLostArc
public section

namespace CH.CompromiseRegainedSlackExample

abbrev Vertex := Fin 7

@[expose] def edge (v u : Vertex) : Prop :=
  (v = 0 ∧ (u = 1 ∨ u = 6)) ∨ (v = 1 ∧ (u = 2 ∨ u = 6)) ∨
  (v = 2 ∧ u = 3) ∨ (v = 3 ∧ u = 4) ∨ (v = 4 ∧ u = 5) ∨
  (v = 5 ∧ u = 0) ∨ (v = 6 ∧ u = 4)

instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

@[expose] noncomputable def r (v : Vertex) : ℝ := if v = 6 then 0 else 1 / 6

@[expose] def secondTable : Vertex → Finset Vertex :=
  ![{2, 4}, {3, 4}, {4}, {5}, {0}, {1, 6}, {5}]

@[expose] def coefficients : Matrix Vertex Vertex ℝ :=
  !![0, -2, 1, 0, 1, 1, -2;
     1, 0, -2, 1, 1, 0, -2;
     0, 1, 0, -2, 1, 0, 0;
     0, 0, 1, 0, -2, 1, 0;
     1, 0, 0, 1, 0, -2, 1;
     -2, 1, 0, 0, 1, 0, 1;
     1, 1, 0, 0, -2, 1, 0]

@[expose] noncomputable def fullCertificate : Vertex → ℝ := ![8, 4, 9, 0, 14, 19, 20]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem seconds : ∀ v, second edge v = secondTable v := by
  simp only [Finset.ext_iff, mem_second]
  decide

theorem coefficient_values (v u : Vertex) : coefficient edge v u = coefficients v u := by
  simp only [coefficient, CH.CompromisePacking.capacity, seconds]
  fin_cases v <;> fin_cases u <;> norm_num [secondTable, coefficients, edge]

theorem probability : r ∈ simplex := by
  constructor
  · intro v
    unfold r
    split_ifs <;> norm_num
  · norm_num [r, Fin.sum_univ_succ]

theorem original_slacks (u : Vertex) : col (coefficient edge) r u =
    if u = 4 then 1 / 3 else if u = 6 then -1 / 3 else 0 := by
  simp only [col, coefficient_values]
  fin_cases u <;> norm_num [coefficients, r, Fin.sum_univ_succ]

theorem regained_sets : ∀ u,
    gainedIn edge (univ.erase 6) u = if u = 4 then {0, 1} else ∅ := by
  simp only [Finset.ext_iff, gainedIn, mem_sdiff, mem_inter, mem_secondIn,
    restrictedSecondIn, mem_filter, mem_erase, mem_univ, and_true]
  decide

theorem regained_mass (u : Vertex) : mass r (gainedIn edge (univ.erase 6) u) =
    if u = 4 then 1 / 3 else 0 := by
  rw [regained_sets]
  by_cases h : u = 4
  · norm_num [h, mass, r]
  · simp [h, mass]

theorem general_local_slacks (p : Vertex → ℝ) (p6 : p 6 = 0) (u : Vertex) :
    localSlack edge p (univ.erase 6) u =
      ![p 1 + p 4 - 2 * p 5, p 2 + p 5 - 2 * p 0,
        p 0 + p 3 - 2 * p 1, p 1 + p 4 - 2 * p 2,
        p 2 + p 5 - 2 * p 3, p 0 + p 3 - 2 * p 4,
        p 4 + p 5 - 2 * p 0 - 2 * p 1] u := by
  have support : ∀ v, v ∉ (univ : Finset Vertex).erase 6 → p v = 0 := by
    intro v hv
    have he : v = 6 := by simpa using hv
    simpa only [he] using p6
  have ident := fair_deletion_identity edge p (univ.erase 6) support u
  rw [← col_coefficient, regained_sets] at ident
  simp only [col, coefficient_values] at ident
  fin_cases u <;>
    norm_num [coefficients, Fin.sum_univ_succ, mass, p6] at ident ⊢ <;> linarith

theorem local_slacks_zero (u : Vertex) (retained : u ≠ 6) :
    localSlack edge r (univ.erase 6) u = 0 := by
  have support : ∀ v, v ∉ (univ : Finset Vertex).erase 6 → r v = 0 := by
    intro v hv
    have he : v = 6 := by simpa using hv
    simp [r, he]
  have identity := fair_deletion_identity edge r (univ.erase 6) support u
  rw [← col_coefficient, original_slacks, regained_mass] at identity
  rw [ite_eq_right retained] at identity
  split_ifs at identity <;> linarith

theorem deleted_fair : FairOn edge (univ.erase 6) r := by
  refine ⟨probability.1, ?_, ⟨0, by decide, by norm_num [r]⟩, ?_⟩
  · intro v hv
    have he : v = 6 := by simpa using hv
    simp [r, he]
  · intro u hu
    have h := local_slacks_zero u (mem_erase.mp hu).1
    dsimp [localSlack] at h
    linarith

/-- Changing the deleted certificate cannot fix this local example:
the directed six-cycle has only its uniform fair probability. -/
theorem deleted_probability_unique (p : Vertex → ℝ) (prob : p ∈ simplex)
    (fair : FairOn edge (univ.erase 6) p) : p = r := by
  have p6 : p 6 = 0 := fair.2.1 6 (by simp)
  have nonneg (u : Vertex) (hu : u ≠ 6) :
      0 ≤ localSlack edge p (univ.erase 6) u := by
    have h := fair.2.2.2 u (by simp [hu])
    dsimp [localSlack]
    linarith
  have h0 := nonneg 0 (by decide)
  have h1 := nonneg 1 (by decide)
  have h2 := nonneg 2 (by decide)
  have h3 := nonneg 3 (by decide)
  have h4 := nonneg 4 (by decide)
  have h5 := nonneg 5 (by decide)
  norm_num [general_local_slacks p p6] at h0 h1 h2 h3 h4 h5
  have total := prob.2
  norm_num [Fin.sum_univ_succ, p6] at total
  funext v
  fin_cases v <;> norm_num [r] <;> linarith

theorem private_paths : lostSecond edge 0 6 = {4} ∧
    lostSecond edge 1 6 = {4} ∧
    lost edge (univ.erase 6) 0 = {4} ∧ lost edge (univ.erase 6) 1 = {4} := by
  have at_zero : lostSecond edge 0 6 = {4} := by
    simp only [Finset.ext_iff, CH.CompromiseSharedPaths.mem_lost_iff, mem_second, mem_singleton]
    decide
  have at_one : lostSecond edge 1 6 = {4} := by
    simp only [Finset.ext_iff, CH.CompromiseSharedPaths.mem_lost_iff, mem_second, mem_singleton]
    decide
  refine ⟨at_zero, at_one, ?_, ?_⟩
  · simpa only [CH.CompromiseRegainedSlack.singleton_lost_eq_arc] using at_zero
  · simpa only [CH.CompromiseRegainedSlack.singleton_lost_eq_arc] using at_one

/-- All retained original slack is regained path mass, while the
omitted column is strictly negative and private paths really exist. -/
theorem entirely_regained :
    col (coefficient edge) r 6 = -1 / 3 ∧
    col (coefficient edge) r 4 = 1 / 3 ∧
    mass r (gainedIn edge (univ.erase 6) 4) = 1 / 3 ∧
    (∀ u, u ≠ 6 → localSlack edge r (univ.erase 6) u = 0) := by
  refine ⟨?_, ?_, ?_, local_slacks_zero⟩
  · norm_num [original_slacks]
  · norm_num [original_slacks]
  · norm_num [regained_mass]

theorem full_slacks (u : Vertex) : col (coefficient edge) fullCertificate u =
    if u = 1 then 32 else if u = 6 then 9 else 0 := by
  simp only [col, coefficient_values]
  fin_cases u <;> norm_num [coefficients, fullCertificate, Fin.sum_univ_succ]

/-- The example is known-good for every nonnegative weighting; it is
not a strict-counterweight or minimal-counterexample construction. -/
theorem compromise_all_weights (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 ≤ surplus edge w v := by
  have positive : ∃ v, 0 < fullCertificate v := ⟨0, by norm_num [fullCertificate]⟩
  have pn (v : Vertex) : 0 ≤ fullCertificate v := by
    fin_cases v <;> norm_num [fullCertificate]
  have cols (u : Vertex) : 0 ≤ col (coefficient edge) fullCertificate u := by
    rw [full_slacks]
    split_ifs <;> norm_num
  obtain ⟨v, hv⟩ := good_of_left (coefficient edge) fullCertificate pn positive cols w hw
  exact ⟨v, by simpa only [row_coefficient] using hv⟩

end CH.CompromiseRegainedSlackExample

#print axioms CH.CompromiseRegainedSlackExample.oriented_triangle_free
#print axioms CH.CompromiseRegainedSlackExample.deleted_fair
#print axioms CH.CompromiseRegainedSlackExample.deleted_probability_unique
#print axioms CH.CompromiseRegainedSlackExample.private_paths
#print axioms CH.CompromiseRegainedSlackExample.entirely_regained
#print axioms CH.CompromiseRegainedSlackExample.compromise_all_weights
