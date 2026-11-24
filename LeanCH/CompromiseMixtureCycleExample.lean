module

public import LeanCH.CompromiseDeletionMixture

set_option linter.style.header false

/-! A hand-specified directed four-cycle and four actual induced
certificates. Every individual feedback product is below one, but
the equal mixture is a full fair probability. Branching contributions
must be added before deciding whether the omitted columns are paid. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromisePerturbation CH.CompromiseDeletionMixture
public section

namespace CH.CompromiseMixtureCycleExample

abbrev Vertex := Fin 4

@[expose] def edge (v u : Vertex) : Prop :=
  (v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 2) ∨
  (v = 2 ∧ u = 3) ∨ (v = 3 ∧ u = 0)

instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

@[expose] def next : Vertex → Vertex := ![1, 2, 3, 0]
@[expose] def prev : Vertex → Vertex := ![3, 0, 1, 2]

@[expose] noncomputable def r (j v : Vertex) : ℝ :=
  if v = next j then 1 / 3 else if v = prev j then 2 / 3 else 0

@[expose] def secondTable : Vertex → Finset Vertex := ![{2}, {3}, {0}, {1}]

@[expose] def coefficients : Matrix Vertex Vertex ℝ :=
  !![0, -2, 1, 1; 1, 0, -2, 1; 1, 1, 0, -2; -2, 1, 1, 0]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem seconds : ∀ v, second edge v = secondTable v := by
  simp only [Finset.ext_iff, mem_second]
  decide

theorem coefficient_values (v u : Vertex) : coefficient edge v u = coefficients v u := by
  simp only [coefficient, CH.CompromisePacking.capacity, seconds]
  fin_cases v <;> fin_cases u <;> norm_num [secondTable, coefficients, edge]

theorem omitted_mass (j : Vertex) : r j j = 0 := by
  fin_cases j <;> norm_num [r, next, prev]

theorem probability (j : Vertex) : r j ∈ simplex := by
  constructor
  · intro v
    unfold r
    split_ifs <;> norm_num
  · fin_cases j <;> norm_num [r, next, prev, Fin.sum_univ_succ]

theorem original_slacks (j u : Vertex) : col (coefficient edge) (r j) u =
    if u = j then -1 else if u = next j then 2 / 3 else
      if u = prev j then 1 / 3 else 0 := by
  simp only [col, coefficient_values]
  fin_cases j <;> fin_cases u <;> norm_num [coefficients, r, next, prev, Fin.sum_univ_succ]

theorem regained_sets : ∀ j u,
    gainedIn edge (univ.erase j) u = if u = next j then {prev j} else ∅ := by
  simp only [Finset.ext_iff, gainedIn, mem_sdiff, mem_inter, mem_secondIn,
    restrictedSecondIn, mem_filter, mem_erase, mem_univ, and_true]
  decide

theorem regained_mass (j u : Vertex) : mass (r j) (gainedIn edge (univ.erase j) u) =
    if u = next j then 2 / 3 else 0 := by
  rw [regained_sets]
  fin_cases j <;> fin_cases u <;> norm_num [r, next, prev, mass]

theorem local_slacks (j u : Vertex) (retained : u ≠ j) :
    localSlack edge (r j) (univ.erase j) u = if u = prev j then 1 / 3 else 0 := by
  have support : ∀ v, v ∉ (univ : Finset Vertex).erase j → r j v = 0 := by
    intro v hv
    have he : v = j := by simpa using hv
    simpa only [he] using omitted_mass j
  have identity := fair_deletion_identity edge (r j) (univ.erase j) support u
  rw [← col_coefficient, original_slacks, regained_mass, ite_eq_right retained] at identity
  have distinct : next j ≠ prev j := by fin_cases j <;> decide
  split_ifs at identity ⊢ <;> first | linarith | aesop

theorem deleted_fair (j : Vertex) : FairOn edge (univ.erase j) (r j) := by
  refine ⟨(probability j).1, ?_, ?_, ?_⟩
  · intro v hv
    have he : v = j := by simpa using hv
    simpa only [he] using omitted_mass j
  · refine ⟨next j, ?_, ?_⟩
    · fin_cases j <;> decide
    · norm_num [r]
  · intro u hu
    have identity := local_slacks j u (mem_erase.mp hu).1
    have nonnegative : 0 ≤ localSlack edge (r j) (univ.erase j) u := by
      rw [identity]
      split_ifs <;> norm_num
    dsimp [localSlack] at nonnegative
    linarith

theorem omitted_deficit (j : Vertex) : -col (coefficient edge) (r j) j = 1 := by
  simp only [original_slacks, ite_true, neg_neg]

theorem feedback_values (j u : Vertex) : feedback edge r j u =
    if u = next j then 2 / 3 else if u = prev j then 1 / 3 else 0 := by
  rw [feedback, omitted_deficit, div_one, original_slacks]
  fin_cases j <;> fin_cases u <;> norm_num [next, prev]

theorem feedback_bounds (j u : Vertex) :
    0 ≤ feedback edge r j u ∧ feedback edge r j u ≤ 2 / 3 := by
  rw [feedback_values]
  split_ifs <;> norm_num

/-- This covers products along every nonempty finite cycle, including
cycles with repeated vertices. No enumeration of cycles is involved. -/
theorem every_nonempty_product_below_one {I : Type*} (s : Finset I) (hne : s.Nonempty)
    (source target : I → Vertex) : (∏ i ∈ s, feedback edge r (source i) (target i)) < 1 := by
  classical
  obtain ⟨i, hi⟩ := hne
  have bound := prod_le_prod_of_subset_of_le_one₀ (singleton_subset_iff.mpr hi)
    (fun k (_ : k ∈ s) => (feedback_bounds (source k) (target k)).1)
    (fun k (_ : k ∈ s) _ => (feedback_bounds (source k) (target k)).2.trans (by norm_num))
  simp only [prod_singleton] at bound
  exact bound.trans_lt ((feedback_bounds (source i) (target i)).2.trans_lt (by norm_num))

theorem feedback_row_sum (j : Vertex) : (∑ u, feedback edge r j u) = 1 := by
  simp only [feedback_values]
  fin_cases j <;> norm_num [next, prev, Fin.sum_univ_succ]

theorem feedback_column_sum (u : Vertex) : (∑ j, feedback edge r j u) = 1 := by
  simp only [feedback_values]
  fin_cases u <;> norm_num [next, prev, Fin.sum_univ_succ]

theorem equal_mixture (v : Vertex) : mixture r (fun _ => 1 / 4) v = 1 / 4 := by
  fin_cases v <;> norm_num [mixture, r, next, prev, Fin.sum_univ_succ]

theorem mixture_slacks_zero (u : Vertex) :
    col (coefficient edge) (mixture r (fun _ => 1 / 4)) u = 0 := by
  simp only [col, coefficient_values, equal_mixture]
  fin_cases u <;> norm_num [coefficients, Fin.sum_univ_succ]

theorem simultaneous_balance (u : Vertex) :
    (1 / 4 : ℝ) * (-col (coefficient edge) (r u) u) =
      ∑ j ∈ univ.erase u, (1 / 4 : ℝ) * col (coefficient edge) (r j) u := by
  have split := sum_erase_add (univ : Finset Vertex)
    (fun j => (1 / 4 : ℝ) * col (coefficient edge) (r j) u) (mem_univ u)
  have zero := mixture_slacks_zero u
  rw [mixture_column] at zero
  linarith

theorem equal_mixture_fair : Fair edge (mixture r (fun _ => 1 / 4)) :=
  mixture_fair edge r deleted_fair (fun _ => 1 / 4) (by intro j; norm_num)
    ⟨0, by norm_num⟩ (fun u => (simultaneous_balance u).le)

theorem compromise_all_weights (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 ≤ surplus edge w v :=
  mixture_compromise edge r deleted_fair (fun _ => 1 / 4) (by intro j; norm_num)
    ⟨0, by norm_num⟩ (fun u => (simultaneous_balance u).le) w hw

end CH.CompromiseMixtureCycleExample

#print axioms CH.CompromiseMixtureCycleExample.oriented_triangle_free
#print axioms CH.CompromiseMixtureCycleExample.deleted_fair
#print axioms CH.CompromiseMixtureCycleExample.every_nonempty_product_below_one
#print axioms CH.CompromiseMixtureCycleExample.simultaneous_balance
#print axioms CH.CompromiseMixtureCycleExample.equal_mixture_fair
#print axioms CH.CompromiseMixtureCycleExample.compromise_all_weights
