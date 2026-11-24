module

public import LeanCH.CompromiseCertificateCharge

set_option linter.style.header false

/-! The generic one-third mass bound at a nonsink is sharp already on
one hand-specified directed path. This is not a K* counterexample. -/

open Finset CH.CompromiseGame CH.CompromiseCritical
public section

namespace CH.CompromiseTailMassExample

abbrev Vertex := Fin 3

@[expose] def edge (v u : Vertex) : Prop := (v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 2)
instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

@[expose] noncomputable def p : Vertex → ℝ := ![1 / 3, 0, 2 / 3]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem probability : p ∈ simplex := by
  constructor
  · intro v
    fin_cases v <;> norm_num [p]
  · norm_num [p, Fin.sum_univ_succ]

theorem slack_values (u : Vertex) :
    col (coefficient edge) p u = if u = 2 then 1 / 3 else 0 := by
  fin_cases u <;>
    norm_num [col, coefficient, CH.CompromisePacking.capacity, edge, p,
      Fin.sum_univ_succ, Fin.exists_fin_succ]

theorem fair : ∀ u, 0 ≤ col (coefficient edge) p u := by
  intro u
  rw [slack_values]
  split_ifs <;> norm_num

theorem sharp_tail : edge 0 1 ∧ p 0 = 1 / 3 := by norm_num [edge, p]

end CH.CompromiseTailMassExample

#print axioms CH.CompromiseTailMassExample.probability
#print axioms CH.CompromiseTailMassExample.fair
#print axioms CH.CompromiseTailMassExample.sharp_tail
