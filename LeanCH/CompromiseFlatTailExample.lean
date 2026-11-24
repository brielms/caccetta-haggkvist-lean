module

public import LeanCH.CompromiseCertificateCharge

set_option linter.style.header false

/-! A fixed example attaining the one-third nonsink certificate bound
even when every column slack is zero. Three sources feed the residue
classes of the nine-vertex circulant with steps one and two. -/

open Finset CH.CompromiseGame CH.CompromiseCritical CH.CompromiseSeven CH.CompromiseDeletion
public section

namespace CH.CompromiseFlatTailExample

abbrev Vertex := Fin 12

@[expose] def edge (v u : Vertex) : Prop :=
  (v.val < 3 ∧ 3 ≤ u.val ∧ (u.val - 3) % 3 = v.val) ∨
  (3 ≤ v.val ∧ 3 ≤ u.val ∧
    ((u.val - 3 + 9 - (v.val - 3)) % 9 = 1 ∨
      (u.val - 3 + 9 - (v.val - 3)) % 9 = 2))

instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

@[expose] noncomputable def p (v : Vertex) : ℝ := if v.val < 3 then 1 / 3 else 0

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem probability : p ∈ simplex := by
  constructor
  · intro v
    unfold p
    split_ifs <;> norm_num
  · norm_num [p, Fin.sum_univ_succ]

theorem source_seconds :
    (∀ u, u ∈ second edge 0 ↔ 3 ≤ u.val ∧ (u.val - 3) % 3 ≠ 0) ∧
    (∀ u, u ∈ second edge 1 ↔ 3 ≤ u.val ∧ (u.val - 3) % 3 ≠ 1) ∧
    (∀ u, u ∈ second edge 2 ↔ 3 ≤ u.val ∧ (u.val - 3) % 3 ≠ 2) := by
  simp only [mem_second]
  decide

theorem all_slacks_zero (u : Vertex) : col (coefficient edge) p u = 0 := by
  have collapse : col (coefficient edge) p u =
      (coefficient edge 0 u + coefficient edge 1 u + coefficient edge 2 u) / 3 := by
    norm_num [col, p, Fin.sum_univ_succ]
    ring
  rw [collapse]
  simp only [coefficient, CH.CompromisePacking.capacity,
    source_seconds.1, source_seconds.2.1, source_seconds.2.2]
  fin_cases u <;> norm_num [edge]

theorem fair : ∀ u, 0 ≤ col (coefficient edge) p u := by
  intro u
  rw [all_slacks_zero]

theorem sharp_tail : edge 0 3 ∧ p 0 = 1 / 3 := by norm_num [edge, p]

theorem sources : ∀ v u, u.val < 3 → ¬ edge v u := by decide

/-- Zero column slacks also allow signed real weights here. -/
theorem compromise_all_weights (w : Vertex → ℝ) :
    ∃ v, 0 ≤ surplus edge w v := by
  by_contra hn
  push Not at hn
  have bad : ∀ v, row (coefficient edge) w v < 0 := by
    intro v
    simpa only [row_coefficient] using hn v
  have neg := payoff_neg (coefficient edge) w p probability bad
  have zero : payoff (coefficient edge) w p = 0 := by
    rw [payoff_transpose]
    simp [all_slacks_zero]
  linarith

end CH.CompromiseFlatTailExample

#print axioms CH.CompromiseFlatTailExample.oriented_triangle_free
#print axioms CH.CompromiseFlatTailExample.probability
#print axioms CH.CompromiseFlatTailExample.all_slacks_zero
#print axioms CH.CompromiseFlatTailExample.sharp_tail
#print axioms CH.CompromiseFlatTailExample.compromise_all_weights
