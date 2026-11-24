module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Card

set_option linter.style.header false

/-!
One explicit hand-constructed 32-vertex example. `decide` verifies its finite
adjacency and integer-weight counts in the kernel; this is not a graph search.
Primeness is proved in the accompanying paper, not asserted by this module.
-/

open Finset
public section

namespace CH.CompromisePrimeExample

abbrev Vertex := Fin 4 × Fin 4 × Bool

@[expose] def next (i : Fin 4) : Fin 4 := ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

@[expose] def edge (u v : Vertex) : Prop :=
  (u.1 = v.1 ∧ v.2.1 = next u.2.1) ∨
  (v.1 = next u.1 ∧ ¬ (u.2.2 = true ∧ v.2.2 = true ∧ u.2.1 = v.2.1))

instance : DecidableRel edge := fun u v => by unfold edge; infer_instance

@[expose] def weight (v : Vertex) : ℕ := if v.2.2 then 1 else 10
@[expose] def outN (v : Vertex) : Finset Vertex := univ.filter (edge v ·)
@[expose] def inN (v : Vertex) : Finset Vertex := univ.filter (edge · v)
@[expose] def second (v : Vertex) : Finset Vertex :=
  univ.filter (fun z => z ≠ v ∧ ¬ edge v z ∧ ∃ a, edge v a ∧ edge a z)
@[expose] def mass (S : Finset Vertex) : ℕ := ∑ v ∈ S, weight v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Reduce the finite adjacency checks for this one 32-vertex graph in the kernel.
theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ u v, edge u v → ¬ edge v u) ∧
      (∀ u v z, edge u v → edge v z → ¬ edge z u) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Exact second-neighbour sums require checking the 32 possible intermediates.
theorem degree_counts : ∀ v,
    mass (outN v) = (if v.2.2 then 54 else 55) ∧
    mass (inN v) = (if v.2.2 then 54 else 55) ∧
    mass (second v) = (if v.2.2 then 56 else 55) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Check all arcs of the specified graph, with exact integer-weight sums.
theorem capture_bound : ∀ v a, edge v a → mass (outN a \ outN v) ≤ 45 := by decide

theorem every_vertex_geometric : ∀ v, mass (outN v) ^ 2 ≤ mass (inN v) * mass (second v) := by
  intro v
  obtain ⟨ho, hi, hs⟩ := degree_counts v
  rw [ho, hi, hs]
  cases v.2.2 <;> norm_num

theorem every_arc_capture_fails : ∀ v a, edge v a →
    mass (inN v) * mass (outN a \ outN v) < mass (outN v) ^ 2 := by
  intro v a h
  obtain ⟨ho, hi, _⟩ := degree_counts v
  have hc := capture_bound v a h
  rw [ho, hi]
  cases v.2.2 <;> norm_num at * <;> omega

end CH.CompromisePrimeExample

#print axioms CH.CompromisePrimeExample.oriented_triangle_free
#print axioms CH.CompromisePrimeExample.degree_counts
#print axioms CH.CompromisePrimeExample.capture_bound
#print axioms CH.CompromisePrimeExample.every_vertex_geometric
#print axioms CH.CompromisePrimeExample.every_arc_capture_fails
