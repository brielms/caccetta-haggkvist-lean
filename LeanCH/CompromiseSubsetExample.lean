module

public import LeanCH.CompromiseSubset

set_option linter.style.header false

/-! One fixed graph C4[2 T2]: a Seymour vertex need not have nonnegative
singleton set potential, even after a transitive-tournament blow-up. -/

open Finset
public section

namespace CH.CompromiseSubsetExample

abbrev Vertex := Fin 4 × Bool × Bool

@[expose] def next (i : Fin 4) : Fin 4 := ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
@[expose] def edge (v a : Vertex) : Prop :=
  a.1 = next v.1 ∨
    (a.1 = v.1 ∧ a.2.1 = v.2.1 ∧ v.2.2 = false ∧ a.2.2 = true)
instance : DecidableRel edge := fun v a => by unfold edge; infer_instance

@[expose] def outs (v : Vertex) : Finset Vertex := univ.filter (edge v ·)
@[expose] def seconds (v : Vertex) : Finset Vertex :=
  univ.filter (fun a => a ≠ v ∧ ¬ edge v a ∧ ∃ b, edge v b ∧ edge b a)
@[expose] def reach (S : Finset Vertex) : Finset Vertex := S.biUnion outs

theorem outs_eq (v : Vertex) : outs v = CH.CompromiseSeven.outN edge v := by
  ext a
  simp [outs]
theorem seconds_eq (v : Vertex) : seconds v = CH.CompromiseSeven.second edge v := by
  ext a
  simp [seconds]
theorem reach_eq (S : Finset Vertex) : reach S = CH.CompromiseSubset.reach edge S := by
  ext a
  simp [reach, outs]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v a, edge v a → ¬ edge a v) ∧
      (∀ v a b, edge v a → edge a b → ¬ edge b v) := by decide

-- All finite checks concern this specified graph, not a search over graphs.
set_option maxRecDepth 10000 in
theorem counts : ∀ v : Vertex,
    (outs v).card = (if v.2.2 then 4 else 5) ∧
    (seconds v).card = 4 ∧
    (reach (outs v)).card = (if v.2.2 then 6 else 8) := by decide

theorem all_singletons_negative (v : Vertex) :
    1 + (CH.CompromiseSubset.reach edge (CH.CompromiseSeven.outN edge v)).card <
      2 * (CH.CompromiseSeven.outN edge v).card := by
  obtain ⟨ho, _, ht⟩ := counts v
  rw [outs_eq] at ho
  rw [reach_eq, outs_eq] at ht
  rw [ho, ht]
  cases v.2.2 <;> norm_num

theorem upper_seymour (i : Fin 4) (b : Bool) :
    (CH.CompromiseSeven.outN edge (i, b, true)).card ≤
      (CH.CompromiseSeven.second edge (i, b, true)).card := by
  obtain ⟨ho, hs, _⟩ := counts (i, b, true)
  rw [outs_eq] at ho
  rw [seconds_eq] at hs
  rw [ho, hs]
  norm_num

@[expose] def fibre : Finset Vertex := {(0, false, false), (0, false, true)}

theorem fibre_counts : fibre.card = 2 ∧ (reach fibre).card = 5 ∧
    (reach (reach fibre)).card = 8 := by decide

theorem fibre_potential_zero :
    fibre.card + (CH.CompromiseSubset.reach edge (CH.CompromiseSubset.reach edge fibre)).card =
      2 * (CH.CompromiseSubset.reach edge fibre).card := by
  obtain ⟨hs, h1, h2⟩ := fibre_counts
  rw [reach_eq] at h1
  rw [reach_eq, reach_eq] at h2
  rw [hs, h1, h2]

end CH.CompromiseSubsetExample

#print axioms CH.CompromiseSubsetExample.oriented_triangle_free
#print axioms CH.CompromiseSubsetExample.all_singletons_negative
#print axioms CH.CompromiseSubsetExample.upper_seymour
#print axioms CH.CompromiseSubsetExample.fibre_potential_zero
