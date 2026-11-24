module

public import LeanCH.CompromiseTailCut
public import LeanCH.CompromiseSharedPaths

set_option linter.style.header false

/-! One hand-specified graph where two arcs jointly lose an endpoint
that survives either single-arc deletion. Another tail arc is retained.
The graph has independent out-neighbourhoods and satisfies weighted K*. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseCritical CH.CompromiseDeletion CH.CompromiseLostArc
open CH.CompromiseTailCut
public section

namespace CH.CompromiseCollectiveLossExample

abbrev Vertex := Fin 7

@[expose] def edge (v u : Vertex) : Prop :=
  (v = 0 ∧ (u = 1 ∨ u = 2 ∨ u = 3)) ∨
  ((v = 1 ∨ v = 2) ∧ u = 4) ∨ (v = 3 ∧ u = 6) ∨
  (v = 4 ∧ u = 5) ∨ (v = 5 ∧ u = 0) ∨ (v = 6 ∧ u = 5)

instance : DecidableRel edge := fun v u => by unfold edge; infer_instance

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v u, edge v u → ¬ edge u v) ∧
      (∀ v u z, edge v u → edge u z → ¬ edge z v) := by decide

theorem independent_heads : ∀ v a b, edge v a → edge v b → ¬ edge a b := by decide

theorem tail_heads : outN edge 0 = {1, 2, 3} := by
  simp only [Finset.ext_iff, mem_outN]
  decide

theorem original_seconds : second edge 0 = {4, 6} := by
  simp only [Finset.ext_iff, mem_second]
  decide

theorem single_arc_losses_empty : lostSecond edge 0 1 = ∅ ∧ lostSecond edge 0 2 = ∅ := by
  constructor <;>
    simp only [Finset.ext_iff, CH.CompromiseSharedPaths.mem_lost_iff, mem_second, notMem_empty] <;>
    decide

theorem retained_seconds : second (retain edge 0 {3}) 0 = {6} := by
  simp only [Finset.ext_iff, mem_second]
  decide

theorem collective_loss :
    removedHeads edge 0 {3} = {1, 2} ∧
    lostEndpoints edge 0 {3} = {4} ∧ gainedEndpoints edge 0 {3} = ∅ := by
  rw [removedHeads, tail_heads, lostEndpoints, gainedEndpoints, original_seconds, retained_seconds]
  decide

theorem retained_head_nonempty : ({3} : Finset Vertex).Nonempty ∧
    {3} ⊆ outN edge 0 ∧ ({3} : Finset Vertex) ≠ outN edge 0 := by
  rw [tail_heads]
  decide

theorem exact_unit_gain :
    surplus (retain edge 0 {3}) (fun _ => 1) 0 - surplus edge (fun _ => 1) 0 = 3 := by
  rw [exact_gain edge oriented_triangle_free.2.1 0 {3} retained_head_nonempty.2.1,
    collective_loss.1, collective_loss.2.1, collective_loss.2.2]
  norm_num [mass]

theorem compromise_all_weights (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 ≤ surplus edge w v := by
  obtain ⟨v, hv⟩ := compromise_independent edge w hw oriented_triangle_free.2.1 independent_heads
  refine ⟨v, ?_⟩
  dsimp [surplus]
  linarith

end CH.CompromiseCollectiveLossExample

#print axioms CH.CompromiseCollectiveLossExample.oriented_triangle_free
#print axioms CH.CompromiseCollectiveLossExample.single_arc_losses_empty
#print axioms CH.CompromiseCollectiveLossExample.collective_loss
#print axioms CH.CompromiseCollectiveLossExample.exact_unit_gain
#print axioms CH.CompromiseCollectiveLossExample.compromise_all_weights
