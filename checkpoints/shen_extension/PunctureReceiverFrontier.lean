import checkpoints.shen_extension.PunctureWeightCoverage
import checkpoints.shen_extension.PuncturedDistance

namespace LeanCH.BR.Closure.PunctureReceiverFrontier
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights PuncturedDistance RootedSplice

/-- One transitive triangle with middle t protects t against deletion of any
other label. This local tensor criterion has no support-size or weight guard. -/
theorem triangle_middle {q n} (X : Model q n) (hq : 2≤q) {p t y}
    (pv : p∈X.V) (tv : t∈X.V) (yv : y∈X.V)
    (pt : X.D p t=true) (ty : X.D t y=true) (py : X.D p y=true) :
    ∀h,h≠t → Covered X.D X.V q h t := by
  intro h ht
  by_contra absent
  have tw := mem_erase.mpr ⟨ht.symm,tv⟩
  rw [missing_arc X hq tw pv yv pt ty absent] at py
  contradiction

/-- Keep the same receiver, its full column of parents, and its full row of heads.
If the marked receiver loses all witnesses, every parent lies one layer before
it and every head one layer after it, with a strict weight cap at the centre. -/
theorem classify {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) :
    Covered X.D X.V q h t ∨
     (X.weights t<(q-1)*X.weights h ∧ X.D h t=false ∧ X.D t h=false ∧
      ∀p∈inN X.D X.V t,∀y∈outN X.D X.V t,
        depth X.D X.V h t=depth X.D X.V h p+1 ∧
        depth X.D X.V h y=depth X.D X.V h t+1 ∧ X.D p y=false) := by
  classical
  by_cases good : Covered X.D X.V q h t
  · exact Or.inl good
  have large := Nat.le_mul_of_pos_right q (show 0<q-1 by omega)
  have th := Bool.eq_false_iff.mpr (fun yes => good (PunctureWeightCoverage.parent_covered X hq tw minimum (by omega) yes))
  refine Or.inr ⟨lt_of_not_ge (fun heavy => good (PunctureWeightCoverage.heavy_covered X hq hv tw minimum size heavy)),
    Bool.eq_false_iff.mpr (fun yes => good (PunctureWeightCoverage.head_covered X hq hv tw minimum size yes)),th,?_⟩
  intro p pi y yi
  obtain ⟨pv,pt⟩ := mem_inN.mp pi
  obtain ⟨yv,ty⟩ := mem_outN.mp yi
  have tv := mem_of_mem_erase tw
  have nh : y≠h := by rintro rfl; rw [th] at ty; contradiction
  have c1 := edge_cycle X hq pv tv pt
  have c2 := edge_cycle X hq tv yv ty
  have first := retained_or_rise X.free (mem_erase.mp tw).1 pt c1
  have second := retained_or_rise X.free nh ty c2
  rw [sdiff_singleton_eq_erase] at first second
  exact ⟨first.resolve_left (fun ⟨A,c,_,ta⟩ => good ⟨A,c,ta⟩),
    second.resolve_left (fun ⟨A,c,ta,_⟩ => good ⟨A,c,ta⟩),
    missing_arc X hq tw pv yv pt ty good⟩

#print axioms triangle_middle
#print axioms classify
end LeanCH.BR.Closure.PunctureReceiverFrontier
