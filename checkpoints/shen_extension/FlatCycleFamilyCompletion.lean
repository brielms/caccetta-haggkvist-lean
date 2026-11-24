import checkpoints.shen_extension.FlatOverlapDescent

namespace LeanCH.BR.Closure.FlatCycleFamilyCompletion
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShenPrimeTransition FirstPacketBarrier MarkedCyclePeeling
open FlatOverlapDescent ShortestCycleWeights

/-- Add every shortest cycle of the selected graph. No new arc appears,
even when the family is used with the original ambient digraph. -/
theorem complete {q D V F} (hq : 1≤q) (free : QFree D V q)
    (cycles : ∀N∈F,Cycle (graph D F) V q N) :
    ∃G : Family,F⊆G ∧ graph D G=graph D F ∧
      (∀N,N∈G ↔ Cycle (graph D F) V q N) ∧ ∀N∈G,Cycle D V q N := by
  classical
  let E := graph D F
  let G := V.powerset.filter (Cycle E V q)
  have cond (N) : N∈G ↔ Cycle E V q N := by
    exact ⟨fun h => (mem_filter.mp h).2,fun cn => mem_filter.mpr ⟨mem_powerset.mpr cn.sub,cn⟩⟩
  have fg : F⊆G := fun N nf => (cond N).mpr (cycles N nf)
  have native {u v} (edge : E u v=true) : D u v=true := by
    obtain ⟨N,nh⟩ := active.mp edge
    exact (mem_col.mp nh).2.2.2
  have reg {N} (cn : Cycle E V q N) : Cycle D V q N := by
    have deg (u) (un : u∈N) : 1≤(outN D N u).card := by
      rw [←cn.heads u un]
      exact card_le_card fun v hv => mem_outN.mpr ⟨(mem_outN.mp hv).1,native (mem_outN.mp hv).2⟩
    have r := dt_reg hq (ball_q_one q hq) (free.mono_set cn.sub) deg (by simpa using cn.size)
    exact ⟨cn.sub,cn.size,r.1,r.2⟩
  refine ⟨G,fg,?_,cond,fun N ng => reg ((cond N).mp ng)⟩
  funext u v
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro edge
    obtain ⟨N,nw⟩ := active.mp edge
    obtain ⟨ng,un,vn,uv⟩ := mem_col.mp nw
    have cn := (cond N).mp ng
    obtain ⟨w,wh⟩ := card_pos.mp (show 0<(outN E N u).card by rw [cn.heads u un]; decide)
    obtain ⟨wn,uw⟩ := mem_outN.mp wh
    have eq := card_le_one.mp ((reg cn).heads u un).le _ (mem_outN.mpr ⟨wn,native uw⟩) _ (mem_outN.mpr ⟨vn,uv⟩)
    change w=v at eq
    exact eq ▸ uw
  · intro edge
    obtain ⟨N,nw⟩ := active.mp edge
    obtain ⟨nf,rest⟩ := mem_col.mp nw
    exact active.mpr ⟨N,mem_col.mpr ⟨fg nf,rest⟩⟩

/-- On a proper nonempty puncture, the universal slack alternative
has a normalized witness from the smaller-host principle. -/
theorem realized {D V U q} (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (sub : U⊂V) (live : U.Nonempty) (stop : ForcedSlack q D U) :
    ∃p,RealDual q D U 1 p ∧ ∃v∈U,realCol q D U p v<1 := by
  obtain ⟨p,law⟩ := realDual_of_smallRow (small D U (card_lt_card sub) (free.mono_set sub.subset)) live
  exact ⟨p,law,stop p law⟩

/-- The overlap transition stays inside a single completed family on the
same normalized graph. Every new child therefore has the original row
and column data available on the unchanged parent. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F : Family} (sub : F⊆family X) :
    let E := graph X.D F
    ∃G : Family,F⊆G ∧ G⊆family X ∧ graph X.D G=E ∧
      (∀N,N∈G ↔ Cycle E X.V q N) ∧
      ∀A∈G,∀B∈G,A≠B →
        let U := X.V\(A\B)
        X.V=A∪B ∨ ForcedSlack q E U ∨ ∀h∈A∩B,
          ∃M∈G,M⊆U ∧ h∉M ∧ A∩M⊂A∩B ∧
            let U' := X.V\(A\M)
            U'⊂U ∧ (ForcedSlack q E U' ∨ A∩M=∅ ∧ (A\B).card=1 ∧ U'.card+q=U.card) := by
  classical
  intro E
  have cycles (N) (nf : N∈F) := retain_cycle (show Cycle X.D X.V q N from (mem_filter.mp (sub nf)).2) nf
  obtain ⟨G,fg,same,cond,native⟩ := complete (by omega : 1≤q) X.free cycles
  have gx : G⊆family X := fun N ng => mem_filter.mpr ⟨mem_powerset.mpr (native N ng).sub,native N ng⟩
  refine ⟨G,fg,gx,same,cond,?_⟩
  intro A ag B bg ne
  rcases transition hq (PrivateArcEndpoints.graph_free X F) small ((cond A).mp ag) ((cond B).mp bg) ne with
    cover | slack | step
  · exact Or.inl cover
  · exact Or.inr (Or.inl slack)
  · refine Or.inr (Or.inr ?_)
    intro h hh
    obtain ⟨M,cy,rest⟩ := step h hh
    exact ⟨M,(cond M).mpr cy,rest⟩

#print axioms complete
#print axioms realized
#print axioms on_source
end LeanCH.BR.Closure.FlatCycleFamilyCompletion
