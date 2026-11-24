import checkpoints.shen_extension.SharedArcLoopTest

namespace LeanCH.BR.Closure.SharedArcCompression
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier FiniteCutInverse
open scoped Matrix

/-- A property entirely determined by the two specified attachments. -/
noncomputable def winning {q n} (X : Model q n) (F : Family) (B M : Finset ℕ) : Prop :=
  let G := graph X.D (insert B (insert M F))
  let E := graph X.D (insert M F)
  let T : Finset X.V := univ.filter (fun j : X.V => j.val ∈ targets X.D X.V F B)
  let H := (excess (realMatrix q G X.V))⁻¹
  let K : Matrix T T ℝ := fun k j => ∑ i : X.V, H k i *
    (realMatrix q G X.V i j - realMatrix q E X.V i j)
  PacketCompression.loopTest q K

theorem winning_iff {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B) (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (M : Finset ℕ) : winning X F B M ↔ SmallRow q (graph X.D (insert M F)) X.V := by
  obtain ⟨_,H,inv,eq⟩ := loop_test X small step bad M
  have he := Matrix.inv_eq_right_inv inv.right
  subst H
  exact eq.symm

/-- The outstanding graph-theoretic existence claim. All matrices and
pivots are defined by the source and the two chosen cycles. -/
def HasWinningCompetitor {q n} (X : Model q n) : Prop :=
  ∀ C F B, Built X.D C F → F ⊆ family X → support F = X.V → SmallRow q (graph X.D F) X.V →
    Boundary X F B → (∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card) →
    ¬SmallRow q (graph X.D (insert B F)) X.V → ∃ M, Boundary X F M ∧ winning X F B M

theorem ch_of_loop (supply : ∀ q n, ∀ X : Model q n, 2 ≤ q → SmallerSmallRow q X.V.card →
    HasWinningCompetitor X) : CH.CaccettaHaggkvistConjecture := by
  apply SharedArcInduction.ch_of_extension
  intro q n X hq small
  exfalso
  classical
  obtain ⟨u,uv⟩ := X.live
  obtain ⟨C,_,cc,_,_,_,_⟩ := ShortestReturnCertificate.on_model X hq uv
  have cf : C ∈ family X := mem_filter.mpr ⟨mem_powerset.mpr cc.sub,cc⟩
  obtain ⟨F,built,sub,_,spans,old,_,next,stop⟩ := SharedArcBarrier.on_source X hq small cf
  obtain ⟨B,step,least,_⟩ := SharedArcPacketDescent.terminal X hq small next (fun M b => (stop M b).1)
  obtain ⟨M,bm,win⟩ := supply q n X hq small C F B built sub spans old step least (stop B step).1
  exact (stop M bm).1 ((winning_iff X small step (stop B step).1 M).mp win)

end LeanCH.BR.Closure.SharedArcCompression

#print axioms LeanCH.BR.Closure.SharedArcCompression.ch_of_loop

