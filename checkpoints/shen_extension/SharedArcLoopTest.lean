import checkpoints.shen_extension.PacketLoopTest
import checkpoints.shen_extension.SharedArcCompression

namespace LeanCH.BR.Closure.SharedArcCompression
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier FiniteCutInverse
open scoped Matrix

/-- Exact loop test on a boundary competitor, with at most q pivots and
no unknown price variables. The union inverse is supplied by induction. -/
theorem loop_test {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B) (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (M : Finset ℕ) :
    let G := graph X.D (insert B (insert M F))
    let E := graph X.D (insert M F)
    let T : Finset X.V := univ.filter (fun j : X.V => j.val ∈ targets X.D X.V F B)
    T.card ≤ q ∧ ∃ H : Matrix X.V X.V ℝ, CommonInverse (realMatrix q G X.V) H ∧
      let K : Matrix T T ℝ := fun k j => ∑ i : X.V, H k i *
        (realMatrix q G X.V i j - realMatrix q E X.V i j)
      (SmallRow q E X.V ↔ PacketCompression.loopTest q K) := by
  classical
  intro G E T
  obtain ⟨size,H,inv,certificate⟩ := competitor X small step bad M
  refine ⟨size,H,inv,?_⟩
  intro K
  have sub (i j : ℕ) (h : E i j = true) : G i j=true := by
    obtain ⟨A,ha⟩ := active.mp h
    obtain ⟨af,ia,ja,ed⟩ := mem_col.mp ha
    exact active.mpr ⟨A,mem_col.mpr ⟨mem_insert_of_mem af,ia,ja,ed⟩⟩
  have nn (i j : T) : 0 ≤ K i j := sum_nonneg fun a _ => mul_nonneg (inv.nonneg i a)
    (sub_nonneg.mpr (realMatrix_mono_graph (fun u _ v _ h => sub u v h) a j))
  exact certificate.trans (PacketCompression.loopTest_iff q K nn (by simpa only [Fintype.card_coe] using size)).symm

end LeanCH.BR.Closure.SharedArcCompression

#print axioms LeanCH.BR.Closure.SharedArcCompression.loop_test

