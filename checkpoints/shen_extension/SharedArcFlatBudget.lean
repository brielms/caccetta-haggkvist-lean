import checkpoints.shen_extension.SharedArcPivotChoice
import checkpoints.shen_extension.StrictSubgraphInverse

namespace LeanCH.BR.Closure.SharedArcFlatBudget
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier
open scoped Matrix

/-- At a flat family each summand may use its own missing native arc. -/
def Breach {q n} (X : Model q n) (F : Family) : Prop :=
  ∃ w p : ℕ → ℚ, (∀ i∈X.V, 0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧
    (∀ i∈X.V, WeightedSD.row q (graph X.D F) X.V w i=1) ∧
    (∀ i∈X.V, WeightedSD.col q (graph X.D F) X.V p i=1) ∧
    ∃ (pick : X.V → SharedArcFlatCut.Missing X F) (v : X.V),
      let E := realMatrix q (graph X.D F) X.V
      let W := fun i : X.V => (w i:ℝ)
      let P := fun i : X.V => (p i:ℝ)
      let U := realMatrix q X.D X.V - E
      (∑ i : X.V, (SharedArcFlatResponse.test E⁻¹ W P q
        (pick i).val.1 (pick i).val.2 v i / ((q:ℝ)*P (pick i).val.1*W (pick i).val.2))
          * (U *ᵥ W) i) < W v

def ProgressAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ)
    (H : Matrix X.V X.V ℝ) (p : ℕ→ℚ) (c : ℚ) : Prop :=
  SharedArcPivot.ProgressAt X F B H p c ∨ Breach X F

theorem blocks {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B H p c} (prior : ¬SharedArcPivot.ProgressAt X F B H p c) :
    ¬ProgressAt X F B H p c := by
  rintro (exit | ⟨w,r,wp,wm,wr,pc,pick,v,fail⟩)
  · exact prior exit
  · obtain ⟨K,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
      (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
    have sub : ∀ i∈X.V, ∀ j∈X.V, graph X.D F i j=true → X.D i j=true := by
      intro i _ j _ ed
      obtain ⟨_,hit⟩ := active.mp ed
      exact (mem_col.mp hit).2.2.2
    exact (StrictSubgraphInverse.row_budget hq inv sub (fun i => (pick i).val.1)
      (fun i => (pick i).val.2) (fun i => (pick i).property.2)
      (fun i => (pick i).property.1) wp wm wr pc v).not_gt fail

#print axioms blocks
end LeanCH.BR.Closure.SharedArcFlatBudget
