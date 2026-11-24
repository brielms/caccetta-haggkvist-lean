import checkpoints.shen_extension.RemoteHeadRectangle

namespace LeanCH.BR.RankedLiveSources
open Finset BRq2 BRq3 WeightedSD Closure

/-- The ordinary source records regularity with the library's OutEq predicate. -/
@[aesop safe forward (immediate := [hq,regular]) (rule_sets := [CHGraphFamilies])]
theorem counted_window {q r D V} (hq : 2≤q) (regular : OutEq r D V) :
    RankedUnitWindow.WindowLaw q r D V := RankedUnitWindow.register hq regular

/-- When all the missed labels are used, the covering row sits in the last
    reached layer of this same head set. -/
@[aesop safe forward (immediate := [hq,law,hs,width]) (rule_sets := [CHGraphFamilies])]
theorem last_layer {q r} {X : ShenMinimumOrder.Source q r} (hq : 2≤q)
    (law : RemoteHeadRectangle.Law X) {H : Finset ℕ} (hs : H⊆X.V)
    (width : q*(r-H.card)+2≤(X.V\BRsub.ballSet X.D X.V H (q-1)).card) :
    ∃i∈BRsub.ballSet X.D X.V H (q-1)\BRsub.ballSet X.D X.V H (q-2),
      (outN X.D X.V i).card=r ∧ X.V\BRsub.ballSet X.D X.V H (q-1)⊆outN X.D X.V i := by
  classical
  let W := X.V\BRsub.ballSet X.D X.V H (q-1)
  change q*(r-H.card)+2≤W.card at width
  have remote (h) (hh : h∈H) : Disjoint (ball X.D X.V h (q-1)) W :=
    disjoint_left.mpr (fun j hit cut=>(mem_sdiff.mp cut).2 (BRsub.mem_ballSet.mpr ⟨h,hh,hit⟩))
  obtain ⟨i,iw,tight,cover⟩ := RemoteHeadRectangle.marked_parent (W:=W) law sdiff_subset hs remote width
  obtain ⟨iv,off⟩ := mem_sdiff.mp iw
  have seen : i∈BRsub.ballSet X.D X.V H (q-1) := by
    by_contra no
    exact off (mem_sdiff.mpr ⟨iv,no⟩)
  obtain ⟨j,jw⟩ := card_pos.mp (show 0<W.card by omega)
  have missed : j∉BRsub.ballSet X.D X.V H (q-1) := (mem_sdiff.mp jw).2
  have near : i∉BRsub.ballSet X.D X.V H (q-2) := by
    intro early
    obtain ⟨h,hh,inside⟩ := BRsub.mem_ballSet.mp early
    obtain ⟨jv,ij⟩ := mem_outN.mp (cover jw)
    exact missed (BRsub.mem_ballSet.mpr ⟨h,hh,by simpa only [show q-2+1=q-1 by omega] using ball_step inside jv ij⟩)
  exact ⟨i,mem_sdiff.mpr ⟨seen,near⟩,tight,cover⟩

ch_family_split_result last_layer

#print axioms counted_window
#print axioms last_layer
end LeanCH.BR.RankedLiveSources
