import checkpoints.shen_extension.SharedArcPivotGate
import LeanCH.BR.BRWeightedFoldBoundary

namespace LeanCH.BR.Closure.SharedArcPivotFold
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights SharedArcBarrier SharedArcComponentExchange
open FirstPacketBarrier MarkedCyclePeeling

/-- Every nonempty bank of fresh heads has a supplier outside the bank
which misses the chosen fresh parent. The same puncture weights work for
all choices and give a strict bound on its reachable out-neighbours. -/
theorem bank_escape {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    let U := X.V.erase a.val
    ∃ w : ℕ→ℚ, (∀i∈U,0<w i) ∧ mass U w=1 ∧ (∀i∈U,WeightedSD.row q X.D U w i=1) ∧
    ∀ (t : X.V), Fresh X F (t,a) → ∀H : Finset ℕ,H.Nonempty → (∀h∈H,Fresh X F (a,h)) →
      mass H w<q*mass (foldBank q X.D U H t) w ∧
      ∃y∈U \ H,X.D y t=false ∧ (∃h∈H,X.D y h=true) ∧
        ((∀x∈U,X.D t x=true → X.D a x=true) → X.D y a=false) := by
  classical
  intro U
  obtain ⟨_,sat,_,w,pos,wm,rows⟩ := (SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no
  refine ⟨w,pos,wm,rows,?_⟩
  intro t ta H live heads
  have ne {i j : ℕ} (jv : j∈X.V) (ed : X.D i j=true) : i≠j :=
    fun eq => loopfree X.free (by omega) jv (eq ▸ ed)
  have tu : t.val∈U := mem_erase.mpr ⟨ne a.property ta.2.2.1,t.property⟩
  have hs : H⊆U := fun h hh => mem_erase.mpr ⟨(ne (heads h hh).2.1 (heads h hh).2.2.1).symm,(heads h hh).2.1⟩
  have notH : t.val∉H := fun tt => X.free a 2 (by decide) hq
    (.step t.property (heads t tt).2.2.1 (.step a.property ta.2.2.1 (.refl _)))
  have retained : t.val∈U \ H := mem_sdiff.mpr ⟨tu,notH⟩
  have free := X.free.mono_set (erase_subset a.val X.V)
  have ss : SmallerSmallRow q U.card := fun D V lt hf => small D V (lt.trans (card_erase_lt_of_mem a.property)) hf
  have price := fold_bank_strict_of_positive_retained hq free ss hs retained
    (fun h hh => Bool.eq_false_iff.mp (SharedArcPivotChoice.stopped_rectangle X hq small step least stop multi edge no ta
      (h:=⟨h,(heads h hh).2.1⟩) (heads h hh)).1) w
    (fun i ui => (pos i ui).le) (fun i ui => pos i (mem_sdiff.mp ui).1)
    (sum_pos (fun i hi => pos i (hs hi)) live) (fun i ui => (wm.trans (rows i ui).symm).le)
  refine ⟨price,?_⟩
  have supplier : ∃y∈U \ H,X.D y t=false ∧ ∃h∈H,X.D y h=true := by
    by_contra noSupplier
    have empty := foldBank_empty_of_parents_head_receiver (by omega : 1≤q) free retained (fun y yu hit => by
      cases ed : X.D y t
      · exact (noSupplier ⟨y,yu,ed,hit⟩).elim
      · rfl)
    rw [empty] at price
    have positive : 0<mass H w := sum_pos (fun i hi => pos i (hs hi)) live
    simp [mass] at price
    exact (not_lt_of_ge positive.le) price
  obtain ⟨y,yu,yt,h,hh,yh⟩ := supplier
  refine ⟨y,yu,yt,⟨h,hh,yh⟩,?_⟩
  intro clean
  apply Bool.eq_false_iff.mpr
  intro ya
  have diff : t.val≠y := by
    intro eq
    have absent := (SharedArcPivotChoice.stopped_rectangle X hq small step least stop multi edge no ta
      (h:=⟨h,(heads h hh).2.1⟩) (heads h hh)).1
    exact Bool.noConfusion (absent.symm.trans (eq ▸ yh))
  have yes := SharedArcPivotGate.forced_parent X.free sat a.property tu (mem_sdiff.mp yu).1 diff ya clean (by omega)
  exact Bool.noConfusion (yt.symm.trans yes)

#print axioms bank_escape

/-- Every nonempty reverse rectangle leaves an actual unpaid row at the
original positive unit weights, even when many new arcs are installed. -/
theorem original_payment_fails {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    let U := X.V.erase a.val
    ∀w : ℕ→ℚ,(∀i∈U,0<w i) → (∀i∈U,WeightedSD.row q X.D U w i=mass U w) →
    ∀T H : Finset ℕ,T.Nonempty → H.Nonempty → (∀t∈T,Fresh X F (t,a)) → (∀h∈H,Fresh X F (a,h)) →
      ∃i∈U,i∉H ∧ WeightedSD.row q (SharedArcPivotGate.edit X.D a T H) U w i<mass U w := by
  classical
  intro U w pos rows
  obtain ⟨_,_,_,_,supply⟩ := bank_escape X hq small step least stop multi edge no
  intro T H live bank parents heads
  obtain ⟨t,tt⟩ := live
  have ta := parents t tt
  have tin : t∈U := mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) a.property (by simpa [eq] using ta.2.2.1),ta.1⟩
  have th : t∉H := fun hh => X.free a 2 (by decide) hq (.step ta.1 (heads t hh).2.2.1 (.step a.property ta.2.2.1 (.refl _)))
  let E := SharedArcPivotGate.edit X.D a T H
  have loss : ∃i∈U,i∉H ∧ ∃j∈U,X.D i j=true ∧ E i j=false := by
    by_cases clean : ∀x∈U,X.D t x=true → X.D a x=true
    · obtain ⟨_,y,yu,_,⟨h,hh,yh⟩,outside⟩ := supply ⟨t,ta.1⟩ ta H bank heads
      obtain ⟨yi,yh'⟩ := mem_sdiff.mp yu
      have hu : h∈U := mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) a.property
        (by simpa [eq] using (heads h hh).2.2.1),(heads h hh).2.1⟩
      exact ⟨y,yi,yh',h,hu,yh,by simp [E,SharedArcPivotGate.edit,SharedArcPivotGate.cutMany,yh',hh,outside clean]⟩
    · push Not at clean
      obtain ⟨x,xu,tx,ax⟩ := clean
      exact ⟨t,tin,th,x,xu,tx,by simp [E,SharedArcPivotGate.edit,SharedArcPivotGate.cutMany,tt,th,ax]⟩
  obtain ⟨i,ui,ih,j,ju,ij,off⟩ := loss
  have sub {k} (ed : E i k=true) : X.D i k=true := by
    simp [E,SharedArcPivotGate.edit,SharedArcPivotGate.cutMany,ih] at ed
    tauto
  have drop : outW E U w i<outW X.D U w i := by
    apply sum_lt_sum
    · intro k ku
      by_cases ed : E i k=true
      · simp [ed,sub ed]
      · by_cases native : X.D i k=true <;> simp [ed,native,(pos k ku).le]
    · exact ⟨j,ju,by simp [off,ij,pos j ju]⟩
  refine ⟨i,ui,ih,?_⟩
  rw [←rows i ui]
  exact add_lt_add_right (mul_lt_mul_of_pos_left drop (by exact_mod_cast (show 0<q by omega))) _

#print axioms original_payment_fails
end LeanCH.BR.Closure.SharedArcPivotFold
