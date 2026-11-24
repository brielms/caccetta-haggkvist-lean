import checkpoints.shen_extension.CycleClassFrontier

namespace LeanCH.BR.Closure.ClassParentBanks
open Finset BRq2 BRq3 BR45 DeficitLevels ShortestCycleClasses ShenMinimumOrder

theorem class_eq {D V q x y} (mem : y∈carrier D V q x) :
    carrier D V q x=carrier D V q y := by
  classical
  have rel := (mem_filter.mp mem).2
  ext a
  simp only [carrier,mem_filter]
  exact and_congr_right (fun _ => ⟨fun path => .trans _ _ _ (.symm _ _ rel) path,
    fun path => .trans _ _ _ rel path⟩)

theorem parent {q s} (X : Source q s) (hq : 2≤q) (hs : 0<s) {v} (hv : v∈X.V) :
    ∃p∈carrier X.D X.V q v, X.D p v=true ∧ (outN X.D X.V p).card=s ∧
      outN X.D X.V v \ carrier X.D X.V q v ⊆ outN X.D X.V p := by
  classical
  obtain ⟨p,pv,pedge,pt,live,returns⟩ := ShenCycleSuccessor.fixed_parent X hq hs hv
  have joint (w) (hw : w∈outN X.D X.V v \ outN X.D X.V p) :=
    ShenCycleSuccessor.marked_cycle hq X.free hv (outN_subset (mem_sdiff.mp hw).1)
      pedge (mem_outN.mp (mem_sdiff.mp hw).1).2 (returns w hw)
  obtain ⟨w,hw⟩ := live
  obtain ⟨M,c,pm,vm,_⟩ := joint w hw
  refine ⟨p,mem_filter.mpr ⟨pv,.rel _ _ ⟨M,c.sub,c.size,c.heads,vm,pm⟩⟩,pedge,pt,?_⟩
  intro a ha
  by_contra miss
  obtain ⟨N,b,_,vn,an⟩ := joint a (mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,miss⟩)
  exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨b.sub an,.rel _ _ ⟨N,b.sub,b.size,b.heads,vn,an⟩⟩)

structure Bank (D : CH.Digraph) (V : Finset ℕ) (q s v : ℕ) (H P : Finset ℕ) : Prop where
  inside : P ⊆ carrier D V q v
  size : q+1 ≤ P.card
  tight : ∀p∈P,(outN D V p).card=s
  covers : ∀p∈P,H⊆outN D V p
  returns : ∀p∈P, ∃a∈P,D a p=true

/-- Following parents preserves the entire prescribed exterior head set. -/
theorem bank {q s} (X : Source q s) (hq : 2≤q) (hs : 0<s) {v} (hv : v∈X.V)
    {H} (extH : H ⊆ outN X.D X.V v \ carrier X.D X.V q v) :
    ∃P, Bank X.D X.V q s v H P := by
  classical
  let C := carrier X.D X.V q v
  let P := C.filter (fun p => (outN X.D X.V p).card=s ∧ H⊆outN X.D X.V p)
  have pv : P⊆X.V := (filter_subset _ _).trans (filter_subset _ _)
  obtain ⟨p,pc,_,pt,cover⟩ := parent X hq hs hv
  have live : P.Nonempty := ⟨p,mem_filter.mpr ⟨pc,pt,extH.trans cover⟩⟩
  have returns (a) (ap : a∈P) : ∃b∈P,X.D b a=true := by
    obtain ⟨ac,_,ha⟩ := mem_filter.mp ap
    obtain ⟨b,bc,ba,bt,bh⟩ := parent X hq hs (pv ap)
    have eq := class_eq ac
    rw [←eq] at bc bh
    exact ⟨b,mem_filter.mpr ⟨bc,bt,fun z hz => bh (mem_sdiff.mpr
      ⟨ha hz,(mem_sdiff.mp (extH hz)).2⟩)⟩,ba⟩
  have deg (a) (ha : a∈P) : 1≤(outN (fun x y => X.D y x) P a).card := by
    obtain ⟨b,bp,ba⟩ := returns a ha
    exact card_pos.mpr ⟨b,mem_outN.mpr ⟨bp,ba⟩⟩
  have size := dt_size (by omega : 1≤q) (ball_q_one q (by omega)) (X.free.reverse.mono_set pv) deg live
  exact ⟨P,filter_subset _ _,by simpa using size,fun _ h => (mem_filter.mp h).2.1,
    fun _ h => (mem_filter.mp h).2.2,returns⟩

/-- A crossing arc cannot return even in exactly q steps. -/
theorem far {D V q x y k} (hq : 2≤q) (free : QFree D V q) (yv : y∈V)
    (xy : D x y=true) (extY : y∉carrier D V q x) (path : Walk D V y x k) : q<k := by
  classical
  by_contra! le
  have eq : k=q := by
    by_contra ne
    exact free x (k+1) (by omega) (by omega) (.step yv xy path)
  cases path with
  | refl => omega
  | step wv yw tail =>
    have ret := DeleteRepair.head_avoided free yv xy tail (by omega)
    obtain ⟨M,c,xm,ym,_⟩ := ShenCycleSuccessor.marked_cycle hq free yv wv xy yw
      (by convert ret using 1; omega)
    exact extY (mem_filter.mpr ⟨yv,.rel _ _ ⟨M,c.sub,c.size,c.heads,xm,ym⟩⟩)

#print axioms bank
#print axioms far
end LeanCH.BR.Closure.ClassParentBanks
