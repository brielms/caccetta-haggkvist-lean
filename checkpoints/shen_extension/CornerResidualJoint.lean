import checkpoints.shen_extension.TwoReceiverIntersection
import checkpoints.shen_extension.SingleArcResidualSource

namespace LeanCH.BR.Closure.CornerResidualJoint
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SingleArcResidualSource

/-- Both alternatives feed the actual exterior supplier d in the old
    table. If its final two native arcs are also old, the old heir has
    at least q−2 steps left before reaching d. -/
def Feed (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (a c d : ℕ) : Prop :=
  let R := nonParentSet E V a
  let A := ancestors E V a d
  (∃v∈A,E a v=true ∧ (∀i∈V,i≠a → E i v=true → E i a=true) ∧
    ∃l,Walk E R v d l ∧ (E d c=true → E c a=true → q-2≤l)) ∨
  ∃v∈A,∃m,q+1≤m ∧ m≤A.card ∧ Walk E A v v m ∧ ∃l,Walk E R v d l

private theorem old_feed {q E V a c d} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {w p : ℕ→ℚ} (pos : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1) (pm : mass V p=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1)
    (av : a∈V) (cv : c∈V) (dv : d∈V) (ne : d≠a) (off : E d a=false) : Feed q E V a c d := by
  classical
  let R := nonParentSet E V a
  let A := ancestors E V a d
  have sub : A⊆R := filter_subset _ _
  have dr : d∈R := mem_nonParentSet.mpr ⟨dv,ne,Bool.eq_false_iff.mp off⟩
  have live : A.Nonempty := ⟨d,mem_filter.mpr ⟨dr,0,.refl _⟩⟩
  have closed (x) (xa : x∈A) (y) (yr : y∈R) (yx : E y x=true) : y∈A := by
    obtain ⟨xr,l,path⟩ := mem_filter.mp xa
    exact mem_filter.mpr ⟨yr,l+1,.step xr yx path⟩
  rcases heir_or_walk hq free small pos wm pm wr pc av sub live closed with
    ⟨v,va,head,par⟩|⟨v,va,m,lo,hi,loop⟩
  · obtain ⟨l,path⟩ := (mem_filter.mp va).2
    refine Or.inl ⟨v,va,head,par,l,path,?_⟩
    intro dc ca
    have vv := (mem_nonParentSet.mp (sub va)).1
    have tail := path.mono (fun _ ir => (mem_nonParentSet.mp ir).1)
    by_contra short
    exact free a (l+1+1+1) (by omega) (by omega) (.step vv head ((tail.snoc cv dc).snoc av ca))
  · exact Or.inr ⟨v,va,m,lo,hi,loop,(mem_filter.mp va).2⟩

/-- Common-label joint of the parent recursion on the native model and
    the residual-ancestor dichotomy on an old flat spanning table. -/
theorem joint {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    {a b₀ c₀ : X.V} (ba : X.D b₀ a=true) (ca : X.D c₀ a=true) (cb : X.D c₀ b₀=true) :
    let P := inN X.D X.V a
    ∃c∈P,∃b∈P,X.D c b=true ∧ ((c=c₀.val ∧ b=b₀.val) ∨ ∃l,Walk X.D P b c₀ l) ∧
      ∃d∈X.V,X.D d c=true ∧ X.D d b=false ∧ X.D d a=false ∧
      Walk X.D ((X.V.erase a.val)\inN X.D (X.V.erase a.val) a) a d (q-1) ∧
      Feed q (graph X.D F) X.V a c d := by
  intro P
  obtain ⟨c,cp,b,bp,ed,trail,d,dv,dc,db,da,path⟩ :=
    TwoReceiverIntersection.upstream_corridor X hq (a:=a) (b₀:=b₀) (c₀:=c₀) ba ca cb
  have incl {i j} (e : graph X.D F i j=true) : X.D i j=true := by
    obtain ⟨_,hit⟩ := active.mp e
    exact (mem_col.mp hit).2.2.2
  obtain ⟨cv,cta⟩ := mem_inN.mp cp
  have ne : d≠a.val := fun eq => X.free a 2 (by decide) hq
    (.step cv (eq ▸ dc) (.step a.property cta (.refl _)))
  exact ⟨c,cp,b,bp,ed,trail,d,dv,dc,db,da,path,
    old_feed hq (qfree_sub (fun _ _ e => incl e) X.free) small pos wm (HeirExit.mass_col_of_flat wm wr pc)
      wr pc a.property cv dv ne (Bool.eq_false_iff.mpr (fun e => Bool.noConfusion (da.symm.trans (incl e))))⟩

open SharedArcBarrier SharedArcComponentExchange

/-- At the original stopped pivot the whole return corridor is already
    old. Its two closing arcs are either both old, or precisely the two
    fresh arcs at that pivot. This applies to the same c and d as Feed. -/
theorem stopped_arc_types {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {y a : X.V} (edge : Fresh X F (y,a))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y a) X.V)
    {c d : X.V} (dc : X.D d c=true) (ca : X.D c a=true) (da : X.D d a=false)
    (path : Walk X.D ((X.V.erase a.val)\inN X.D (X.V.erase a.val) a) a d (q-1)) :
    Walk (graph X.D F) ((X.V.erase a.val)\inN X.D (X.V.erase a.val) a) a d (q-1) ∧
      ((c≠y ∧ graph X.D F d c=true ∧ graph X.D F c a=true) ∨
       (c=y ∧ Fresh X F (d,y) ∧ Fresh X F (y,a))) := by
  have center := ((SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no).2.2.1
  have ay : a≠y := fun eq => loopfree X.free (by omega) y.property (eq ▸ edge.2.2.1)
  have dy : d≠y := fun eq => Bool.noConfusion (da.symm.trans (eq ▸ edge.2.2.1))
  have kept {i j : X.V} (iy : i≠y) (jy : j≠y) (old : X.D i j=true) : graph X.D F i j=true := by
    cases e : graph X.D F i j
    · rcases center ⟨(i,j),old,e⟩ with hit|hit
      · exact (iy hit).elim
      · exact (jy hit).elim
    · rfl
  let R := (X.V.erase a.val)\inN X.D (X.V.erase a.val) a
  have safe {i} (ir : i∈R) : i≠y.val := by
    intro eq
    obtain ⟨iu,off⟩ := mem_sdiff.mp ir
    exact off (mem_inN.mpr ⟨iu,eq ▸ edge.2.2.1⟩)
  have lift {i j k} (p : Walk X.D R i j k) (iv : i∈X.V) (iy : i≠y.val) : Walk (graph X.D F) R i j k := by
    induction p with
    | refl => exact .refl _
    | @step u v _ _ vr uv _ ih =>
      have vv := mem_of_mem_erase (mem_sdiff.mp vr).1
      exact .step vr (kept (i:=⟨u,iv⟩) (j:=⟨v,vv⟩) (fun eq => iy (congrArg Subtype.val eq))
        (fun eq => safe vr (congrArg Subtype.val eq)) uv) (ih vv (safe vr))
  refine ⟨lift path a.property (fun eq => ay (Subtype.ext eq)),?_⟩
  by_cases cy : c=y
  · subst c
    have old := SharedArcPivot.classify_parents X hq small step least multi edge no d dc
    exact Or.inr ⟨rfl,⟨d.property,y.property,dc,
      Bool.eq_false_iff.mpr (fun ed => Bool.noConfusion (da.symm.trans (old.mp ed)))⟩,edge⟩
  · exact Or.inl ⟨cy,kept dy cy dc,kept cy ay ca⟩

#print axioms stopped_arc_types
#print axioms joint
end LeanCH.BR.Closure.CornerResidualJoint
