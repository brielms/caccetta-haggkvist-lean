import checkpoints.shen_extension.SharedArcPivot

namespace LeanCH.BR.Closure.SharedArcPivotPaths
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcBarrier SharedArcComponentExchange

/-- In a stopped pivot, each old parent points to every fresh head and
each fresh parent points to every old head. The tested head need not be
the head of either of the two arcs under comparison. -/
theorem crossed {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (tested : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    (t c : X.V) (ta : X.D t a=true) (ac : X.D a c=true)
    (mixed : graph X.D F t a ≠ graph X.D F a c) : X.D t c=true := by
  classical
  let E := graph X.D F
  let U := X.V.erase a.val
  obtain ⟨_,sat,center,_⟩ :=
    (SharedArcPivot.alternatives X hq small step least multi tested).resolve_left no
  have tu : t.val∈U := mem_erase.mpr ⟨by
    intro e
    exact loopfree X.free (by omega) a.property (by simpa [e] using ta),t.property⟩
  have cu : c.val∈U := mem_erase.mpr ⟨by
    intro e
    exact loopfree X.free (by omega) a.property (by simpa [e] using ac),c.property⟩
  by_contra miss
  obtain ⟨_,k,bound,path⟩ := mem_ball.mp (sat _ cu _ tu miss)
  have star {i j} (tail : ℕ) (ed : E i j=true) :
      SharedArcCover.onStars X.D E {tail} ∅ i j=true := by
    obtain ⟨C,m⟩ := active.mp ed
    simp [SharedArcCover.onStars,ed,(mem_col.mp m).2.2.2]
  have lift {i j k} (tail : ℕ) (p : Walk X.D U i j k) (hi : i∈U) :
      Walk (SharedArcCover.onStars X.D E {tail} ∅) X.V i j k := by
    induction p with
    | refl => exact .refl _
    | @step i j _ _ hj ij _ ih =>
      apply Walk.step (mem_of_mem_erase hj) (star tail ?_) (ih hj)
      by_contra off
      let f : SharedArcFlatCut.Missing X F :=
        ⟨(⟨i,mem_of_mem_erase hi⟩,⟨j,mem_of_mem_erase hj⟩),ij,Bool.eq_false_iff.mpr off⟩
      rcases center f with h|h
      · exact (mem_erase.mp hi).1 (congrArg Subtype.val h)
      · exact (mem_erase.mp hj).1 (congrArg Subtype.val h)
  by_cases old : E t a=true
  · have off : E a c=false := Bool.eq_false_iff.mpr (fun yes => mixed (old.trans yes.symm))
    have fresh : Fresh X F (a,c) := ⟨a.property,c.property,ac,off⟩
    apply SharedArcCover.no_return X hq step least {a.val} ∅ (by simpa using multi) fresh (by simp)
    exact mem_ball.mpr ⟨a.property,_,by omega,(lift a path cu).snoc a.property (star a old)⟩
  · have off := Bool.eq_false_iff.mpr old
    have yes : E a c=true := by
      by_contra h
      exact mixed (off.trans (Bool.eq_false_iff.mpr h).symm)
    have fresh : Fresh X F (t,a) := ⟨t.property,a.property,ta,off⟩
    apply SharedArcCover.no_return X hq step least {t.val} ∅ (by simpa using multi) fresh (by simp)
    exact mem_ball.mpr ⟨t.property,k+1,by omega,.step c.property (star t yes) (lift t path cu)⟩

/-- A transfer between two split returns pays at least one step beyond the
phase difference. No assumption about where the transfer travels is needed. -/
theorem transfer_length {D V q} (free : QFree D V q) {c t x y i j k l}
    (cv : c∈V) (cross : D t c=true)
    (firstLeg : Walk D V c x i) (transfer : Walk D V x y k)
    (suffix : Walk D V y t l) (len : j + 1 + l = q) : j + 1 ≤ i + k := by
  by_contra! short
  exact free c (i + k + l + 1) (by omega) (by omega)
    (((firstLeg.append transfer).append suffix).snoc cv cross)

/-- When both cross arcs exist, two shortest returns cannot meet even
at different positions. A meeting would force both strict phase orders. -/
theorem separate {D V q} (free : QFree D V q) {c b t u x y i j l m}
    (cv : c∈V) (bv : b∈V) (uc : D u c=true) (tb : D t b=true)
    (cp : Walk D V c x i) (xt : Walk D V x t l) (bp : Walk D V b y j)
    (yu : Walk D V y u m) (one : i+1+l=q) (two : j+1+m=q) : x≠y := by
  rintro rfl
  have left := transfer_length free cv uc cp (.refl _) yu two
  have right := transfer_length free bv tb bp (.refl _) xt one
  omega

/-- A meeting on two native shortest returns forces strict separation
of the tested edit, for every cutoff and every support size. -/
theorem strict_of_meeting {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (tested : Fresh X F (a,b))
    {c h t u : X.V} (ta : X.D t a=true) (ac : X.D a c=true)
    (ua : X.D u a=true) (ah : X.D a h=true)
    (mix₁ : graph X.D F u a ≠ graph X.D F a c)
    (mix₂ : graph X.D F t a ≠ graph X.D F a h)
    {x i j l m} (cp : Walk X.D X.V c x i) (xt : Walk X.D X.V x t l)
    (hp : Walk X.D X.V h x j) (xu : Walk X.D X.V x u m)
    (one : i+1+l=q) (two : j+1+m=q) :
    SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V := by
  by_contra no
  have cross := crossed X hq small step least multi tested no
  exact separate X.free c.property h.property (cross u c ua ac mix₁)
    (cross t h ta ah mix₂) cp xt hp xu one two rfl

#print axioms crossed
#print axioms transfer_length
#print axioms separate
#print axioms strict_of_meeting

/-- Two heads of the same root are linked if some shortest cycle through
each head visits the same vertex between its head and its last parent. -/
def Link {q n} (X : Model q n) (a c h : X.V) : Prop :=
  X.D a c=true ∧ X.D a h=true ∧ ∃ (t u : X.V) (x i j l m : ℕ),
    X.D t a=true ∧ X.D u a=true ∧
    Walk X.D X.V c x i ∧ Walk X.D X.V x t l ∧
    Walk X.D X.V h x j ∧ Walk X.D X.V x u m ∧ i+1+l=q ∧ j+1+m=q

/-- Along arbitrarily many overlapping shortest returns, old/fresh status
is constant whenever the one-arc test fails. -/
theorem constant_on_chains {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (tested : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {c h} (chain : Relation.ReflTransGen (Link X a) c h) : graph X.D F a c = graph X.D F a h := by
  have cross := crossed X hq small step least multi tested no
  have same {v t : X.V} (tv : X.D t a=true) (av : X.D a v=true)
      {x i l} (p : Walk X.D X.V v x i) (r : Walk X.D X.V x t l) (len : i+1+l=q) :
      graph X.D F t a = graph X.D F a v := by
    by_contra diff
    exact X.free v (i+l+1) (by omega) (by omega) ((p.append r).snoc v.property (cross t v tv av diff))
  induction chain with
  | refl => rfl
  | @tail v w _ link ih =>
    apply ih.trans
    obtain ⟨av,aw,t,u,x,i,j,l,m,ta,ua,p,r,p',r',one,two⟩ := link
    by_contra diff
    have first := same ta av p r one
    have second := same ua aw p' r' two
    exact no (strict_of_meeting X hq small step least multi tested ta av ua aw
      (by rw [second]; exact Ne.symm diff) (by rw [first]; exact diff) p r p' r' one two)

/-- A path from the tested fresh head to any old head pays the strict
one-arc test, independently of the number of returns used in the path. -/
theorem strict_of_chain {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (tested : Fresh X F (a,b))
    {h : X.V} (old : graph X.D F a h=true) (chain : Relation.ReflTransGen (Link X a) b h) :
    SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V := by
  by_contra no
  have same := constant_on_chains X hq small step least multi tested no chain
  rw [tested.2.2.2,old] at same
  contradiction

#print axioms constant_on_chains
#print axioms strict_of_chain

/-- The selected spanning family supplies an actual old head. Thus a failed
test requires a disconnected native link at its tail. -/
theorem disconnected {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (sub : F⊆family X) (spans : SharedArcExpansion.support F=X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (tested : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃h : X.V,X.D a h=true ∧ graph X.D F a h=true ∧ ¬Relation.ReflTransGen (Link X a) b h := by
  classical
  have ha : a.val∈SharedArcExpansion.support F := by rw [spans]; exact a.property
  obtain ⟨C,cf,ac⟩ := mem_biUnion.mp ha
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q C := (mem_filter.mp (sub cf)).2
  obtain ⟨h,hh⟩ := card_pos.mp (show 0<(outN X.D C a).card by rw [cyc.heads a ac]; decide)
  obtain ⟨hc,ed⟩ := mem_outN.mp hh
  have old : graph X.D F a h=true := active.mpr ⟨C,mem_col.mpr ⟨cf,ac,hc,ed⟩⟩
  exact ⟨⟨h,cyc.sub hc⟩,ed,old,fun chain =>
    no (strict_of_chain X hq small step least multi tested (h:=⟨h,cyc.sub hc⟩) old chain)⟩

#print axioms disconnected

end LeanCH.BR.Closure.SharedArcPivotPaths
