import checkpoints.shen_extension.SharedArcPivotLoopSums

namespace LeanCH.BR.Closure.SharedArcPivotChoice
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open SharedArcBarrier SharedArcComponentExchange FirstPacketBarrier MarkedCyclePeeling
open scoped Matrix

def pair (a t c : ℕ) : Finset SharedArcComponentExchange.Arc := {(t,a),(a,c)}

private theorem tail_ne {q n} (X : Model q n) (hq : 2≤q) {F} {x y : X.V}
    (edge : Fresh X F (x,y)) : x.val≠y.val := by
  intro h
  exact loopfree X.free (by omega) y.property (by simpa [h] using edge.2.2.1)

/-- Every actual boundary at a centered multiple-head minimum adds exactly
one incoming and one outgoing arc at the center. -/
theorem boundary_pair {q n} (X : Model q n) {F M} (bm : Boundary X F M)
    (enough : 1<(targets X.D X.V F M).card) (a : X.V)
    (center : ∀f : SharedArcFlatCut.Missing X F,f.val.1=a ∨ f.val.2=a) :
    ∃t c : X.V,Fresh X F (t,a) ∧ Fresh X F (a,c) ∧ added X.D F M=pair a t c := by
  classical
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  let P := added X.D F M
  have many : 1<P.card := (count cyc).symm ▸ enough
  have touch {e : SharedArcComponentExchange.Arc} (hit : e∈P) : e.1=a.val ∨ e.2=a.val := by
    obtain ⟨i,j,ed,off⟩ := mem_added.mp hit
    let f : SharedArcFlatCut.Missing X F := ⟨(⟨e.1,cyc.sub i⟩,⟨e.2,cyc.sub j⟩),ed,off⟩
    exact (center f).imp (congrArg Subtype.val) (congrArg Subtype.val)
  have both (left : Bool) : ∃e∈P,(if left then e.1 else e.2)=a.val := by
    by_contra! no
    apply many.not_ge
    apply card_le_one.mpr
    intro e he f hf
    cases left with
    | true => exact matching cyc he hf (Or.inr (((touch he).resolve_left (no e he)).trans
        ((touch hf).resolve_left (no f hf)).symm))
    | false => exact matching cyc he hf (Or.inl (((touch he).resolve_right (no e he)).trans
        ((touch hf).resolve_right (no f hf)).symm))
  obtain ⟨⟨t,u⟩,hin,hu⟩ := both false
  obtain ⟨⟨v,c⟩,hout,hv⟩ := both true
  change u=a.val at hu; change v=a.val at hv
  subst u; subst v
  obtain ⟨tm,_,ta,offT⟩ := mem_added.mp hin
  obtain ⟨_,cm,ac,offC⟩ := mem_added.mp hout
  refine ⟨⟨t,cyc.sub tm⟩,⟨c,cyc.sub cm⟩,⟨cyc.sub tm,a.property,ta,offT⟩,
    ⟨a.property,cyc.sub cm,ac,offC⟩,?_⟩
  ext e
  constructor
  · intro he
    rcases touch he with h|h
    · exact mem_insert_of_mem (mem_singleton.mpr (matching cyc he hout (Or.inl h)))
    · exact mem_insert.mpr (Or.inl (matching cyc he hin (Or.inr h)))
  · intro he
    rcases mem_insert.mp he with rfl|hc
    · exact hin
    · exact mem_singleton.mp hc ▸ hout

def outCost {V : Type*} [Fintype V] (R S H : Matrix V V ℝ) (a : V) :=
  ∑j,(R a j-S a j)*H j a

def inCost {V : Type*} [Fintype V] (R S H : Matrix V V ℝ) (a : V) :=
  ∑i,H a i*(R i a-S i a)

/-- Keeping one pair subtracts exactly its two endpoint entries from
the two old bills. The inverse used for all comparisons is fixed. -/
theorem costs {q n} (X : Model q n) (hq : 2≤q) {F M} {a t c : X.V}
    (ta : Fresh X F (t,a)) (ac : Fresh X F (a,c)) (p : added X.D F M=pair a t c)
    (H : Matrix X.V X.V ℝ) :
    let R := realMatrix q X.D X.V
    let S := realMatrix q (graph X.D F) X.V
    let J := realMatrix q (graph X.D (insert M F)) X.V
    outCost R J H a=outCost R S H a-q*H c a ∧ inCost R J H a=inCost R S H a-q*H a t := by
  classical
  intro R S J
  have delta (i j : X.V) : J i j-S i j = if (i.val,j.val)∈pair a t c then (q:ℝ) else 0 := by
    rw [←p]
    change realMatrix q _ _ i j-realMatrix q _ _ i j=_
    rw [realMatrix_added_difference (fun _ _ _ _ e => union_arc.mpr (Or.inl e))]
    by_cases hit : (i.val,j.val)∈added X.D F M
    · have off := (mem_added.mp hit).2.2.2
      simp [hit,off,union_arc.mpr (Or.inr hit)]
    · have iff := union_arc (D:=X.D) (F:=F) (B:=M) (i:=i.val) (j:=j.val)
      simp only [hit,or_false] at iff
      simp only [hit,ite_false,iff,and_not_self]
  have outgoing (j : X.V) : J a j-S a j=if j=c then q else 0 := by
    rw [delta]; by_cases h : j=c
    · simp [h,pair]
    · simp [pair,Ne.symm (tail_ne X hq ta),show j.val≠c.val from fun e => h (Subtype.ext e),h]
  have incoming (i : X.V) : J i a-S i a=if i=t then q else 0 := by
    rw [delta]; by_cases h : i=t
    · simp [h,pair]
    · simp [pair,tail_ne X hq ac,show i.val≠t.val from fun e => h (Subtype.ext e),h]
  constructor
  · have e : outCost R S H a-outCost R J H a=(q:ℝ)*H c a := by
      unfold outCost
      rw [←sum_sub_distrib]
      calc
        _ = ∑j,(J a j-S a j)*H j a := sum_congr rfl fun _ _ => by ring
        _ = _ := by simp_rw [outgoing]; simp [ite_mul]
    linarith
  · have e : inCost R S H a-inCost R J H a=(q:ℝ)*H a t := by
      unfold inCost
      rw [←sum_sub_distrib]
      calc
        _ = ∑i,H a i*(J i a-S i a) := sum_congr rfl fun _ _ => by ring
        _ = _ := by simp_rw [incoming]; simp [mul_ite,mul_comm]
    linarith

#print axioms boundary_pair
#print axioms costs

/-- Either endpoint of an actual pair can be prescribed by one exchange
from the initial strict boundary; no other boundary needs to be strict. -/
theorem singles {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) {a t c : X.V}
    (ta : Fresh X F (t,a)) (shape : added X.D F B=pair a t c) :
    (∀s : X.V,Fresh X F (s,a) → ∃M,Boundary X F M ∧ added X.D F M=pair a s c) ∧
    (∀h : X.V,Fresh X F (a,h) → ∃M,Boundary X F M ∧ added X.D F M=pair a t h) := by
  classical
  let i : SharedArcComponentExchange.Arc := (t.val,a.val)
  let o : SharedArcComponentExchange.Arc := (a.val,c.val)
  have ne : i≠o := fun eq => tail_ne X hq ta (congrArg Prod.fst eq)
  have tab : added X.D F B={i,o} := shape
  constructor
  · intro s fresh
    obtain ⟨M,bm,eq⟩ := exchange X hq small step least bad (e:=i) (tab ▸ mem_insert_self _ _) fresh (Or.inr rfl)
    exact ⟨M,bm,by rw [eq,tab]; simp [pair,i,o,ne]⟩
  · intro h fresh
    obtain ⟨M,bm,eq⟩ := exchange X hq small step least bad (e:=o)
      (tab ▸ mem_insert_of_mem (mem_singleton_self _)) fresh (Or.inl rfl)
    refine ⟨M,bm,?_⟩
    rw [eq,tab]
    change insert (a.val,h.val) (({i,o} : Finset SharedArcComponentExchange.Arc).erase o)={i,(a.val,h.val)}
    ext z
    simp only [mem_insert,mem_erase,mem_singleton]
    grind

/-- The optimum is specified by the two least native entries. The
equivalence keeps the existential graph-level winning boundary on the
left; each sufficient inequality is realized by a single actual exchange. -/
theorem minimum_test {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃ (H : Matrix X.V X.V ℝ) (s h : X.V),CommonInverse (realMatrix q X.D X.V) H ∧
      Fresh X F (s,a) ∧ Fresh X F (a,h) ∧
      (∀t : X.V,Fresh X F (t,a) → H a s≤H a t) ∧ (∀c : X.V,Fresh X F (a,c) → H h a≤H c a) ∧
      let R := realMatrix q X.D X.V
      let S := realMatrix q (graph X.D F) X.V
      ((∃M,Boundary X F M ∧ SharedArcCompression.winning X F B M) ↔
        1+(q:ℝ)*H h a ≤ outCost R S H a ∨ 1+(q:ℝ)*H a s ≤ inCost R S H a) := by
  classical
  obtain ⟨H,inv,test⟩ := SharedArcPivotLoopSums.all_competitors X hq small step least multi edge no
  have center := SharedArcPivot.single_center X hq small step least multi edge no
  obtain ⟨t,c,ta,ac,pairB⟩ := boundary_pair X step multi a center
  let I := univ.filter (fun j : X.V => Fresh X F (j,a))
  let O := univ.filter (fun j : X.V => Fresh X F (a,j))
  obtain ⟨s,si,sm⟩ := I.exists_min_image (fun j => H a j) ⟨t,mem_filter.mpr ⟨mem_univ _,ta⟩⟩
  obtain ⟨h,ho,hm⟩ := O.exists_min_image (fun j => H j a) ⟨c,mem_filter.mpr ⟨mem_univ _,ac⟩⟩
  have minI (j : X.V) (fr : Fresh X F (j,a)) := sm j (mem_filter.mpr ⟨mem_univ _,fr⟩)
  have minO (j : X.V) (fr : Fresh X F (a,j)) := hm j (mem_filter.mpr ⟨mem_univ _,fr⟩)
  have fs := (mem_filter.mp si).2
  have fh := (mem_filter.mp ho).2
  refine ⟨H,s,h,inv,fs,fh,minI,minO,?_⟩
  intro R S
  have atPair {M} (bm : Boundary X F M) {u v : X.V} (ua : Fresh X F (u,a)) (av : Fresh X F (a,v))
      (p : added X.D F M=pair a u v) : SharedArcCompression.winning X F B M ↔
      1+(q:ℝ)*H v a ≤ outCost R S H a ∨ 1+(q:ℝ)*H a u ≤ inCost R S H a := by
    have e := (SharedArcCompression.winning_iff X small step bad M).trans (test M)
    change SharedArcCompression.winning X F B M ↔ 1 ≤ outCost R _ H a ∨ 1 ≤ inCost R _ H a at e
    obtain ⟨eo,ei⟩ := costs X hq ua av p H
    rw [e,eo,ei]
    constructor <;> rintro (l|r)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  constructor
  · rintro ⟨M,bm,win⟩
    obtain ⟨u,v,ua,av,shape⟩ := boundary_pair X bm (multi.trans_le (least M bm)) a center
    rcases (atPair bm ua av shape).mp win with yes|yes
    · exact Or.inl (by linarith [mul_le_mul_of_nonneg_left (minO v av) (Nat.cast_nonneg (α:=ℝ) q)])
    · exact Or.inr (by linarith [mul_le_mul_of_nonneg_left (minI u ua) (Nat.cast_nonneg (α:=ℝ) q)])
  · obtain ⟨inc,out⟩ := singles X hq small step least bad ta pairB
    rintro (yes|yes)
    · obtain ⟨M,bm,shape⟩ := out h fh
      exact ⟨M,bm,(atPair bm ta fh shape).mpr (Or.inl yes)⟩
    · obtain ⟨M,bm,shape⟩ := inc s fs
      exact ⟨M,bm,(atPair bm fs ac shape).mpr (Or.inr yes)⟩

#print axioms minimum_test

/-- If all boundaries stop, the two endpoint choices can also be made on
one cycle. The intermediate exchange is again a minimum boundary. -/
theorem joint_pair {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {s h : X.V} (fs : Fresh X F (s,a)) (fh : Fresh X F (a,h)) :
    ∃M, Boundary X F M ∧ added X.D F M=pair a s h := by
  classical
  have center := SharedArcPivot.single_center X hq small step least multi edge no
  obtain ⟨t,c,ta,_,p⟩ := boundary_pair X step multi a center
  obtain ⟨M,bm,shape⟩ := (singles X hq small step least (stop B step) ta p).1 s fs
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have two : (targets X.D X.V F M).card ≤ 2 := by
    rw [← count cyc,shape]
    unfold pair
    exact (card_insert_le _ _).trans (by simp)
  have minM (N) (bn : Boundary X F N) := two.trans ((show 2≤(targets X.D X.V F B).card from multi).trans (least N bn))
  exact (singles X hq small bm minM (stop M bm) fs shape).2 h fh

#print axioms joint_pair

/-- Fresh parents and fresh heads form a zero rectangle in the native
adjacency matrix at a stopped pivot. Each entry has a cycle witness. -/
theorem stopped_rectangle {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {s h : X.V} (fs : Fresh X F (s,a)) (fh : Fresh X F (a,h)) :
    X.D s h=false ∧ ∃M, Boundary X F M ∧ added X.D F M=pair a s h := by
  classical
  obtain ⟨M,bm,p⟩ := joint_pair X hq small step least stop multi edge no fs fh
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have i : (s.val,a.val)∈added X.D F M := p ▸ mem_insert_self _ _
  have o : (a.val,h.val)∈added X.D F M := p ▸ mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨sm,am,sa,_⟩ := mem_added.mp i
  obtain ⟨_,hm,_,_⟩ := mem_added.mp o
  refine ⟨Bool.eq_false_iff.mpr (fun sh => ?_),M,bm,p⟩
  exact tail_ne X hq fh (card_le_one.mp (cyc.heads s sm).le _
    (mem_outN.mpr ⟨am,sa⟩) _ (mem_outN.mpr ⟨hm,sh⟩))

#print axioms stopped_rectangle
end LeanCH.BR.Closure.SharedArcPivotChoice
