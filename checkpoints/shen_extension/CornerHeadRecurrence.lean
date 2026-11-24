import checkpoints.shen_extension.CornerResidualJoint
import checkpoints.shen_extension.ShortestCycleFiberModule
import LeanCH.BR.BRRegionCycle

namespace LeanCH.BR.Closure.CornerHeadRecurrence
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

/-- An all-old return through two specified closing arcs. The exterior
    predecessor distinguishes an actual arc among the parents of h. -/
def OldCorner (q : ℕ) (D E : CH.Digraph) (V : Finset ℕ) (h : ℕ) : Prop :=
  ∃ c∈inN D V h, ∃ b∈inN D V h, D c b=true ∧ ∃d∈V,
    E d c=true ∧ E c h=true ∧ D d b=false ∧ D d h=false ∧
    Walk E ((V.erase h)\inN D (V.erase h) h) h d (q-1)

def heads (D E : CH.Digraph) (V : Finset ℕ) (y : ℕ) :=
  (outN D V y).filter (fun j => E y j=false)

def Block (D : CH.Digraph) (U S : Finset ℕ) : Prop :=
  S⊆U ∧ 2≤S.card ∧ InUniform D U S ∧ OutUniform D U S

private theorem lift_away {D E : CH.Digraph} {V S : Finset ℕ} {y : ℕ}
    (sub : S⊆V) (off : y∉S)
    (kept : ∀i∈V,∀j∈V,i≠y → j≠y → D i j=true → E i j=true)
    {u v k} (p : Walk D S u v k) (uv : u∈V) (uy : u≠y) : Walk E S u v k := by
  induction p with
  | refl => exact .refl _
  | @step i j _ _ js ij _ ih =>
    have jy : j≠y := fun e => off (e ▸ js)
    exact .step js (kept i uv j (sub js) uy jy ij) (ih (sub js) jy)

/-- Take the last marked vertex before the end of a finite walk. -/
private theorem last_mark {D : CH.Digraph} {P M : Finset ℕ} {i x k} (p : Walk D P i x k)
    (ip : i∈P) (xm : x∉M) :
    (i∉M ∧ Walk D (P\M) i x k) ∨
    ∃z∈P,z∈M ∧ ∃v∈P\M,D z v=true ∧ ∃l,Walk D (P\M) v x l := by
  induction p with
  | refl => exact Or.inl ⟨xm,.refl _⟩
  | @step i j _ k jp ij _ ih =>
    rcases ih jp xm with ⟨jm,tail⟩ | hit
    · have ju := mem_sdiff.mpr ⟨jp,jm⟩
      by_cases im : i∈M
      · exact Or.inr ⟨i,ip,im,j,ju,ij,k,tail⟩
      · exact Or.inl ⟨im,.step ju ij tail⟩
    · exact Or.inr hit

section
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
  {F B} (step : Boundary X F B)
  (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
  (multi : 1<(targets X.D X.V F B).card) {y a : X.V} (edge : Fresh X F (y,a))
  (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y a) X.V)

include hq small step least multi edge no in
private theorem kept_off (i) (iv : i∈X.V) (j) (jv : j∈X.V)
    (iy : i≠y.val) (jy : j≠y.val) (ij : X.D i j=true) : graph X.D F i j=true := by
  by_contra missing
  let f : SharedArcFlatCut.Missing X F := ⟨(⟨i,iv⟩,⟨j,jv⟩),ij,Bool.eq_false_iff.mpr missing⟩
  exact (SharedArcPivot.single_center X hq small step least multi edge no f).elim
    (fun e=>iy (congrArg Subtype.val e)) (fun e=>jy (congrArg Subtype.val e))

include hq small step least multi edge no in
/-- For any old parent x and any fresh head h, failure to find an old
    corner forces a fresh predecessor of h and an old closed walk through x
    inside h's parents. Only one vertex of that walk is a head of x. -/
theorem at_head {x h : X.V} (old : graph X.D F x y=true) (fresh : Fresh X F (y,h)) :
    let E := graph X.D F
    let H := heads X.D E X.V y
    let P := inN X.D X.V h
    let U := P\outN X.D X.V x
    OldCorner q X.D E X.V h ∨
    ((∃b∈H,E b h=true) ∧ q≤U.card ∧
      ∃z∈P,X.D x z=true ∧ ∃m,q+1≤m ∧ Walk E (insert z U) x x m) := by
  classical
  intro E H P U
  have native {i j} (e : E i j=true) : X.D i j=true := (mem_col.mp (active.mp e).choose_spec).2.2.2
  have kept := kept_off X hq small step least multi edge no
  have cross := SharedArcPivotPaths.crossed X hq small step least multi edge no
  have xy := native old
  have cover {j} (mem : j∈H) : X.D x j=true := by
    obtain ⟨jv,yj⟩ := mem_outN.mp (mem_filter.mp mem).1
    exact cross x ⟨j,jv⟩ xy yj (fun eq=>Bool.noConfusion
      (old.symm.trans (eq.trans (mem_filter.mp mem).2)))
  have xh := cover (show h.val∈H from mem_filter.mpr ⟨mem_outN.mpr ⟨h.property,fresh.2.2.1⟩,fresh.2.2.2⟩)
  have xyNe : x.val≠y.val := fun eq=>loopfree X.free (by omega) y.property (eq ▸ xy)
  have hy : h.val≠y.val := fun eq=>loopfree X.free (by omega) y.property (eq ▸ fresh.2.2.1)
  obtain ⟨c,cp,b,bp,cb,trail,d,dv,dc,db,dh,path⟩ :=
    TwoReceiverIntersection.upstream_corridor X hq fresh.2.2.1 xh xy
  obtain ⟨cv,ch⟩ := mem_inN.mp cp
  obtain ⟨bv,bh⟩ := mem_inN.mp bp
  have dy : d≠y.val := fun eq=>Bool.noConfusion (dh.symm.trans (eq ▸ fresh.2.2.1))
  by_cases cy : c=y.val
  · subst c
    have dOld : E d y=false := Bool.eq_false_iff.mpr (fun ed=>Bool.noConfusion
      (dh.symm.trans (cross ⟨d,dv⟩ h dc fresh.2.2.1 (fun eq=>Bool.noConfusion
        (ed.symm.trans (eq.trans fresh.2.2.2))))))
    have bFresh : E y b=false := Bool.eq_false_iff.mpr (fun ed=>Bool.noConfusion
      (db.symm.trans (cross ⟨d,dv⟩ ⟨b,bv⟩ dc cb (fun eq=>Bool.noConfusion
        (dOld.symm.trans (eq.trans ed))))))
    have bH : b∈H := mem_filter.mpr ⟨mem_outN.mpr ⟨bv,cb⟩,bFresh⟩
    have byNe : b≠y.val := fun eq=>loopfree X.free (by omega) y.property (eq ▸ cb)
    obtain ⟨l,back⟩ := trail.resolve_left (fun eq=>xyNe eq.1.symm)
    let M := outN X.D X.V x
    have bm : b∈M := mem_outN.mpr ⟨bv,cover bH⟩
    have xm : x.val∉M := fun m=>loopfree X.free (by omega) x.property (mem_outN.mp m).2
    have ym : y.val∈M := mem_outN.mpr ⟨y.property,xy⟩
    obtain ⟨z,zp,zm,v,vu,zv,k,tail⟩ := (last_mark (M:=M) back bp xm).resolve_left (fun e=>e.1 bm)
    have pv : P⊆X.V := filter_subset _ _
    have us : U⊆X.V := fun _ u=>pv (mem_sdiff.mp u).1
    have yu : y.val∉U := fun u=>(mem_sdiff.mp u).2 ym
    have xvU : x.val∈U := mem_sdiff.mpr ⟨mem_inN.mpr ⟨x.property,xh⟩,xm⟩
    have vy : v≠y.val := fun eq=>yu (eq ▸ vu)
    have xz : X.D x z=true := (mem_outN.mp zm).2
    have xzOld : E x z=true := by
      by_cases zy : z=y.val
      · exact zy ▸ old
      · exact kept _ x.property _ (pv zp) xyNe zy xz
    have zvOld : E z v=true := by
      by_cases zy : z=y.val
      · subst z
        by_contra off
        have vH : v∈H := mem_filter.mpr ⟨mem_outN.mpr ⟨us vu,zv⟩,Bool.eq_false_iff.mpr off⟩
        exact (mem_sdiff.mp vu).2 (mem_outN.mpr ⟨us vu,cover vH⟩)
      · exact kept _ (pv zp) _ (us vu) zy vy zv
    have oldTail := lift_away us yu kept tail (us vu) vy
    have loop : Walk E (insert z U) x x (k+1+1) := .step (mem_insert_self ..) xzOld
      (.step (mem_insert_of_mem vu) zvOld (oldTail.mono (subset_insert ..)))
    have free := (qfree_sub (fun _ _ e=>native e) X.free).mono_set
      (insert_subset_iff.mpr ⟨pv zp,us⟩ : insert z U⊆X.V)
    obtain ⟨r,S,qr,_,ss,sz,_,_,_⟩ := region_closed_walk_shortest_support (by omega : 1≤q) free (by omega) loop
    have bound := (card_le_card ss).trans (card_insert_le z U)
    have long : q+1≤k+1+1 := by by_contra! short; exact free x _ (by omega) (by omega) loop
    exact Or.inr ⟨⟨b,bH,kept _ bv _ h.property byNe hy bh⟩,by omega,z,zp,xz,_,long,loop⟩
  · let R := (X.V.erase h.val)\inN X.D (X.V.erase h.val) h
    have sub : R⊆X.V := fun _ u=>mem_of_mem_erase (mem_sdiff.mp u).1
    have off : y.val∉R := fun u=>(mem_sdiff.mp u).2 (mem_inN.mpr ⟨(mem_sdiff.mp u).1,fresh.2.2.1⟩)
    exact Or.inl ⟨c,cp,b,bp,cb,d,dv,kept _ dv _ cv dy cy dc,kept _ cv _ h.property cy hy ch,db,dh,
      lift_away sub off kept path h.property hy⟩

include hq small step least multi edge no in
/-- Every predecessor-closed nonempty set of fresh heads contains an
    old corner or an old cycle together with a cut bound at every head. -/
theorem recurrent {x : X.V} (old : graph X.D F x y=true) {S : Finset ℕ} (live : S.Nonempty)
    (sub : S⊆heads X.D (graph X.D F) X.V y)
    (closed : ∀h∈S,∀b∈heads X.D (graph X.D F) X.V y,graph X.D F b h=true → b∈S) :
    (∃h∈S,OldCorner q X.D (graph X.D F) X.V h) ∨
    ((∃b∈S,∃m,q+1≤m ∧ m≤S.card ∧ Walk (graph X.D F) S b b m) ∧
      ∀h∈S,∀u:X.V,graph X.D F u y=true → q≤(inN X.D X.V h\outN X.D X.V u).card) := by
  classical
  apply or_iff_not_imp_left.mpr
  intro fail
  have alt {h} (hh : h∈S) (u : X.V) (uy : graph X.D F u y=true) :
      (∃b∈heads X.D (graph X.D F) X.V y,graph X.D F b h=true) ∧
      q≤(inN X.D X.V h\outN X.D X.V u).card := by
    obtain ⟨hv,yh⟩ := mem_outN.mp (mem_filter.mp (sub hh)).1
    have both := (at_head X hq small step least multi edge no (x:=u) (h:=⟨h,hv⟩) uy
      ⟨y.property,hv,yh,(mem_filter.mp (sub hh)).2⟩).resolve_left (fun hit=>fail ⟨h,hh,hit⟩)
    exact ⟨both.1,both.2.1⟩
  have sv : S⊆X.V := fun _ h=>(mem_outN.mp (mem_filter.mp (sub h)).1).1
  have free := PrivateArcEndpoints.graph_free X F
  refine ⟨closed_walk_of_not_acyclic (D:=graph X.D F) free sv ?_,fun h hh u uy=>(alt hh u uy).2⟩
  intro ac
  obtain ⟨h,hh,source⟩ := exists_sink ac.reverse live le_rfl
  obtain ⟨b,bH,bh⟩ := (alt hh x old).1
  exact source b (closed h hh b bH bh) bh

/-- A saturated puncture with positive flat weights separates every arc
    at its tail. A nontrivial source component is the only way all the
    external parents can propagate along the arcs of a parent set. -/
private theorem component_or_separator {D : CH.Digraph} {U : Finset ℕ} {h q : ℕ}
    (free : QFree D U q) (sat : Sat q D U)
    (sep : ∀c∈U,∀b∈U,D c b=true → ∃d∈U,D d c=true ∧ D d b=false)
    {x b} (xp : x∈inN D U h) (bp : b∈inN D U h) (xb : D x b=true) :
    (∃c∈inN D U h,∃j∈inN D U h,D c j=true ∧ ∃d∈U,D d c=true ∧ D d j=false ∧ D d h=false) ∨
    ∃S,Block D U S ∧ S⊆inN D U h := by
  classical
  let P := inN D U h
  let A := P.filter (fun i=>∃j∈P,D i j=true)
  have live : A.Nonempty := ⟨x,mem_filter.mpr ⟨xp,b,bp,xb⟩⟩
  obtain ⟨S,sl,sa,sc,strong⟩ := exists_closed_strong_bank (fun i j=>D j i) live
  have sp : S⊆P := fun _ s=>(mem_filter.mp (sa s)).1
  have su : S⊆U := fun _ s=>(mem_inN.mp (sp s)).1
  have inward {i j} (si : i∈S) (jp : j∈P) (ji : D j i=true) : j∈S :=
    sc i si j (mem_filter.mpr ⟨jp,i,sp si,ji⟩) ji
  apply or_iff_not_imp_left.mpr
  intro noSep
  by_cases large : 2≤S.card
  · have uni : InUniform D U S := by
      intro c cs j js d du ds
      by_cases dp : d∈P
      · have off {i} (si : i∈S) := Bool.eq_false_iff.mpr (fun (ed : D d i=true)=>ds (inward si dp ed))
        exact (off cs).trans (off js).symm
      · have dh : D d h=false := Bool.eq_false_iff.mpr (fun ed=>dp (mem_inN.mpr ⟨du,ed⟩))
        have along {i k l} (p : Walk (fun u v=>D v u) S i k l) (si : i∈S) : D d k=true → D d i=true := by
          induction p with
          | refl => exact id
          | @step i j _ _ sj ji _ ih =>
            intro hit
            by_contra off
            exact noSep ⟨j,sp sj,i,sp si,ji,d,du,ih sj hit,Bool.eq_false_iff.mpr off,dh⟩
        obtain ⟨_,cj⟩ := strong c cs j js
        obtain ⟨_,jc⟩ := strong j js c cs
        exact Bool.eq_iff_iff.mpr ⟨along jc js,along cj cs⟩
    exact ⟨S,⟨su,large,uni,outUniform_inUniform free.reverse (SerialChain.sat_reverse sat) su uni⟩,sp⟩
  · obtain ⟨c,cs⟩ := sl
    obtain ⟨j,jp,cj⟩ := (mem_filter.mp (sa cs)).2
    obtain ⟨d,du,dc,dj⟩ := sep c (su cs) j (mem_inN.mp jp).1 cj
    have dh : D d h=false := Bool.eq_false_iff.mpr (fun ed=>by
      have ds := inward cs (mem_inN.mpr ⟨du,ed⟩) dc
      have eq := card_le_one.mp (show S.card≤1 by omega) d ds c cs
      exact Bool.noConfusion (dj.symm.trans (by simpa only [eq] using cj)))
    exact (noSep ⟨c,sp cs,j,jp,cj,d,du,dc,dj,dh⟩).elim

include hq small step least multi edge no in
theorem module_at_head {x h : X.V} (old : graph X.D F x y=true) (fresh : Fresh X F (y,h))
    (absent : ¬OldCorner q X.D (graph X.D F) X.V h) :
    ∃S,Block X.D (X.V.erase y.val) S ∧ S⊆inN X.D (X.V.erase y.val) h := by
  classical
  let U := X.V.erase y.val
  have uf := X.free.mono_set (erase_subset y.val X.V)
  obtain ⟨_,sat,_,w,wp,wm,wr⟩ := (SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no
  have sep (c) (cu : c∈U) (b) (bu : b∈U) (cb : X.D c b=true) : ∃d∈U,X.D d c=true ∧ X.D d b=false := by
    have less : SmallerSmallRow q U.card := fun E T lt f=>small E T (lt.trans (card_erase_lt_of_mem y.property)) f
    have ret := feasible_reach_positive_within hq uf less w (fun i iu=>(wp i iu).le)
      (fun i iu=>(wm.trans (wr i iu).symm).le) bu cu (wp c cu)
    obtain ⟨_,k,km,path⟩ := mem_ball.mp ret
    cases k with
    | zero => exact (loopfree uf (by omega) cu (walk_zero path ▸ cb)).elim
    | succ k =>
      obtain ⟨d,pre,_,dc⟩ := path.unsnoc
      exact ⟨d,pre.end_mem_or.elim (fun e=>e ▸ bu) id,dc,
        Bool.eq_false_iff.mpr (fun db=>uf b _ (by omega) km (pre.snoc bu db))⟩
  obtain ⟨b,bH,bh⟩ := ((at_head X hq small step least multi edge no old fresh).resolve_left absent).1
  obtain ⟨bv,yb⟩ := mem_outN.mp (mem_filter.mp bH).1
  have native {i j} (e : graph X.D F i j=true) : X.D i j=true := (mem_col.mp (active.mp e).choose_spec).2.2.2
  have xy := native old
  have xu : x.val∈U := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property (eq ▸ xy),x.property⟩
  have bu : b∈U := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property (eq ▸ yb),bv⟩
  have cross := SharedArcPivotPaths.crossed X hq small step least multi edge no
  have xb := cross x ⟨b,bv⟩ (native old) yb (fun eq=>Bool.noConfusion (old.symm.trans (eq.trans (mem_filter.mp bH).2)))
  have xh := cross x h (native old) fresh.2.2.1 (fun eq=>Bool.noConfusion (old.symm.trans (eq.trans fresh.2.2.2)))
  apply (component_or_separator uf sat sep (mem_inN.mpr ⟨xu,xh⟩) (mem_inN.mpr ⟨bu,native bh⟩) xb).resolve_left
  rintro ⟨c,cp,j,jp,cj,d,du,dc,dj,dh⟩
  have cu := (mem_inN.mp cp).1
  have ch := (mem_inN.mp cp).2
  have hu : h.val∈U := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property (eq ▸ fresh.2.2.1),h.property⟩
  have kept := kept_off X hq small step least multi edge no
  have oldIn {i j} (iu : i∈U) (ju : j∈U) := kept i (mem_of_mem_erase iu) j (mem_of_mem_erase ju)
    (mem_erase.mp iu).1 (mem_erase.mp ju).1
  have widen {i} (ip : i∈inN X.D U h) : i∈inN X.D X.V h :=
    mem_inN.mpr ⟨mem_of_mem_erase (mem_inN.mp ip).1,(mem_inN.mp ip).2⟩
  apply absent
  refine ⟨c,widen cp,j,widen jp,cj,d,mem_of_mem_erase du,oldIn du cu dc,oldIn cu hu ch,dj,dh,?_⟩
  obtain ⟨_,k,le,path⟩ := mem_ball.mp (sat _ hu _ du (Bool.eq_false_iff.mp dh))
  have len : k=q-1 := by by_contra ne; exact uf h _ (by omega) (by omega) ((path.snoc cu dc).snoc hu ch)
  have lift {i l} (p : Walk X.D U h i l) (le : l≤q-1) :
      Walk (graph X.D F) ((X.V.erase h.val)\inN X.D (X.V.erase h.val) h) h i l := by
    induction l generalizing i with
    | zero => cases p; exact .refl _
    | succ l ih =>
      obtain ⟨v,pre,iu,vi⟩ := p.unsnoc
      have vu := pre.end_mem_or.elim (fun e=>e ▸ hu) id
      have ne : i≠h.val := fun e=>uf h _ (by omega) (by omega) (e ▸ p)
      have off : i∉inN X.D (X.V.erase h.val) h := fun ip=>
        uf h _ (by omega) (by omega) (p.snoc hu (mem_inN.mp ip).2)
      exact (ih pre (by omega)).snoc (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,mem_of_mem_erase iu⟩,off⟩) (oldIn vu iu vi)
  exact len ▸ lift path le

private theorem meets_pivot {S : Finset ℕ} (block : Block X.D (X.V.erase y.val) S) :
    (∃t∈S,X.D t y=true) ∧ ∃v∈S,X.D y v=true := by
  classical
  obtain ⟨su,big,inc,out⟩ := block
  have sv : S⊆X.V := fun _ s=>mem_of_mem_erase (su s)
  have proper : S≠X.V := fun eq=>(mem_erase.mp (su (eq ▸ y.property))).1 rfl
  have prime := X.prime S sv big proper
  constructor
  · by_contra! none
    have all : OutUniform X.D X.V S := by
      intro i si j sj z zv zs
      by_cases e : z=y.val
      · subst z; exact (Bool.eq_false_iff.mpr (none i si)).trans (Bool.eq_false_iff.mpr (none j sj)).symm
      · exact out i si j sj z (mem_erase.mpr ⟨e,zv⟩) zs
    exact prime ⟨all,outUniform_inUniform X.free X.sat sv all⟩
  · by_contra! none
    have all : InUniform X.D X.V S := by
      intro i si j sj z zv zs
      by_cases e : z=y.val
      · subst z; exact (Bool.eq_false_iff.mpr (none i si)).trans (Bool.eq_false_iff.mpr (none j sj)).symm
      · exact inc i si j sj z (mem_erase.mpr ⟨e,zv⟩) zs
    exact prime ⟨outUniform_inUniform X.free.reverse (SerialChain.sat_reverse X.sat) sv all,all⟩

/-- The module produced by finite descent supplies old two-step paths
    for the entire rectangle of fresh parents and fresh heads at once. -/
def OldBlockAt (D E : CH.Digraph) (V : Finset ℕ) (y : ℕ) (S : Finset ℕ) : Prop :=
    Block D (V.erase y) S ∧
    (∀m∈S,E m y=D m y ∧ E y m=D y m) ∧
    (∃t∈S,E t y=true) ∧ (∃v∈S,E y v=true) ∧
    (∀i∈V,D i y=true → E i y=false → ∀m∈S,E i m=true) ∧
    (∀j∈V,D y j=true → E y j=false → ∀m∈S,E m j=true)

def OldBlock (D E : CH.Digraph) (V : Finset ℕ) (y : ℕ) := ∃S,OldBlockAt D E V y S

include hq small step least multi edge no in
theorem descend (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {x : X.V} (old : graph X.D F x y=true) :
    let E := graph X.D F
    let H := heads X.D E X.V y
    (∃h∈H,OldCorner q X.D E X.V h) ∨ OldBlock X.D E X.V y := by
  classical
  intro E H
  apply or_iff_not_imp_left.mpr
  intro none
  let U := X.V.erase y.val
  let C := fun (S : Finset ℕ) => ∃h∈H,Block X.D U S ∧ S⊆inN X.D U h
  have freshH {h} (hh : h∈H) : Fresh X F (y.val,h) :=
    ⟨y.property,(mem_outN.mp (mem_filter.mp hh).1).1,(mem_outN.mp (mem_filter.mp hh).1).2,(mem_filter.mp hh).2⟩
  have findS {h} (hh : h∈H) : ∃S,Block X.D U S ∧ S⊆inN X.D U h := by
    let h' : X.V := ⟨h,(freshH hh).2.1⟩
    exact module_at_head X hq small step least multi edge no (h:=h') old (freshH hh) (fun e=>none ⟨h,hh,e⟩)
  have initial : a.val∈H := mem_filter.mpr ⟨mem_outN.mpr ⟨a.property,edge.2.2.1⟩,edge.2.2.2⟩
  have existsSize : ∃k,∃S,C S ∧ (S∩H).card=k := by
    obtain ⟨S,bl,sp⟩ := findS initial
    exact ⟨_,S,⟨a,initial,bl,sp⟩,rfl⟩
  obtain ⟨S,sC,size⟩ := Nat.find_spec existsSize
  obtain ⟨h,hh,bl,parents⟩ := sC
  have cross := SharedArcPivotPaths.crossed X hq small step least multi edge no
  have zero {i j : X.V} (iy : Fresh X F (i,y)) (yj : Fresh X F (y,j)) :=
    (SharedArcPivotChoice.stopped_rectangle X hq small step least stop multi edge no iy yj).1
  have inOld {m} (ms : m∈S) (my : X.D m y=true) : E m y=true := by
    by_contra off
    let i : X.V := ⟨m,mem_of_mem_erase (bl.1 ms)⟩
    let j : X.V := ⟨h,(freshH hh).2.1⟩
    exact Bool.noConfusion ((zero (i:=i) (j:=j) ⟨i.property,y.property,my,Bool.eq_false_iff.mpr off⟩
      (freshH hh)).symm.trans (mem_inN.mp (parents ms)).2)
  obtain ⟨⟨t,ts,ty⟩,⟨v,vs,yv⟩⟩ := meets_pivot X (y:=y) bl
  let t' : X.V := ⟨t,mem_of_mem_erase (bl.1 ts)⟩
  have th {j} (jH : j∈H) : X.D t j=true := cross t' ⟨j,(freshH jH).2.1⟩ ty (freshH jH).2.2.1
    (fun eq=>Bool.noConfusion ((inOld ts ty).symm.trans (eq.trans (freshH jH).2.2.2)))
  have ju {j} (jh : j∈H) : j∈U := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property
    (by simpa only [eq] using (freshH jh).2.2.1),(freshH jh).2.1⟩
  have dis {k} (ks : k∈S) (kh : k∈H) : False := by
    obtain ⟨T,block,inside⟩ := findS kh
    have incl : T∩H⊆(S∩H).erase k := by
      intro j jm
      obtain ⟨jt,jh⟩ := mem_inter.mp jm
      have jk := (mem_inN.mp (inside jt)).2
      have ne : j≠k := fun eq=>loopfree X.free (by omega) (freshH kh).2.1 (eq ▸ jk)
      refine mem_erase.mpr ⟨ne,mem_inter.mpr ⟨?_,jh⟩⟩
      by_contra js
      have hit := (bl.2.2.1 k ks t ts j (ju jh) js).symm.trans jk
      exact X.free t 2 (by decide) hq (.step (freshH jh).2.1 (th jh) (.step t'.property hit (.refl _)))
    have lt := (card_le_card incl).trans_lt (card_erase_lt_of_mem (mem_inter.mpr ⟨ks,kh⟩))
    have ge := Nat.find_min' existsSize (show ∃L,C L ∧ (L∩H).card=(T∩H).card from
      ⟨T,⟨k,kh,block,inside⟩,rfl⟩)
    omega
  have outOld {m} (ms : m∈S) (ym : X.D y m=true) : E y m=true := by
    by_contra off
    exact dis ms (mem_filter.mpr ⟨mem_outN.mpr ⟨mem_of_mem_erase (bl.1 ms),ym⟩,Bool.eq_false_iff.mpr off⟩)
  have native {i j} (e : E i j=true) : X.D i j=true := (mem_col.mp (active.mp e).choose_spec).2.2.2
  have kept := kept_off X hq small step least multi edge no
  refine ⟨S,bl,fun m ms=>⟨Bool.eq_iff_iff.mpr ⟨native,inOld ms⟩,Bool.eq_iff_iff.mpr ⟨native,outOld ms⟩⟩,
    ⟨t,ts,inOld ts ty⟩,⟨v,vs,outOld vs yv⟩,?_,?_⟩
  · intro i iv iy miss m ms
    have ni : i≠y.val := fun eq=>loopfree X.free (by omega) y.property (eq ▸ iy)
    have outside : i∉S := fun si=>Bool.noConfusion (miss.symm.trans (inOld si iy))
    have hit := cross ⟨i,iv⟩ ⟨v,mem_of_mem_erase (bl.1 vs)⟩ iy yv
      (fun eq=>Bool.noConfusion (miss.symm.trans (eq.trans (outOld vs yv))))
    exact kept i iv m (mem_of_mem_erase (bl.1 ms)) ni (mem_erase.mp (bl.1 ms)).1
      ((bl.2.2.1 m ms v vs i (mem_erase.mpr ⟨ni,iv⟩) outside).trans hit)
  · intro j jv yj miss m ms
    have jh : j∈H := mem_filter.mpr ⟨mem_outN.mpr ⟨jv,yj⟩,miss⟩
    exact kept m (mem_of_mem_erase (bl.1 ms)) j jv (mem_erase.mp (bl.1 ms)).1 (mem_erase.mp (ju jh)).1
      ((bl.2.2.2 m ms t ts j (ju jh) (fun s=>dis s jh)).trans (th jh))

/-- Each boundary cycle has a fixed path and one moving label. Every
    replacement from S is already a member of the selected family, and
    every actual arc among the moving labels gives an oriented shift. -/
def Copies (D : CH.Digraph) (F : Family) (M S : Finset ℕ) (y : ℕ) : Prop :=
  let P := M.erase y
  let slot := fun i=>insert i P
  Disjoint P (insert y S) ∧ (∀z∈P,∀m∈S,D m z=D y z ∧ D z m=D z y) ∧ (∀m∈S,slot m∈F) ∧
  ∃t h,∀i∈insert y S,∀j∈insert y S,D i j=true →
    CycleSquareTensor.Shift D (slot i) (slot j) t i j h

include hq small step least multi edge no in
theorem copies {S M} (block : OldBlockAt X.D (graph X.D F) X.V y S) (bm : Boundary X F M) :
    Copies X.D F M S y := by
  classical
  obtain ⟨bl,_,_,_,allIn,allOut⟩ := block
  have inside {m} (ms : m∈S) := mem_of_mem_erase (bl.1 ms)
  have sv : insert y.val S⊆X.V := insert_subset_iff.mpr ⟨y.property,fun _ ms=>inside ms⟩
  have center := SharedArcPivot.single_center X hq small step least multi edge no
  obtain ⟨t,h,ty,yh,shape⟩ := SharedArcPivotChoice.boundary_pair X bm (lt_of_lt_of_le multi (least M bm)) y center
  have ti : (t.val,y.val)∈added X.D F M := shape ▸ mem_insert_self _ _
  have hi : (y.val,h.val)∈added X.D F M := shape ▸ mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨tm,ym,_,_⟩ := mem_added.mp ti
  have hm := (mem_added.mp hi).2.1
  have native {i j} (ed : graph X.D F i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have edges (z) (zs : z∈insert y.val S) : X.D t z=true ∧ X.D z h=true := by
    rcases mem_insert.mp zs with rfl|ms
    · exact ⟨ty.2.2.1,yh.2.2.1⟩
    · exact ⟨native (allIn t t.property ty.2.2.1 ty.2.2.2 z ms),native (allOut h h.property yh.2.2.1 yh.2.2.2 z ms)⟩
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  obtain ⟨dis,fits⟩ := ShortestCycleFiberModule.slots (by omega : 1≤q) X.free cyc tm ym hm sv (mem_insert_self ..) edges
  let P := M.erase y.val
  have tp : t.val∈P := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property (eq ▸ ty.2.2.1),tm⟩
  have hp : h.val∈P := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property (eq ▸ yh.2.2.1),hm⟩
  refine ⟨dis,?_,?_,t,h,?_⟩
  · intro z zp m ms
    have profile (i) (im : i∈insert y.val S) :
        (X.D i z=true ↔ z=h.val) ∧ (X.D z i=true ↔ z=t.val) := by
      have c := fits i im
      have cs := edges i im
      have zi : z∈insert i P := mem_insert_of_mem zp
      have ih : i∈insert i P := mem_insert_self ..
      exact ⟨⟨fun hit=>card_le_one.mp (c.heads i ih).le _ (mem_outN.mpr ⟨zi,hit⟩) _
        (mem_outN.mpr ⟨mem_insert_of_mem hp,cs.2⟩),fun eq=>eq ▸ cs.2⟩,
        ⟨fun hit=>card_le_one.mp (c.incoming i ih).le _ (mem_inN.mpr ⟨zi,hit⟩) _
        (mem_inN.mpr ⟨mem_insert_of_mem tp,cs.1⟩),fun eq=>eq ▸ cs.1⟩⟩
    have first := profile m (mem_insert_of_mem ms)
    have pivot := profile y (mem_insert_self ..)
    exact ⟨Bool.eq_iff_iff.mpr (first.1.trans pivot.1.symm),Bool.eq_iff_iff.mpr (first.2.trans pivot.2.symm)⟩
  · intro m ms
    let N := insert m P
    have nm : m∈N := mem_insert_self ..
    have nt : t.val∈N := mem_insert_of_mem tp
    have cn := fits m (mem_insert_of_mem ms)
    have outside {z} (zn : z∈N) : z≠y.val := (mem_insert.mp zn).elim
      (fun eq=>eq ▸ (mem_erase.mp (bl.1 ms)).1) (fun zp=>(mem_erase.mp zp).1)
    by_contra newCycle
    obtain ⟨A,use⟩ := active.mp (allIn t t.property ty.2.2.1 ty.2.2.2 m ms)
    obtain ⟨af,ta,ma,arc⟩ := mem_col.mp use
    have boundary : Boundary X F N := ⟨mem_filter.mpr ⟨mem_powerset.mpr cn.sub,cn⟩,newCycle,
      A,af,t,mem_inter.mpr ⟨ta,nt⟩,m,mem_inter.mpr ⟨ma,nm⟩,arc⟩
    have zero : targets X.D X.V F N=∅ := eq_empty_iff_forall_notMem.mpr (by
      intro j hit
      obtain ⟨_,jn,i,inn,ij,off⟩ := mem_filter.mp hit
      exact Bool.noConfusion (off.symm.trans (kept_off X hq small step least multi edge no
        i (cn.sub inn) j (cn.sub jn) (outside inn) (outside jn) ij)))
    have low := least N boundary
    rw [zero,card_empty] at low
    omega
  · intro i im j jm ij
    have ji : j≠i := fun eq=>loopfree X.free (by omega) (sv im) (eq ▸ ij)
    have ip : i∉P := fun here=>disjoint_left.mp dis here im
    have jp : j∉P := fun here=>disjoint_left.mp dis here jm
    refine ⟨mem_insert_of_mem tp,mem_insert_self ..,mem_insert_of_mem hp,fun hit=>(mem_insert.mp hit).elim ji jp,
      (edges i im).1,(edges i im).2,(edges j jm).1,(edges j jm).2,ij,?_⟩
    simp [show i∉M.erase y.val from ip]

/-- A fixed splitter of the pivot from every member of the block, away
    from every attachable cycle simultaneously. The two directions may
    have different splitters. -/
def Outside {q n} (X : Model q n) (F : Family) (S : Finset ℕ) (y : ℕ) (R : CH.Digraph) : Prop :=
  ∃z∈X.V,z∉insert y S ∧ (∀M,Boundary X F M → z∉M) ∧ ∀m∈S,R m z≠R y z

private theorem outside_of_nonuniform {q n} (X : Model q n) {F S y} (R : CH.Digraph)
    (sv : S⊆X.V.erase y) (live : S.Nonempty) (old : OutUniform R (X.V.erase y) S)
    (splits : ¬OutUniform R X.V (insert y S))
    (fixed : ∀M,Boundary X F M → ∀z∈M.erase y,∀m∈S,R m z=R y z) : Outside X F S y R := by
  classical
  unfold OutUniform at splits
  push Not at splits
  obtain ⟨a,at',b,bt,z,zv,zt,diff⟩ := splits
  have zy : z≠y := fun eq=>zt (eq ▸ mem_insert_self ..)
  have zs : z∉S := fun hs=>zt (mem_insert_of_mem hs)
  have all (m) (ms : m∈S) : R m z≠R y z := by
    intro equal
    have eq {i} (it : i∈insert y S) : R i z=R y z := by
      rcases mem_insert.mp it with rfl|si
      · rfl
      · exact (old i si m ms z (mem_erase.mpr ⟨zy,zv⟩) zs).trans equal
    exact diff ((eq at').trans (eq bt).symm)
  obtain ⟨m,ms⟩ := live
  exact ⟨z,zv,zt,fun M bm zm=>all m ms (fixed M bm z (mem_erase.mpr ⟨zy,zm⟩) m ms),all⟩

include hq in
theorem splitters {S} (bl : OldBlockAt X.D (graph X.D F) X.V y S)
    (copy : ∀M,Boundary X F M → Copies X.D F M S y) (fresh : Fresh X F (y,a)) :
    Outside X F S y X.D ∧ Outside X F S y (fun i j=>X.D j i) := by
  classical
  let T := insert y.val S
  have sv := bl.1.1
  have size := bl.1.2.1
  have live : S.Nonempty := card_pos.mp (by omega)
  have sub : T⊆X.V := insert_subset_iff.mpr ⟨y.property,fun _ ms=>mem_of_mem_erase (sv ms)⟩
  have more := card_le_card (subset_insert y.val S)
  have big : 2≤T.card := size.trans more
  have proper : T≠X.V := by
    intro eq
    have at' : a.val∈T := by rw [eq]; exact a.property
    rcases mem_insert.mp at' with same|sa
    · exact loopfree X.free (by omega) y.property (same ▸ fresh.2.2.1)
    · exact Bool.noConfusion (fresh.2.2.2.symm.trans ((bl.2.1 a sa).2.trans fresh.2.2.1))
  have prime := X.prime T sub big proper
  constructor
  · apply outside_of_nonuniform X X.D sv live bl.1.2.2.2 (fun out=>prime ⟨out,outUniform_inUniform X.free X.sat sub out⟩)
    exact fun M bm z zp m ms=>((copy M bm).2.1 z zp m ms).1
  · apply outside_of_nonuniform X (fun i j=>X.D j i) sv live bl.1.2.2.1 (fun inc=>prime
      ⟨outUniform_inUniform X.free.reverse (SerialChain.sat_reverse X.sat) sub inc,inc⟩)
    exact fun M bm z zp m ms=>((copy M bm).2.1 z zp m ms).2

include hq small step least multi edge no in
private theorem classified {C} (cyc : ShenCycleSuccessor.Cycle X.D X.V q C) : C∈F ∨ Boundary X F C := by
  classical
  by_cases cf : C∈F
  · exact Or.inl cf
  have next (i) (ic : i∈C) : ∃j∈C,X.D i j=true := by
    obtain ⟨j,jh⟩ := card_pos.mp (show 0<(outN X.D C i).card by rw [cyc.heads i ic]; decide)
    exact ⟨j,mem_outN.mp jh⟩
  obtain ⟨i,ic,j,jc,iy,jy,ij⟩ : ∃i∈C,∃j∈C,i≠y.val ∧ j≠y.val ∧ X.D i j=true := by
    by_cases yc : y.val∈C
    · obtain ⟨i,ic,yi⟩ := next y yc
      obtain ⟨j,jc,ij⟩ := next i ic
      exact ⟨i,ic,j,jc,fun eq=>loopfree X.free (by omega) y.property (eq ▸ yi),
        fun eq=>X.free y 2 (by decide) hq (.step (cyc.sub ic) yi (.step y.property (eq ▸ ij) (.refl _))),ij⟩
    · have size := cyc.size
      obtain ⟨i,ic⟩ := card_pos.mp (show 0<C.card by omega)
      obtain ⟨j,jc,ij⟩ := next i ic
      exact ⟨i,ic,j,jc,fun eq=>yc (eq ▸ ic),fun eq=>yc (eq ▸ jc),ij⟩
  obtain ⟨A,use⟩ := active.mp (kept_off X hq small step least multi edge no i (cyc.sub ic) j (cyc.sub jc) iy jy ij)
  obtain ⟨af,ia,ja,_⟩ := mem_col.mp use
  exact Or.inr ⟨mem_filter.mpr ⟨mem_powerset.mpr cyc.sub,cyc⟩,cf,A,af,i,mem_inter.mpr ⟨ia,ic⟩,
    j,mem_inter.mpr ⟨ja,jc⟩,ij⟩

def SelectedAt {q n} (X : Model q n) (F : Family) (S : Finset ℕ) (y : ℕ) (R : CH.Digraph) : Prop :=
  ∃z∈X.V,z∉insert y S ∧ (∀m∈S,R m z≠R y z) ∧
    ∀C,ShenCycleSuccessor.Cycle X.D X.V q C → z∈C → C∈F

include hq small step least multi edge no in
private theorem selected {S R} (split : Outside X F S y R) : SelectedAt X F S y R := by
  obtain ⟨z,zv,zs,off,diff⟩ := split
  exact ⟨z,zv,zs,diff,fun C cyc zc=>(classified X hq small step least multi edge no cyc).resolve_right
    (fun bm=>off C bm zc)⟩

/-- For every internal entry and exit of the pivot there is a return
    wholly inside the block. Its exact length decides the period of the
    corresponding closed sequence of cycle replacements. -/
def InternalReturns (q : ℕ) (E : CH.Digraph) (S : Finset ℕ) (y : ℕ) : Prop :=
  ∀v∈S,E y v=true → ∀t∈S,E t y=true →
    Walk E S v t (if E t v=true then q else q-1)

include hq small step least multi edge no in
theorem block_size {S} (bl : OldBlockAt X.D (graph X.D F) X.V y S) : q<S.card := by
  let U := X.V.erase y.val
  obtain ⟨_,_,_,w,wp,wm,wr⟩ := (SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no
  have free := X.free.mono_set (erase_subset y.val X.V)
  have less : SmallerSmallRow q U.card := fun J L lt fr=>small J L (lt.trans (card_erase_lt_of_mem y.property)) fr
  have su := bl.1.1
  by_contra! short
  obtain ⟨i,si,sink⟩ := exists_sink (free.mono_set su) (card_pos.mp (by have := bl.1.2.1; omega)) short
  obtain ⟨a,sa,b,sb,ab⟩ := one_lt_card.mp (show 1<S.card from bl.1.2.1)
  obtain ⟨r,sr,ne⟩ : ∃r∈S,i≠r := by
    by_cases ia : i=a
    · exact ⟨b,sb,ia ▸ ab⟩
    · exact ⟨a,sa,ia⟩
  obtain ⟨_,k,le,path⟩ := mem_ball.mp (feasible_reach_positive_within hq free less w (fun j ju=>(wp j ju).le)
    (fun j ju=>(wm.trans (wr j ju).symm).le) (su si) (su sr) (wp r (su sr)))
  cases path with
  | refl => exact ne rfl
  | @step _ j _ k ju ij tail =>
    by_cases sj : j∈S
    · exact sink j sj ij
    · exact free r (k+1) (by omega) le (.step ju ((bl.1.2.2.2 r sr i si j ju sj).trans ij) tail)

include hq small step least multi edge no in
theorem internal_returns {S} (bl : OldBlockAt X.D (graph X.D F) X.V y S) :
    InternalReturns q (graph X.D F) S y := by
  classical
  let E := graph X.D F
  let U := X.V.erase y.val
  obtain ⟨_,sat,_,w,wp,wm,wr⟩ := (SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no
  have uf := X.free.mono_set (erase_subset y.val X.V)
  have less : SmallerSmallRow q U.card := fun J L lt fr=>small J L (lt.trans (card_erase_lt_of_mem y.property)) fr
  have native {i j} (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have su := bl.1.1
  have kept {i j} (si : i∈S) (sj : j∈S) := kept_off X hq small step least multi edge no i
    (mem_of_mem_erase (su si)) j (mem_of_mem_erase (su sj)) (mem_erase.mp (su si)).1 (mem_erase.mp (su sj)).1
  intro v vs yv t ts ty
  change Walk E S v t (if E t v=true then q else q-1)
  have lock {i k} (path : Walk X.D U i t k) (si : i∈S) (lim : k≤q) : Walk E S i t k := by
    induction path with
    | refl => exact .refl _
    | @step i j dest k ju ij tail ih =>
      have sj : j∈S := by
        by_contra off
        have destJ := (bl.1.2.2.2 dest ts i si j ju off).trans ij
        exact uf dest (k+1) (by omega) lim (.step ju destJ tail)
      exact .step sj (kept si sj ij) (ih ts ty sj (by omega))
  by_cases tv : E t v=true
  · obtain ⟨_,k,le,path⟩ := mem_ball.mp (feasible_reach_positive_within hq uf less w (fun i iu=>(wp i iu).le)
      (fun i iu=>(wm.trans (wr i iu).symm).le) (su vs) (su ts) (wp t (su ts)))
    have eq : k=q := by by_contra ne; exact uf v (k+1) (by omega) (by omega) (path.snoc (su vs) (native tv))
    simpa only [tv,ite_true,←eq] using lock path vs le
  · obtain ⟨_,k,le,path⟩ := mem_ball.mp (sat v (su vs) t (su ts) (fun e=>tv (kept ts vs e)))
    have eq : k=q-1 := by
      by_contra ne
      exact X.free y (k+1+1) (by omega) (by omega) (.step (mem_of_mem_erase (su vs)) (native yv)
        ((path.mono (erase_subset ..)).snoc y.property (native ty)))
    rw [ite_eq_right tv,←eq]
    exact lock path vs (by omega)

include hq small step least in
/-- Capstone interface: a single stalled insertion applies the family
    descent simultaneously to every actual boundary. -/
theorem frontier (sub : F⊆family X) (spans : SharedArcExpansion.support F=X.V)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (many : 1<(targets X.D X.V F B).card) {u v : X.V} (fresh : Fresh X F (u,v)) :
    let E := graph X.D F
    SharedArcReachMargin.StrictColumns q (insertArc E u v) X.V ∨
    (∃h∈heads X.D E X.V u,OldCorner q X.D E X.V h) ∨
    ∃S,OldBlockAt X.D E X.V u S ∧ q<S.card ∧ InternalReturns q E S u ∧ (∀M,Boundary X F M → Copies X.D F M S u) ∧
      SelectedAt X F S u X.D ∧ SelectedAt X F S u (fun i j=>X.D j i) := by
  classical
  intro E
  apply or_iff_not_imp_left.mpr
  intro stuck
  have live : u.val∈SharedArcExpansion.support F := by rw [spans]; exact u.property
  obtain ⟨C,cf,uc⟩ := mem_biUnion.mp live
  have cc : ShenCycleSuccessor.Cycle X.D X.V q C := (mem_filter.mp (sub cf)).2
  obtain ⟨x,xu⟩ := card_pos.mp (show 0<(inN X.D C u).card by
    have one := cc.incoming u uc
    change (inN X.D C u).card=1 at one
    omega)
  obtain ⟨xc,xy⟩ := mem_inN.mp xu
  have old : E x u=true := active.mpr ⟨C,mem_col.mpr ⟨cf,xc,uc,xy⟩⟩
  rcases descend X hq small step least many fresh stuck stop (x:=⟨x,cc.sub xc⟩) old with corner | ⟨S,bl⟩
  · exact Or.inl corner
  · have copy (M) (bm : Boundary X F M) := copies X hq small step least many fresh stuck bl bm
    obtain ⟨left,right⟩ := splitters X hq bl copy fresh
    exact Or.inr ⟨S,bl,block_size X hq small step least many fresh stuck bl,internal_returns X hq small step least many fresh stuck bl,copy,selected X hq small step least many fresh stuck left,
      selected X hq small step least many fresh stuck right⟩

end
#print axioms at_head
#print axioms recurrent
#print axioms module_at_head
#print axioms descend
#print axioms copies
#print axioms splitters
#print axioms internal_returns
#print axioms block_size
#print axioms frontier
end LeanCH.BR.Closure.CornerHeadRecurrence
