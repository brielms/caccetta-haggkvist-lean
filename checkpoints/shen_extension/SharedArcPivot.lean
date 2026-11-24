import LeanCH.BR.BRWeightedOrderCongruence
import checkpoints.shen_extension.SharedArcExchangeReturn
import checkpoints.shen_extension.SharedArcLoopClosure

namespace LeanCH.BR.Closure.SharedArcPivot
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcBarrier SharedArcComponentExchange SharedArcExpansion
open scoped Matrix

/-- If a weak feasible spanning subgraph misses a target, every omitted
native arc is incident to that target. All other native rows are exactly
tight at the same probability vector. -/
theorem one_hole {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (E : CH.Digraph) (incl : ∀i j,E i j=true → X.D i j=true)
    (a y : X.V) (hole : (a:ℕ)∉ball E X.V y q)
    (survives : ¬SharedArcReachMargin.StrictColumns q E X.V) :
    ∃w : X.V→ℚ,(∀i,0≤w i) ∧ (∑i,w i)=1 ∧ w a=0 ∧
      (∀i,i≠a → 0<w i ∧ (WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D X.V) *ᵥ w) i=1) ∧
      ∀i j : X.V,X.D i j=true → E i j=false → i=a ∨ j=a := by
  classical
  let _ : Nonempty X.V := ⟨a⟩
  let S := WeightedArithmetic.rationalMatrix q (adjacencyMatrix E X.V)
  obtain ⟨w,wn,wm,wr⟩ : ∃w : X.V→ℚ,(∀k,0≤w k) ∧ (∑k,w k)=1 ∧ ∀k,1≤∑l,S k l*w l := by
    by_contra no
    obtain ⟨p,pn,pm,pc⟩ := FiniteDual.rational_demand_strict_separator (J:=X.V) S (fun _ => 1) 1
      (by norm_num) no
    apply survives
    refine ⟨p,pn,pm,fun j => ?_⟩
    have e := pc j
    simp only [Rat.cast_one,one_mul,mul_one,pm] at e
    exact e
  have wa : w a=0 := by
    apply le_antisymm _ (wn a)
    by_contra! pos
    apply hole
    apply feasible_reach_positive_within hq (qfree_sub incl X.free) small (extendWeight X.V w) _ _ y.property a.property
    · simpa [extendWeight_on] using pos
    · intro k hk; rw [extendWeight_on X.V w ⟨k,hk⟩]; exact wn _
    · intro k hk; rw [mass_extendWeight,wm,row_extendWeight q E X.V w ⟨k,hk⟩]; exact wr _
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  let W := fun i => (w i:ℝ)
  let D := realMatrix q X.D X.V
  let J := realMatrix q E X.V
  have mass : ∑i,W i=1 := by dsimp [W]; exact_mod_cast wm
  have nn (i) : 0≤W i := by dsimp [W]; exact_mod_cast wn i
  have sub (i j : X.V) : J i j≤D i j := realMatrix_mono_graph (fun u _ v _ => incl u v) i j
  have old (i : X.V) : 1≤(J *ᵥ W) i := by
    change (1:ℝ)≤∑j,(S i j:ℝ)*(w j:ℝ)
    exact_mod_cast wr i
  have good (i : X.V) : 0≤(excess D *ᵥ W) i := by
    rw [mulVec_excess,mass,sub_nonneg]
    exact (old i).trans (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (sub i j) (nn j)))
  have live : W≠0 := by intro eq; rw [eq] at mass; simp at mass
  have zero : W a=0 := by simp [W,wa]
  obtain ⟨t,ht,_,ray⟩ := InverseOffDiagonal.single_ray inv (fun _ _ ne => InverseOffDiagonal.graph_positive hq inv ne)
    W live good zero
  have pos (i) (ne : i≠a) : 0<W i := (ray i) ▸ mul_pos ht (InverseOffDiagonal.graph_positive hq inv ne)
  have recover : H *ᵥ (excess D *ᵥ W)=W := by
    rw [Matrix.mulVec_mulVec,mul_eq_one_comm.mp inv.right,Matrix.one_mulVec]
  have exactRow (i) (ne : i≠a) : (D *ᵥ W) i=1 := by
    have cap := single_le_sum (s:=univ) (f:=fun j => H a j*(excess D *ᵥ W) j)
      (fun j _ => mul_nonneg (inv.nonneg a j) (good j)) (mem_univ i)
    change _≤(H *ᵥ (excess D *ᵥ W)) a at cap
    rw [recover,zero] at cap
    have hi := le_antisymm (nonpos_of_mul_nonpos_right cap (InverseOffDiagonal.graph_positive hq inv ne.symm)) (good i)
    rwa [mulVec_excess,mass,sub_eq_zero] at hi
  refine ⟨w,wn,wm,wa,fun i ne => ⟨?_,?_⟩,?_⟩
  · exact_mod_cast (show (0:ℝ)<w i from pos i ne)
  · have eq := exactRow i ne
    change (∑j,((WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D X.V) i j:ℚ):ℝ)*(w j:ℝ))=1 at eq
    change (∑j,WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D X.V) i j*w j)=1
    exact_mod_cast eq
  · intro i j edge off
    by_contra! both
    have gain : J i j<D i j := by
      dsimp [J,D]; simp [realMatrix_entry,edge,off,show 0<q by omega]
    have more : (J *ᵥ W) i<(D *ᵥ W) i := sum_lt_sum
      (fun k _ => mul_le_mul_of_nonneg_right (sub i k) (nn k))
      ⟨j,mem_univ _,mul_lt_mul_of_pos_right gain (pos j both.2)⟩
    rw [exactRow i both.1] at more
    exact more.not_ge (old i)

/-- On a stopped single-arc child every missing native arc of the original
spanning union enters or leaves its one exceptional tail. -/
theorem single_data {q n} (X : Model q n) (hq : 2≤q)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card)
    {a b : X.V} (first : Fresh X F (a,b))
    : (∀i j,insertArc (graph X.D F) a b i j=true → X.D i j=true) ∧
      (a:ℕ)∉ball (insertArc (graph X.D F) a b) X.V b q := by
  let E := graph X.D F
  let J := insertArc E a b
  have old {i j} (ed : E i j=true) : X.D i j=true := by
    obtain ⟨A,m⟩ := active.mp ed
    exact (mem_col.mp m).2.2.2
  have incl {i j} (ed : J i j=true) : X.D i j=true := by
    by_cases pair : i=(a:ℕ) ∧ j=(b:ℕ)
    · exact pair.1 ▸ pair.2 ▸ first.2.2.1
    exact old (by simpa [J,insertArc,pair] using ed)
  have lift {u v k} (path : Walk J X.V u v k) :
      Walk (SharedArcCover.onStars X.D (graph X.D F) {a.val} ∅) X.V u v k := by
    induction path with
    | refl => exact .refl _
    | @step i j _ _ hv edge _ ih =>
      apply Walk.step hv _ ih
      by_cases h : i=(a:ℕ)
      · have orig := incl edge
        simpa [SharedArcCover.onStars,h] using orig
      · have orig : E i j=true := by simpa [J,insertArc,h] using edge
        simpa [SharedArcCover.onStars,h] using orig
  have miss : (a:ℕ)∉ball J X.V b q := by
    intro ret
    obtain ⟨_,k,le,path⟩ := mem_ball.mp ret
    apply SharedArcCover.no_return X hq step least {a.val} ∅ (by simpa using multi) first (by simp)
    exact mem_ball.mpr ⟨a.property,k,le,lift path⟩
  exact ⟨fun _ _ e => incl e,miss⟩

theorem single_center {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card)
    {a b : X.V} (first : Fresh X F (a,b))
    (survives : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∀f : SharedArcFlatCut.Missing X F,f.val.1=a ∨ f.val.2=a := by
  let J := insertArc (graph X.D F) a b
  obtain ⟨incl,miss⟩ := single_data X hq step least multi first
  obtain ⟨_,_,_,_,_,center⟩ := one_hole X hq small J incl a b miss survives
  intro f
  by_cases atA : f.val.1=a
  · exact Or.inl atA
  · have ne : (f.val.1:ℕ)≠(a:ℕ) := fun e => atA (Subtype.ext e)
    exact center _ _ f.property.1 (by simpa [J,insertArc,ne] using f.property.2)


/-- Three usable exits on the selected family: the descent proof, a
negative old tensor entry, or a winning finite loop test on a real boundary. -/
def ProgressAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ)
    (H : Matrix X.V X.V ℝ) (p : ℕ→ℚ) (c : ℚ) : Prop :=
  SharedArcFlatArithmetic.ProgressAt X F B H p c ∨
    ∃M,Boundary X F M ∧ SharedArcCompression.winning X F B M

theorem blocks {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {F B H p c} (step : Boundary X F B)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (prior : ¬SharedArcFlatArithmetic.ProgressAt X F B H p c) : ¬ProgressAt X F B H p c := by
  rintro (done|⟨M,bm,win⟩)
  · exact prior done
  · exact stop M bm ((SharedArcCompression.winning_iff X small step (stop B step) M).mp win)

def Law {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → SmallRow q (graph X.D F) X.V →
    Boundary X F B → (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) →
    ∀H : Matrix X.V X.V ℝ,FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H →
    (∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a) →
    ∀p : ℕ→ℚ,∀c : ℚ,1<c → (∀v∈X.V,0<p v) → mass X.V p=1 →
    (∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c) → ProgressAt X F B H p c

/-- A single general supplier of any of these exits suffices for literal CH. -/
theorem ch_of_exits (law : ∀q n,∀X : Model q n,2≤q → SmallerSmallRow q X.V.card → Law X) :
    CH.CaccettaHaggkvistConjecture := by
  apply SharedArcInduction.ch_of_extension
  intro q n X hq small
  exfalso
  classical
  obtain ⟨u,uv⟩ := X.live
  obtain ⟨C,_,cc,_,_,_,_⟩ := ShortestReturnCertificate.on_model X hq uv
  have cf : C∈family X := mem_filter.mpr ⟨mem_powerset.mpr cc.sub,cc⟩
  obtain ⟨F,built,sub,_,spans,weak,_,next,stop⟩ := SharedArcBarrier.on_source X hq small cf
  obtain ⟨B,step,least,p,c,high,pos,pm,cols,compare⟩ := SharedArcPacketDescent.terminal X hq small next
    (fun M bm => (stop M bm).1)
  obtain ⟨H,inv,charge⟩ := SharedArcMinimalPacket.charges X hq small weak step least (stop B step).1
  have old := SharedArcPacketReturns.blocks_exit X hq small step least inv charge (fun M bm => (stop M bm).1)
  have stopped := SharedArcPacketDescent.blocks_progress (p:=p) (c:=c) X old (by
    intro M bm sz cap v vv
    obtain ⟨_,_,_,_,_,_,_,_,_,flat⟩ := compare M bm sz
    exact ((flat cap).2 v vv).1)
  exact blocks X small step (fun M bm => (stop M bm).1) (SharedArcFlatArithmetic.blocks X hq small stopped)
    (law q n X hq small C F B built sub spans weak step least H inv charge p c high pos pm cols)

#print axioms ch_of_exits

/-- The shared graph away from the exceptional label is a saturated,
positive, exact unit core on a strictly smaller support. Its order fixes
the native support residue modulo the full (possibly composite) cutoff. -/
theorem puncture {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (E : CH.Digraph) (incl : ∀i j,E i j=true → X.D i j=true) (a y : X.V)
    (hole : (a:ℕ)∉ball E X.V y q) (survives : ¬SharedArcReachMargin.StrictColumns q E X.V) :
    let U := X.V.erase a.val
    BRsub.Sat q X.D U ∧ (X.V.card : ZMod q)=2 ∧
    (∀i∈U,∀j∈U,E i j=X.D i j) ∧
    ∃z : ℕ→ℚ,(∀i∈U,0<z i) ∧ mass U z=1 ∧ ∀i∈U,WeightedSD.row q X.D U z i=1 := by
  classical
  intro U
  obtain ⟨w,_,wm,wa,positive,center⟩ := one_hole X hq small E incl a y hole survives
  let z := extendWeight X.V w
  have za : z a=0 := (extendWeight_on X.V w a).trans wa
  have total : mass U z=1 := by
    have all := mass_extendWeight X.V w
    rw [wm] at all
    have e := sum_erase_add X.V z a.property
    rw [za,add_zero] at e
    exact e.trans all
  have pos (i) (hi : i∈U) : 0<z i := by
    obtain ⟨diff,iv⟩ := mem_erase.mp hi
    change 0<extendWeight X.V w i
    rw [extendWeight_on X.V w ⟨i,iv⟩]
    exact (positive ⟨i,iv⟩ (fun e => diff (congrArg Subtype.val e))).1
  have rows (i) (hi : i∈U) : WeightedSD.row q X.D U z i=1 := by
    obtain ⟨diff,iv⟩ := mem_erase.mp hi
    have e := (row_extendWeight q X.D X.V w ⟨i,iv⟩).trans
      (positive ⟨i,iv⟩ (fun e => diff (congrArg Subtype.val e))).2
    change z i+q*outW X.D X.V z i=1 at e
    rwa [outW_erase a.property,za,ite_self,add_zero] at e
  have smaller : U.card<X.V.card := card_erase_lt_of_mem a.property
  have free := X.free.mono_set (erase_subset a.val X.V)
  have weak (i) (hi : i∈U) : mass U z≤WeightedSD.row q X.D U z i := by rw [total,rows i hi]
  have sat : BRsub.Sat q X.D U := by
    intro v vv u uv missing
    by_contra no
    let u' : U := ⟨u,uv⟩
    let v' : U := ⟨v,vv⟩
    have safe := qfree_insertArc free u' v' no
    exact positive_feasible_extension_not_smallRow (D:=X.D) hq
      (fun i _ j _ h => insertArc_mono X.D u v i j h) z pos weak uv vv missing (by simp [insertArc])
      (small _ U smaller safe)
  have live : U.Nonempty := by
    by_contra! empty
    rw [empty] at total
    simp [mass] at total
  have modU := SmallerSmallRow.positive_child_card_mod hq small smaller free z pos live weak
  have size : U.card+1=X.V.card := card_erase_add_one a.property
  have modV := congrArg (fun m : ℕ => (m:ZMod q)) size
  push_cast at modV
  rw [modU] at modV
  refine ⟨sat,by rw [←modV]; norm_num,?_,z,pos,total,rows⟩
  intro i hi j hj
  apply Bool.eq_iff_iff.mpr
  refine ⟨incl i j,fun ed => ?_⟩
  by_contra off
  obtain ⟨ia,iv⟩ := mem_erase.mp hi
  obtain ⟨ja,jv⟩ := mem_erase.mp hj
  rcases center ⟨i,iv⟩ ⟨j,jv⟩ ed (Bool.eq_false_iff.mpr off) with ai|aj
  · exact ia (congrArg Subtype.val ai)
  · exact ja (congrArg Subtype.val aj)

/-- The one-arc branch either has strict slack or has the explicit
single-pivot structure, support residue and saturated puncture. -/
theorem alternatives {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b)) :
    SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V ∨
    ((X.V.card:ZMod q)=2 ∧ BRsub.Sat q X.D (X.V.erase a.val) ∧
      (∀f : SharedArcFlatCut.Missing X F,f.val.1=a ∨ f.val.2=a) ∧
      ∃z : ℕ→ℚ,(∀i∈X.V.erase a.val,0<z i) ∧ mass (X.V.erase a.val) z=1 ∧
        ∀i∈X.V.erase a.val,WeightedSD.row q X.D (X.V.erase a.val) z i=1) := by
  classical
  apply or_iff_not_imp_left.mpr
  intro no
  obtain ⟨incl,miss⟩ := single_data X hq step least multi edge
  obtain ⟨sat,residue,_,weights⟩ := puncture X hq small _ incl a b miss no
  exact ⟨residue,sat,single_center X hq small step least multi edge no,weights⟩


/-- The head b classifies all parents of the exceptional vertex a. An old
parent points to b, and a new parent does not. The test is on native labels. -/
theorem classify_parents {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    (t : X.V) (parent : X.D t a=true) : graph X.D F t a=true ↔ X.D t b=true := by
  let J := insertArc (graph X.D F) a b
  let U := X.V.erase a.val
  obtain ⟨incl,miss⟩ := single_data X hq step least multi edge
  obtain ⟨sat,_,agree,_⟩ := puncture X hq small J incl a b miss no
  have ab : X.D a b=true := edge.2.2.1
  have ta : t≠a := by intro h; subst t; exact loopfree X.free (by omega) a.property parent
  have ba : b≠a := by intro h; subst b; exact loopfree X.free (by omega) a.property ab
  have offA (k : X.V) (ne : k≠a) : k.val∈U :=
    mem_erase.mpr ⟨fun e => ne (Subtype.ext e),k.property⟩
  constructor
  · intro old
    by_contra missing
    obtain ⟨_,l,le,path⟩ := mem_ball.mp (sat _ (offA b ba) _ (offA t ta) missing)
    have lift {u v k} (path : Walk X.D U u v k) (uv : u∈U) : Walk J X.V u v k := by
      induction path with
      | refl => exact .refl _
      | @step x y _ _ yy xy _ ih =>
        exact .step (mem_of_mem_erase yy) ((agree x uv y yy).trans xy) (ih yy)
    have final := (lift path (offA b ba)).snoc a.property (insertArc_mono (graph X.D F) a b t a old)
    exact miss (mem_ball.mpr ⟨a.property,l+1,by omega,final⟩)
  · intro tb
    by_contra missing
    have f : Fresh X F (t,a) := ⟨t.property,a.property,parent,Bool.eq_false_iff.mpr missing⟩
    obtain ⟨l,m,len,path,_⟩ := SharedArcSingleCorridor.corridor X hq small step least multi edge no f ta.symm
    have lift {i j k} (p : Walk (graph X.D F) X.V i j k) : Walk X.D X.V i j k := by
      induction p with
      | refl => exact .refl _
      | step hv ed _ ih =>
        obtain ⟨A,hit⟩ := active.mp ed
        exact .step hv (mem_col.mp hit).2.2.2 ih
    exact X.free t (l+1) (by omega) (by omega) (.step b.property tb (lift path))

#print axioms classify_parents

#print axioms alternatives

#print axioms puncture

#print axioms one_hole
#print axioms single_center
end LeanCH.BR.Closure.SharedArcPivot
