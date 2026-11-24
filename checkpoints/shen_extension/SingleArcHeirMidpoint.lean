import checkpoints.shen_extension.SingleArcResidualSource

namespace LeanCH.BR.Closure.SingleArcHeirMidpoint
open Finset BRq2 BRq3 BR45 BRsub WeightedSD StrictFlatSubsetMerge SingleArcResidualSource
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

/-- In a saturated host an heir points to all the other children of its root. -/
theorem first_child {q : ℕ} (hq : 2≤q) {D : CH.Digraph} {V : Finset ℕ}
    (free : QFree D V q) (sat : Sat q D V) {a v y : ℕ} (ha : a∈V) (hv : v∈V) (hy : y∈V)
    (par : ∀i∈V,i≠a → D i v=true → D i a=true) (yv : y≠v) (ay : D a y=true) : D v y=true := by
  by_contra off
  obtain ⟨_,m,short,path⟩ := mem_ball.mp (sat y hy v hv off)
  cases m with
  | zero => exact yv (walk_zero path)
  | succ m =>
    obtain ⟨t,pre,_,tv⟩ := path.unsnoc
    by_cases eq : t=a
    · subst t
      exact free a (m+1) (by omega) (by omega) (.step hy ay pre)
    · have tV : t∈V := pre.end_mem_or.elim (fun e=>e ▸ hy) id
      exact free a (m+1+1) (by omega) (by omega) (.step hy ay (pre.snoc ha (par t tV eq tv)))

private theorem midpoint_price {q : ℕ} (hq : 2≤q) {D E : CH.Digraph} {V : Finset ℕ}
    (free : QFree D V q) (sat : Sat q D V) (sub : ∀i j,E i j=true → D i j=true)
    {a b v : ℕ} (ha : a∈V) (hb : b∈V) (hv : v∈V) (ab : D a b=true) (off : E a b=false)
    (only : ∀i∈V,∀j∈V,D i j=true → E i j=true ∨ i=a ∧ j=b)
    (av : E a v=true) (par : ∀i∈V,i≠a → E i v=true → E i a=true)
    {w : ℕ→ℚ} (pos : ∀i∈V,0<w i) (rowA : WeightedSD.row q E V w a=mass V w)
    (cuts : ∀S⊆V,2≤S.card → S≠V → mass S w+q*mass (common D V S) w<mass V w) :
    E v b=true ∧ (∀y∈V,y≠v → E a y=true → E v y=true) ∧ (q:ℚ)*w b<((q:ℚ)-1)*w v := by
  have va : v≠a := fun eq=>loopfree free (by omega) ha (eq ▸ sub a v av)
  have bv : b≠v := fun eq=>Bool.noConfusion (off.symm.trans (eq ▸ av))
  have ba : b≠a := fun eq=>loopfree free (by omega) ha (eq ▸ ab)
  have hostPar (i) (iv : i∈V) (ne : i≠a) (ivEdge : D i v=true) : D i a=true :=
    sub i a (par i iv ne ((only i iv v hv ivEdge).resolve_right (fun h=>ne h.1)))
  have first (y) (hy : y∈V) (ne : y≠v) (ay : D a y=true) : E v y=true :=
    (only v hv y hy (first_child hq free sat ha hv hy hostPar ne ay)).resolve_right (fun h=>va h.1)
  have vb := first b hb bv ab
  refine ⟨vb,fun y hy ne ay=>first y hy ne (sub _ _ ay),?_⟩
  let N := outN E V a
  have vN : v∈N := mem_outN.mpr ⟨hv,av⟩
  have bN : b∉N.erase v := fun h=>Bool.noConfusion (off.symm.trans (mem_outN.mp (mem_of_mem_erase h)).2)
  have inc : insert b (N.erase v)⊆common D V {a,v} := by
    intro y hit
    have data : y∈V ∧ D a y=true ∧ D v y=true := by
      rcases mem_insert.mp hit with rfl | yn
      · exact ⟨hb,ab,sub _ _ vb⟩
      · obtain ⟨ne,mem⟩ := mem_erase.mp yn
        obtain ⟨yv,edge⟩ := mem_outN.mp mem
        exact ⟨yv,sub _ _ edge,sub _ _ (first _ yv ne (sub _ _ edge))⟩
    exact mem_filter.mpr ⟨data.1,by simpa using data.2⟩
  have massLe := mass_mono inc (fun i hi=>(pos i (mem_filter.mp hi).1).le)
  have ins : mass (insert b (N.erase v)) w=w b+mass (N.erase v) w := sum_insert bN
  rw [ins] at massLe
  have pairSub : ({a,v}:Finset ℕ)⊆V := insert_subset_iff.mpr ⟨ha,singleton_subset_iff.mpr hv⟩
  have proper : ({a,v}:Finset ℕ)≠V := fun eq=>(show b∉({a,v}:Finset ℕ) by simp [ba,bv]) (eq ▸ hb)
  have cut := cuts {a,v} pairSub (by simp [card_pair va.symm]) proper
  have pairMass : mass {a,v} w=w a+w v := sum_pair va.symm
  have sumN : w v+mass (N.erase v) w=mass N w := add_sum_erase N w vN
  rw [pairMass] at cut
  rw [WeightedSD.row,outW_eq_mass] at rowA
  change w a+q*mass N w=mass V w at rowA
  rw [←sumN,mul_add] at rowA
  have price := mul_le_mul_of_nonneg_left massLe (Nat.cast_nonneg (α:=ℚ) q)
  rw [mul_add] at price
  linarith only [price,cut,rowA]

def MidpointOrWalk (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (a b : ℕ) : Prop :=
  let U := ancestors E V a b
  (∃v∈U,E a v=true ∧ E v b=true ∧ (∀i∈V,i≠a → E i v=true → E i a=true) ∧
    (∀y∈V,y≠v → E a y=true → E v y=true) ∧ (q:ℚ)*w b<((q:ℚ)-1)*w v) ∨
    ∃x∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk E U x x m

/-- Without a sufficiently heavy midpoint, an entire long old walk lies
among the residual ancestors, imposing a lower bound on the support size. -/
theorem cycle_of_no_heavy_midpoint {q : ℕ} (hq : 1≤q) {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q) {a b : ℕ} (av : a∈V) {w : ℕ→ℚ}
    (alt : MidpointOrWalk q E V w a b)
    (light : ∀v∈V,E a v=true → E v b=true → ((q:ℚ)-1)*w v≤(q:ℚ)*w b) :
    let U := ancestors E V a b
    (inN E V a).card+q+2≤V.card ∧ ∃x∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk E U x x m := by
  classical
  intro U
  have sub : U⊆nonParentSet E V a := filter_subset _ _
  rcases alt with ⟨v,vu,head,parent,_,_,price⟩ | cycle
  · exact (price.not_ge (light v (mem_nonParentSet.mp (sub vu)).1 head parent)).elim
  · refine ⟨?_,cycle⟩
    obtain ⟨_,_,m,lo,hi,_⟩ := cycle
    change m≤U.card at hi
    have bound := card_le_card sub
    have setSub : insert a (inN E V a)⊆V := insert_subset_iff.mpr ⟨av,filter_subset _ _⟩
    have nmem : a∉inN E V a := fun h=>loopfree free hq av (mem_inN.mp h).2
    change U.card≤(V \ insert a (inN E V a)).card at bound
    rw [card_sdiff_of_subset setSub,card_insert_of_notMem nmem] at bound
    omega

theorem singleton {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) :
    let E := graph X.D F
    MidpointOrWalk q E X.V w f.val.1 f.val.2 ∧ MidpointOrWalk q (fun x y=>E y x) X.V p f.val.2 f.val.1 := by
  classical
  intro E
  let a := f.val.1
  let b := f.val.2
  have old (i j) (e : E i j=true) : X.D i j=true := (mem_col.mp (active.mp e).choose_spec).2.2.2
  have only (i) (iv : i∈X.V) (j) (jv : j∈X.V) (ij : X.D i j=true) : E i j=true ∨ i=a ∧ j=b := by
    by_cases h : E i j=true
    · exact Or.inl h
    · let g : SharedArcFlatCut.Missing X F := ⟨(⟨i,iv⟩,⟨j,jv⟩),ij,Bool.eq_false_iff.mpr h⟩
      exact Or.inr ⟨congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.1.val) (single g),
        congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.2.val) (single g)⟩
  have pm := HeirExit.mass_col_of_flat wm wr pc
  have bounds := @StrictFlatSubsetMerge.host q n X hq small F w p pos
    (fun i hi=>by rw [wm,wr i hi]) (fun i hi=>by rw [pm,pc i hi])
  obtain ⟨tail,head⟩ := both_ends X hq small F f pos wm wr pc
  constructor
  · rcases tail with ⟨v,vu,av,par,_⟩ | cycle
    · have vv := (mem_nonParentSet.mp (mem_filter.mp vu).1).1
      obtain ⟨vb,first,price⟩ := midpoint_price hq X.free X.sat old a.property b.property vv f.property.1 f.property.2
        only av par (fun i hi=>(pos i hi).1) ((wr a a.property).trans wm.symm) (fun _ s k h=>(bounds s k h).1)
      exact Or.inl ⟨v,vu,av,vb,par,first,price⟩
    · exact Or.inr cycle
  · rcases head with ⟨v,vu,bv,par,_⟩ | cycle
    · have vv := (mem_nonParentSet.mp (mem_filter.mp vu).1).1
      obtain ⟨va,first,price⟩ := midpoint_price (E:=fun i j=>E j i) hq X.free.reverse (SerialChain.sat_reverse X.sat)
        (fun i j=>old j i) b.property a.property vv f.property.1 f.property.2
        (fun i iv j jv ij=>(only j jv i iv ij).imp_right And.symm) bv par (fun i hi=>(pos i hi).2)
        ((pc b b.property).trans pm.symm) (fun _ s k h=>(bounds s k h).2)
      exact Or.inl ⟨v,vu,bv,va,par,first,price⟩
    · exact Or.inr cycle

end LeanCH.BR.Closure.SingleArcHeirMidpoint
#print axioms LeanCH.BR.Closure.SingleArcHeirMidpoint.first_child
#print axioms LeanCH.BR.Closure.SingleArcHeirMidpoint.cycle_of_no_heavy_midpoint
#print axioms LeanCH.BR.Closure.SingleArcHeirMidpoint.singleton
