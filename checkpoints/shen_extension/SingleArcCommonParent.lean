import checkpoints.shen_extension.SingleArcCommonTilt
import checkpoints.shen_extension.SingletonSecondNeighbors

namespace LeanCH.BR.Closure.SingleArcCommonParent
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ShenCycleSuccessor
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SingleArcCycleBalance SingleArcCycleSlope SingleArcCommonTilt

/-- A row hitting both the tail and midpoint fails the exterior
inequality at every admissible parameter, regardless of its other hits. -/
theorem margin {q E V C} (hq : 2≤q) (free : QFree E V q) (cy : Cycle E V q C)
    (a v : C) (av : E a v=true) (x : ℝ) (heavy : 1<((q:ℝ)-1)*x)
    (N : Finset C) (an : a∈N) (vn : v∈N) (t : ℝ) (one : 1≤t) :
    ((q:ℝ)+1)*score q N (tiltedPrices q E a v t x) <
      -((q:ℝ)+t)*min 1 (((q:ℝ)-1)*x-1) := by
  obtain ⟨s,vs⟩ := SingleArcCycleSparse.successor cy v
  obtain ⟨r,sr⟩ := SingleArcCycleSparse.successor cy s
  let z := tiltedPrices q E a v 1 x
  have va : v≠a := by rintro rfl; exact loopfree free (by omega) (cy.sub v.property) av
  have sv : s≠v := by rintro rfl; exact loopfree free (by omega) (cy.sub s.property) vs
  have sa : s≠a := by rintro rfl; exact free s 2 (by omega) hq (.step (cy.sub v.property) av (.step (cy.sub s.property) vs (.refl _)))
  obtain ⟨_,_,_,others,tail,mid⟩ := SingleArcCycleSparse.sparse hq free cy a v s r av vs sr x heavy
  change z a+(q:ℝ)*z v-∑k,z k= -1 at tail
  change z v+(q:ℝ)*z s-∑k,z k=1 at mid
  have zv : z v= -x := by simp [z,tiltedPrices]
  have za : z a<0 := others a sa.symm
  have qtwo : (2:ℝ)≤q := by exact_mod_cast hq
  have qp : (0:ℝ)<q := by linarith
  have pair : ({a,v}:Finset C)⊆N := insert_subset_iff.mpr ⟨an,singleton_subset_iff.mpr vn⟩
  let gap := min 1 (((q:ℝ)-1)*x-1)
  have baseline : score q N z < -gap := by
    unfold score
    by_cases sn : s∈N
    · have triple : insert s {a,v}⊆N := insert_subset sn pair
      have bound := sum_le_sum_of_subset_of_nonpos (f:=z) triple (fun j _ off=>
        (others j (fun e=>off (mem_insert.mpr (Or.inl e)))).le)
      rw [sum_insert (by simp [sa,sv]),sum_pair va.symm] at bound
      have gapBound : gap≤((q:ℝ)-1)*x-1 := min_le_right .. 
      nlinarith only [mul_le_mul_of_nonneg_left bound qp.le,mid,tail,zv,gapBound,mul_neg_of_pos_of_neg qp za]
    · have bound := sum_le_sum_of_subset_of_nonpos (f:=z) pair (fun j jn _=>
        (others j (fun e=>sn (e ▸ jn))).le)
      rw [sum_pair va.symm] at bound
      have gapBound : gap≤1 := min_le_left ..
      nlinarith only [mul_le_mul_of_nonneg_left bound qp.le,tail,gapBound,mul_neg_of_pos_of_neg
        (show 0<(q:ℝ)-1 by linarith) za]
  have many := card_le_card pair
  rw [card_pair va.symm] at many
  have neg := (signs hq heavy N v).2.2 many
  have eq := score_change hq cy a v av t x N
  have prod := mul_lt_mul_of_pos_left baseline (show 0<(q:ℝ)+t by linarith)
  have dec := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr one) neg.le
  change ((q:ℝ)+1)*score q N (tiltedPrices q E a v t x)< -((q:ℝ)+t)*gap
  change ((q:ℝ)+1)*score q N (tiltedPrices q E a v t x)=((q:ℝ)+t)*score q N z+_ at eq
  linarith only [eq,prod,dec]

theorem veto {q E V C} (hq : 2≤q) (free : QFree E V q) (cy : Cycle E V q C)
    (a v : C) (av : E a v=true) (x : ℝ) (heavy : 1<((q:ℝ)-1)*x)
    (N : Finset C) (an : a∈N) (vn : v∈N) (t : ℝ) (one : 1≤t) :
    score q N (tiltedPrices q E a v t x)<0 := by
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have gap : 0<min 1 (((q:ℝ)-1)*x-1) := lt_min zero_lt_one (sub_pos.mpr heavy)
  have neg := mul_neg_of_neg_of_pos (show -((q:ℝ)+t)<0 by linarith) gap
  exact neg_of_mul_neg_right ((margin hq free cy a v av x heavy N an vn t one).trans neg) (by linarith)

private theorem trim {q E V v j i m l} (free : QFree E V q) (pre : Walk E V v j l)
    (w : Walk E V j i m) (room : l+m≤q) : Walk E (V \ {v}) j i m := by
  induction w generalizing l with
  | refl => exact .refl _
  | @step j k i m kv jk rest ih =>
    have next := pre.snoc kv jk
    have ne : k≠v := by rintro rfl; exact free _ (l+1) (by omega) (by omega) next
    exact .step (mem_sdiff.mpr ⟨kv,by simpa using ne⟩) jk (ih next (by omega))

/-- One native separating parent vetoes *every* old marked cycle and
every t ≥ 1. It also belongs to an old boundary cycle through v→b
that omits a. The conclusion uses no induction hypothesis on smaller graphs. -/
theorem native {q n} (X : Model q n) (hq : 2≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (v : X.V) (av : graph X.D F f.val.1 v=true) (vb : graph X.D F v f.val.2=true)
    (heir : ∀i∈X.V,i≠f.val.1.val → graph X.D F i v=true → graph X.D F i f.val.1=true)
    (x : ℝ) (heavy : 1<((q:ℝ)-1)*x) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    ∃i : X.V,E i a=true ∧ E i v=true ∧ X.D i b=false ∧
      (3≤q → let A := SingletonSecondNeighbors.adj E X.V
             i∈BalancedSecondNeighborhood.inN A v ∩ BalancedSecondNeighborhood.nonAdj A b ∧
             BalancedSecondNeighborhood.isP2 A i b) ∧
      (∃K,Cycle E X.V q K ∧ i.val∈K ∧ v.val∈K ∧ b.val∈K ∧ a.val∉K) ∧
      ∀C,Cycle E X.V q C → ∀(ac : a.val∈C) (vc : v.val∈C),i.val∉C ∧
        ∀t : ℝ,1≤t → score q (hits E C i) (tiltedPrices q E ⟨a,ac⟩ ⟨v,vc⟩ t x)<0 := by
  intro E a b
  have free := PrivateArcEndpoints.graph_free X F
  have sub (j k) (ed : E j k=true) : X.D j k=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have only (j) (jv : j∈X.V) (k) (kv : k∈X.V) (ed : X.D j k=true) : E j k=true ∨ j=a.val ∧ k=b.val := by
    by_cases old : E j k=true
    · exact Or.inl old
    · let g : SharedArcFlatCut.Missing X F := ⟨(⟨j,jv⟩,⟨k,kv⟩),ed,Bool.eq_false_iff.mpr old⟩
      exact Or.inr ⟨congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.1.val) (single g),
        congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.2.val) (single g)⟩
  have bv : b.val≠v.val := fun e=>Bool.noConfusion (f.property.2.symm.trans (e ▸ av))
  have va : v.val≠a.val := fun e=>loopfree free (by omega) a.property (e ▸ av)
  obtain ⟨i,iv,toV,miss⟩ := X.separated v v.property b b.property bv
  have ia : i≠a.val := fun eq=>Bool.noConfusion (miss.symm.trans (eq ▸ f.property.1))
  have iv' := (only i iv v v.property toV).resolve_right (fun h=>ia h.1)
  have ia' := heir i iv ia iv'
  have ballEq := (SingleArcReturnProfile.balls (by omega : 1≤q) X.free X.sat sub only b.property f.property.1).2
  have hit : i∈ball E X.V b (q-1) := by
    rw [ballEq]; exact mem_sdiff.mpr ⟨iv,fun p=>Bool.noConfusion (miss.symm.trans (mem_inN.mp p).2)⟩
  obtain ⟨_,m,le,path⟩ := mem_ball.mp hit
  have floor : q<m+2 := by
    by_contra! low
    exact free i (m+1+1) (by omega) (by omega) (.step v.property iv' (.step b.property vb path))
  have path' := trim free (Walk.step b.property vb (.refl _)) path (by omega)
  obtain ⟨K,cycleK,ik,vk,bk⟩ := marked_cycle hq free v.property b.property iv' vb ((by omega : m=q-1) ▸ path')
  have noA : a.val∉K := by
    intro ak
    exact va (card_le_one.mp (cycleK.heads i ik).le _ (mem_outN.mpr ⟨vk,iv'⟩) _ (mem_outN.mpr ⟨ak,ia'⟩))
  refine ⟨⟨i,iv⟩,ia',iv',miss,?_,⟨K,cycleK,ik,vk,bk,noA⟩,?_⟩
  · intro three
    let k : X.V := ⟨i,iv⟩
    let A := SingletonSecondNeighbors.adj E X.V
    have f3 := SingletonSecondNeighbors.three_free three free
    have off : ¬A k b := fun ed=>Bool.noConfusion (miss.symm.trans (sub i b ed))
    have back : ¬A b k := f3.2 k v b iv' vb
    have ne : k≠b := fun eq=>f3.1.2 v b vb (eq ▸ iv')
    exact ⟨mem_inter.mpr ⟨BalancedSecondNeighborhood.mem_inN.mpr iv',
      BalancedSecondNeighborhood.mem_nonAdj.mpr ⟨ne,back,off⟩⟩,ne.symm,off,back,v,iv',vb⟩
  ·
    intro C cy ac vc
    have outside : i∉C := by
      intro ic
      have reg : (inN E C v).card=1 := cy.incoming v vc
      exact ia (card_le_one.mp reg.le _ (mem_inN.mpr ⟨ic,iv'⟩) _ (mem_inN.mpr ⟨ac,av⟩))
    exact ⟨outside,fun t t1=>veto hq free cy ⟨a,ac⟩ ⟨v,vc⟩ av x heavy (hits E C i)
      (mem_filter.mpr ⟨mem_univ _,ia'⟩) (mem_filter.mpr ⟨mem_univ _,iv'⟩) t t1⟩

/-- The common parameter proposed for an old cycle through a→v. -/
def passes (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (a v : ℕ) (x : ℝ) : Prop :=
  ∃C,Cycle E V q C ∧ ∃(ac : a∈C) (vc : v∈C) (t : ℝ),1≤t ∧
    ∀i∈V \ C,0≤score q (hits E C i) (tiltedPrices q E ⟨a,ac⟩ ⟨v,vc⟩ t x)

theorem no_common {q n} (X : Model q n) (hq : 2≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (v : X.V) (av : graph X.D F f.val.1 v=true) (vb : graph X.D F v f.val.2=true)
    (heir : ∀i∈X.V,i≠f.val.1.val → graph X.D F i v=true → graph X.D F i f.val.1=true)
    (x : ℝ) (heavy : 1<((q:ℝ)-1)*x) : ¬passes q (graph X.D F) X.V f.val.1 v x := by
  obtain ⟨i,_,_,_,_,_,blocked⟩ := native X hq F f single v av vb heir x heavy
  rintro ⟨C,cy,ac,vc,t,one,pay⟩
  obtain ⟨off,neg⟩ := blocked C cy ac vc
  exact (neg t one).not_ge (pay i (mem_sdiff.mpr ⟨i.property,off⟩))

/-- Specialization to the flat singleton obtained by the capstone.
The heavy alternative has old marked cycles and none passes; the
other alternative carries the previous long residual ancestor walk. -/
theorem singleton {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let U := SingleArcResidualSource.ancestors E X.V a b
    (∃v : X.V,v.val∈U ∧ E a v=true ∧ E v b=true ∧
      (∃C,Cycle E X.V q C ∧ a.val∈C ∧ v.val∈C) ∧
      ¬passes q E X.V a v ((w v:ℝ)/((q:ℝ)*(w b:ℝ)))) ∨
    ∃i∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk E U i i m := by
  classical
  intro E a b U
  rcases (SingleArcHeirMidpoint.singleton X hq small F f single wp wm wr pc).1 with ⟨v,vu,av,vb,heir,_,heavy⟩|long
  · let k : X.V := ⟨v,(mem_nonParentSet.mp (mem_filter.mp vu).1).1⟩
    obtain ⟨_,_,_,C,cy,ac,vc,_,_⟩ := SingleArcCycleParents.supply X hq small F wp wm wr pc f single k av
    have den : 0<(q:ℝ)*(w b:ℝ) := mul_pos (by exact_mod_cast (by omega : 0<q))
      (by exact_mod_cast (wp b b.property).1)
    refine Or.inl ⟨k,vu,av,vb,⟨C,cy,ac,vc⟩,no_common X hq F f single k av vb heir _ ?_⟩
    rw [←mul_div_assoc,lt_div_iff₀ den,one_mul]
    exact_mod_cast heavy
  · exact Or.inr long

end LeanCH.BR.Closure.SingleArcCommonParent
#print axioms LeanCH.BR.Closure.SingleArcCommonParent.veto
#print axioms LeanCH.BR.Closure.SingleArcCommonParent.margin
#print axioms LeanCH.BR.Closure.SingleArcCommonParent.native
#print axioms LeanCH.BR.Closure.SingleArcCommonParent.no_common
#print axioms LeanCH.BR.Closure.SingleArcCommonParent.singleton
