import checkpoints.shen_extension.SingleArcCycleParents
import checkpoints.shen_extension.SingleArcCyclePrices

namespace LeanCH.BR.Closure.SingleArcCycleHead
open Finset BRq2 BRq3 BR45 BRsub WeightedSD FiniteCutInverse ShenCycleSuccessor
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SingleArcCyclePrices

private theorem unique_head {E : CH.Digraph} {V C : Finset ℕ} {q} (cy : Cycle E V q C)
    (i j k : C) (ij : E i j=true) (ik : E i k=true) : j=k := by
  apply Subtype.ext
  exact card_le_one.mp (cy.heads i i.property).le _ (mem_outN.mpr ⟨j.property,ij⟩)
    _ (mem_outN.mpr ⟨k.property,ik⟩)

/-- A common exterior child of two consecutive cycle vertices can
re-enter the old cycle only at the successor of the second vertex. -/
theorem ports {q} (hq : 2≤q) {E D : CH.Digraph} {V C : Finset ℕ}
    (free : QFree D V q) (sub : ∀i j,E i j=true → D i j=true) (cy : Cycle E V q C)
    (a v : C) (av : E a v=true) {y : ℕ} (yv : y∈V) (ay : D a y=true) (vy : D v y=true)
    (j : C) (yj : E y j=true) : E v j=true := by
  have old := qfree_sub sub free
  obtain ⟨low,upper,front,back⟩ := MandatoryExcursion.segments (by omega : 1≤q) old cy a.property j.property
  let d := MandatoryExcursion.span E V q a j
  change Walk E C a j d at front
  change Walk E C j a (q+1-d) at back
  change 1≤d at low
  change d≤q+1 at upper
  have atMost : d≤2 := by
    by_contra! big
    exact free a (q+1-d+1+1) (by omega) (by omega)
      (.step yv ay (.step (cy.sub j.property) (sub _ _ yj) ((walk_sub sub back).mono cy.sub)))
  have two : d=2 := by
    by_contra no
    have one : d=1 := by omega
    have aj := (walk_one (one ▸ front)).2
    obtain rfl := unique_head cy a j v aj av
    exact free j 2 (by omega) hq (.step yv vy (.step (cy.sub j.property) (sub _ _ yj) (.refl _)))
  have path : Walk E C a j 2 := two ▸ front
  obtain ⟨k,ak,kc,kj⟩ := path.unsnoc
  have eq := unique_head cy a ⟨k,(walk_one ak).1⟩ v (walk_one ak).2 av
  exact (congrArg Subtype.val eq) ▸ kj

private theorem row_value {q} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ} (cy : Cycle E V q C)
    (a v i j : C) (anchor : ℝ) (ij : E i j=true) :
    let z := prices (realMatrix q E C) a v anchor
    z i+(q:ℝ)*z j-∑k,z k=(if i=v then 1 else 0)-(if i=a then 1 else 0) := by
  intro z
  have eq := exterior_on hq cy a v anchor i
  have edges (k : C) : E i k=true ↔ k=j := ⟨fun h=>unique_head cy i k j h ij, fun h=>h ▸ ij⟩
  have diag (k : C) : i.val=k.val ↔ k=i := Subtype.ext_iff.symm.trans eq_comm
  simp only [SingleArcCyclePrices.exterior,show prices (realMatrix q E C) a v anchor=z from rfl,edges,diag,
    add_mul,sub_mul,ite_mul,zero_mul,one_mul,sum_sub_distrib,sum_add_distrib,sum_ite_eq',
    mem_univ,ite_true] at eq
  simp only [show (v=i)↔i=v from eq_comm,show (a=i)↔i=a from eq_comm] at eq
  linarith only [eq]

private theorem external_value {q} {E : CH.Digraph} {C : Finset ℕ}
    (a v : C) (anchor : ℝ) {y : ℕ} (outside : y∉C) :
    let z := prices (realMatrix q E C) a v anchor
    exterior q E a v anchor y=(∑j : C,if E y j=true then (q:ℝ)*z j else 0)-∑j,z j := by
  intro z
  have off (j : C) : y≠j.val := fun eq=>outside (eq ▸ j.property)
  simp only [SingleArcCyclePrices.exterior,off,ite_false,zero_add,sub_zero,add_zero,sub_mul,one_mul,
    ite_mul,zero_mul,sum_sub_distrib,z]

/-- Missing the cycle, or reaching it only at the midpoint's successor,
gives a strictly positive exterior price at a heavy midpoint. -/
theorem positive_of_ports {q} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ}
    (free : QFree E V q) (cy : Cycle E V q C) (a v : C) (av : E a v=true)
    {y : ℕ} (off : y∉C) (allowed : ∀j : C,E y j=true → E v j=true)
    (x : ℝ) (heavy : 1<((q:ℝ)-1)*x) : 0<exterior q E a v (-x) y := by
  let z := prices (realMatrix q E C) a v (-x)
  let mean := (∑k,z k)/((q:ℝ)+1)
  let h (k : C) := z k-mean
  have qpos : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have qtwo : (2:ℝ)≤q := by exact_mod_cast hq
  have total : ∑k,z k=((q:ℝ)+1)*mean := by dsimp [mean]; field_simp
  have recur (i j : C) (ed : E i j=true) : h i+(q:ℝ)*h j=(if i=v then 1 else 0)-(if i=a then 1 else 0) := by
    have eq := row_value hq cy a v i j (-x) ed
    change z i+_*z j-_= _ at eq
    dsimp [h]; linarith only [total,eq]
  have zval : z v= -x := by simp [z,prices]
  have neq : v≠a := by
    rintro rfl
    exact loopfree free (by omega) (cy.sub v.property) av
  have ext := external_value a v (-x) off (q:=q) (E:=E)
  change exterior q E a v (-x) y=(∑j : C,if E y j=true then (q:ℝ)*z j else 0)-∑j,z j at ext
  by_cases hit : ∃j : C,E y j=true
  · obtain ⟨j,yj⟩ := hit
    have vj := allowed j yj
    have edges (k : C) : E y k=true ↔ k=j := ⟨fun ek=>unique_head cy v k j (allowed k ek) vj,fun e=>e ▸ yj⟩
    simp only [edges,sum_ite_eq',mem_univ,ite_true] at ext
    have eq := row_value hq cy a v v j (-x) vj
    change z v+_*z j-_= _ at eq
    simp only [ite_true,if_neg neq,sub_zero] at eq
    have xp : 0<x := pos_of_mul_pos_right (by linarith only [heavy] : 0<((q:ℝ)-1)*x) (by linarith)
    linarith only [ext,eq,zval,xp]
  · push_neg at hit
    simp only [if_neg (hit _),sum_const_zero,zero_sub] at ext
    obtain ⟨k,_,mx⟩ := exists_max_image univ (fun j : C=>|h j|) ⟨v,mem_univ _⟩
    have regular : (inN E C k).card=1 := cy.incoming k k.property
    obtain ⟨i,hi⟩ := card_pos.mp (show 0<(inN E C k).card by omega)
    let t : C := ⟨i,(mem_inN.mp hi).1⟩
    have eq := recur t k (mem_inN.mp hi).2
    have lim : |h t+(q:ℝ)*h k|≤1 := by rw [eq]; split_ifs <;> norm_num
    have triangle := abs_sub_le (h t+(q:ℝ)*h k) 0 (h t)
    rw [add_sub_cancel_left,abs_mul,abs_of_pos qpos,sub_zero,zero_sub,abs_neg] at triangle
    have maxBound : ((q:ℝ)-1)*|h k|≤1 := by linarith only [triangle,lim,mx t (mem_univ _)]
    have hBound := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs (h v)) (mx v (mem_univ _))) (by linarith : 0≤(q:ℝ)-1)
    have negMean : mean<0 := by
      have hx : -h v<x := lt_of_mul_lt_mul_left (hBound.trans_lt (maxBound.trans_lt heavy)) (by linarith : 0≤(q:ℝ)-1)
      dsimp [h] at hx; linarith only [hx,zval]
    linarith only [ext,total,mul_neg_of_pos_of_neg (by linarith : 0<(q:ℝ)+1) negMean]

/-- At a heavy midpoint every old cycle has an exterior vertex of
negative price. That vertex hits the cycle away from the midpoint's
successor and cannot be a common child of the tail and midpoint. -/
theorem witness {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    (f : SharedArcFlatCut.Missing X F) (v : X.V) {C : Finset ℕ}
    (cy : Cycle (graph X.D F) X.V q C) (ac : f.val.1.val∈C) (vc : v.val∈C)
    (av : graph X.D F f.val.1 v=true)
    (heavy : (q:ℚ)*w f.val.2<((q:ℚ)-1)*w v) :
    let E := graph X.D F
    let x := (w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))
    ∃i : X.V,i.val∉C ∧ SingleArcCyclePrices.exterior q E ⟨f.val.1,ac⟩ ⟨v,vc⟩ (-x) i<0 ∧
      (∃j : C,E i j=true ∧ E v j=false) ∧ ¬(X.D f.val.1 i=true ∧ X.D v i=true) := by
  intro E x
  have sub (i j) (h : E i j=true) : X.D i j=true := (mem_col.mp (active.mp h).choose_spec).2.2.2
  have bc := SingleArcCycleParents.head_outside hq X.free sub cy ac vc av f.property.2 f.property.1
  have acc := account X hq F wp wm wr pc f v cy.sub ac vc bc
  let z (i : X.V) := SingleArcCyclePrices.exterior q E ⟨f.val.1,ac⟩ ⟨v,vc⟩ (-x) i
  let T := SharedArcFlatResponse.test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
  have anchor : -(w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))= -x := neg_div ..
  change T v v= -(∑i : X.V,T v i*SingleArcCyclePrices.exterior q E ⟨f.val.1,ac⟩ ⟨v,vc⟩
    (-(w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))) i) at acc
  rw [anchor] at acc
  change T v v= -(∑i : X.V,T v i*z i) at acc
  have tp (i : X.V) : 0<T v i := SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f v i
  have neg : ∃i : X.V,z i<0 := by
    by_contra! none
    have allPos := sum_nonneg (s:=univ) (fun (i : X.V) _=>mul_nonneg (tp i).le (none i))
    linarith only [tp v,acc,allPos]
  obtain ⟨i,zi⟩ := neg
  have off : i.val∉C := by
    intro ic
    exact zi.ne (exterior_on hq cy _ _ _ ⟨i,ic⟩)
  have denom : (0:ℝ)<(q:ℝ)*(w f.val.2:ℝ) := mul_pos (by exact_mod_cast (by omega : 0<q))
    (by exact_mod_cast (wp _ f.val.2.property).1)
  have heavyr : 1<((q:ℝ)-1)*x := by
    dsimp [x]; rw [←mul_div_assoc,lt_div_iff₀ denom,one_mul]
    exact_mod_cast heavy
  have bad : ¬∀j : C,E i j=true → E v j=true := fun h=>zi.not_gt
    (positive_of_ports hq (qfree_sub sub X.free) cy ⟨_,ac⟩ ⟨_,vc⟩ av off h x heavyr)
  push_neg at bad
  obtain ⟨j,ij,vj⟩ := bad
  exact ⟨i,off,zi,⟨j,ij,Bool.eq_false_iff.mpr vj⟩,fun h=>vj (ports hq X.free sub cy
    ⟨_,ac⟩ ⟨_,vc⟩ av i.property h.1 h.2 j ij)⟩

/-- On a native singleton either the previous long ancestor walk
survives, or every cycle through a supplied midpoint needs a negatively
priced label outside the entire native out-neighborhood of the tail. -/
theorem singleton {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let U := SingleArcResidualSource.ancestors E X.V a b
    (∃v : X.V,v.val∈U ∧ E a v=true ∧ E v b=true ∧ (∃C,Cycle E X.V q C ∧ a.val∈C ∧ v.val∈C) ∧
      ∀C,Cycle E X.V q C → ∀(ac : a.val∈C) (vc : v.val∈C),∃i : X.V,i.val∉C ∧ X.D a i=false ∧
        SingleArcCyclePrices.exterior q E ⟨a,ac⟩ ⟨v,vc⟩ (-((w v:ℝ)/((q:ℝ)*(w b:ℝ)))) i<0 ∧
        ∃j : C,E i j=true ∧ E v j=false) ∨ ∃x∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk E U x x m := by
  classical
  intro E a b U
  have alternatives := (SingleArcHeirMidpoint.singleton X hq small F f single wp wm wr pc).1
  rcases alternatives with ⟨v,vu,av,vb,_,first,heavy⟩|long
  · have vv := (mem_nonParentSet.mp (mem_filter.mp vu).1).1
    let k : X.V := ⟨v,vv⟩
    obtain ⟨_,_,_,C,cy,ac,vc,_,_⟩ := SingleArcCycleParents.supply X hq small F wp wm wr pc f single k av
    refine Or.inl ⟨k,vu,av,vb,⟨C,cy,ac,vc⟩,?_⟩
    intro M cm am vm
    obtain ⟨i,im,neg,hit,separate⟩ := witness X hq small F wp wm wr pc f k cm am vm av heavy
    have old (i j) (ij : E i j=true) := (mem_col.mp (active.mp ij).choose_spec).2.2.2
    have ib : i≠b := by
      rintro rfl
      exact separate ⟨f.property.1,old _ _ vb⟩
    have off : X.D a i=false := by
      apply Bool.eq_false_iff.mpr
      intro ed
      have ai : E a i=true := by
        by_contra no
        let g : SharedArcFlatCut.Missing X F := ⟨(a,i),ed,Bool.eq_false_iff.mpr no⟩
        exact ib (congrArg (fun h : SharedArcFlatCut.Missing X F=>h.val.2) (single g))
      have vi := first i i.property (fun e=>im (e ▸ vm)) ai
      exact separate ⟨ed,old _ _ vi⟩
    exact ⟨i,im,off,neg,hit⟩
  · exact Or.inr long

end LeanCH.BR.Closure.SingleArcCycleHead
#print axioms LeanCH.BR.Closure.SingleArcCycleHead.ports
#print axioms LeanCH.BR.Closure.SingleArcCycleHead.positive_of_ports
#print axioms LeanCH.BR.Closure.SingleArcCycleHead.witness
#print axioms LeanCH.BR.Closure.SingleArcCycleHead.singleton
