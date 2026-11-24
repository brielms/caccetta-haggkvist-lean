import checkpoints.shen_extension.SingleArcCommonParent

namespace LeanCH.BR.Closure.CommonParentRepair
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SingleArcCycleBalance SharedArcFlatResponse

/-- Averaging marked cycles and allowing a different admissible t on
each one leaves a uniform deficit at their common obstructing vertex. -/
theorem mixture {q E V} (hq : 2≤q) (free : QFree E V q) (a v i : ℕ) (av : E a v=true)
    (ia : E i a=true) (iv : E i v=true) (x : ℝ) (heavy : 1<((q:ℝ)-1)*x)
    {I : Type*} [Fintype I] (C : I→Finset ℕ) (cy : ∀k,Cycle E V q (C k))
    (ac : ∀k,a∈C k) (vc : ∀k,v∈C k) (t l : I→ℝ) (t1 : ∀k,1≤t k)
    (pos : ∀k,0≤l k) (prob : ∑k,l k=1) :
    (∑k,l k*SingleArcCycleSlope.score q (SingleArcCommonTilt.hits E (C k) i)
      (tiltedPrices q E ⟨a,ac k⟩ ⟨v,vc k⟩ (t k) x)) < -min 1 (((q:ℝ)-1)*x-1) := by
  let S (k : I) := SingleArcCycleSlope.score q (SingleArcCommonTilt.hits E (C k) i)
    (tiltedPrices q E ⟨a,ac k⟩ ⟨v,vc k⟩ (t k) x)
  let d := min 1 (((q:ℝ)-1)*x-1)
  have dp : 0<d := lt_min zero_lt_one (sub_pos.mpr heavy)
  have qp : 0<(q:ℝ)+1 := by positivity
  have bound (k : I) : S k< -d := by
    have mb := SingleArcCommonParent.margin hq free (cy k) ⟨a,ac k⟩ ⟨v,vc k⟩ av x heavy
      (SingleArcCommonTilt.hits E (C k) i) (mem_filter.mpr ⟨mem_univ _,ia⟩) (mem_filter.mpr ⟨mem_univ _,iv⟩) (t k) (t1 k)
    change ((q:ℝ)+1)*S k< -((q:ℝ)+t k)*d at mb
    apply lt_of_mul_lt_mul_left (a:=(q:ℝ)+1) _ qp.le
    nlinarith only [mb,mul_nonneg (sub_nonneg.mpr (t1 k)) dp.le]
  have live : ∃k,0<l k := by
    by_contra! zero
    have vanished : (∑k,l k)=0 := sum_eq_zero (fun k _=>le_antisymm (zero k) (pos k))
    linarith only [vanished,prob]
  obtain ⟨j,hit⟩ := live
  have h := sum_lt_sum (s:=univ) (fun k _=>mul_le_mul_of_nonneg_left (bound k).le (pos k))
    ⟨j,mem_univ _,mul_lt_mul_of_pos_left (bound j) hit⟩
  simpa only [←sum_mul,prob,one_mul] using h

/-- The residual tested by the variable-tail diagonal bound. -/
noncomputable def residual (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (a v : V) (t : ℝ)
    (phi : V→ℝ) (i : V) : ℝ :=
  (∑j : V,(realMatrix q E V i j-1)*phi j)-(if i=v then 1 else 0)+(if i=a then t else 0)

def edit {I : Type*} [DecidableEq I] (phi : I→ℝ) (y : I) (c : ℝ) (j : I) : ℝ :=
  phi j-(if j=y then c else 0)

theorem change_at {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (a v y : V) (t c : ℝ) (phi : V→ℝ) (loop : E y y=false) (i : V) :
    residual q E V a v t (edit phi y c) i =
      residual q E V a v t phi i +
        (if i=y then 0 else if E i y=true then -((q:ℝ)-1)*c else c) := by
  simp only [residual,edit,mul_sub,sum_sub_distrib,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true,realMatrix_entry]
  by_cases iy : i=y
  · subst i; simp [loop]
  · simp only [ite_eq_right iy]
    by_cases ed : E i y=true <;> simp [ed] <;> ring

/-- The named deficit itself can always be repaired at a missed
column. This conclusion assumes nothing about the other residuals. -/
theorem fixed_row {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (a v i y : V) (t : ℝ) (phi : V→ℝ) (loop : E y y=false)
    (iy : i≠y) (miss : E i y=false) (bad : residual q E V a v t phi i<0) :
    let c := -residual q E V a v t phi i
    residual q E V a v t (edit phi y c) i=0 ∧ edit phi y c y<phi y := by
  intro c
  constructor
  · rw [change_at a v y t c phi loop i]
    simp [iy,miss,c]
  · simp [edit,c,bad]

/-- When q ≥ 3 the companion cycle supplies an unanchored column
which is missed by its own marked predecessor. -/
theorem repair_label {q E V K} (hq : 3≤q) (cy : Cycle E V q K) (i v b : V)
    (ik : i.val∈K) (iv : E i v=true) (vk : v.val∈K) :
    ∃y : V,y.val∈K ∧ y≠i ∧ y≠v ∧ y≠b ∧ E i y=false := by
  have live : (K \ {i.val,v.val,b.val}).Nonempty := by
    by_contra miss
    have sub : K⊆{i.val,v.val,b.val} := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp miss)
    have le := (card_le_card sub).trans card_le_three
    rw [cy.size] at le; omega
  obtain ⟨j,hj⟩ := live
  obtain ⟨jk,off⟩ := mem_sdiff.mp hj
  simp only [mem_insert,mem_singleton,not_or] at off
  let y : V := ⟨j,cy.sub jk⟩
  have yv : y≠v := fun e=>off.2.1 (congrArg Subtype.val e)
  refine ⟨y,jk,fun e=>off.1 (congrArg Subtype.val e),yv,fun e=>off.2.2 (congrArg Subtype.val e),?_⟩
  exact Bool.eq_false_iff.mpr (fun ed=>off.2.1 (card_le_one.mp (cy.heads i ik).le _
    (mem_outN.mpr ⟨jk,ed⟩) _ (mem_outN.mpr ⟨vk,iv⟩)))

/-- Extend the one-cycle price by zero to the full support. -/
noncomputable def cyclePrice (q : ℕ) (E : CH.Digraph) {V C : Finset ℕ}
    (a v : C) (t x : ℝ) (j : V) : ℝ :=
  if h : j.val∈C then tiltedPrices q E a v t x ⟨j,h⟩ else 0

theorem exterior_row {q : ℕ} {E : CH.Digraph} {V C : Finset ℕ} (sub : C⊆V) (a v i : V)
    (ac : a.val∈C) (vc : v.val∈C) (off : i.val∉C) (t x : ℝ) :
    residual q E V a v t (cyclePrice q E ⟨a,ac⟩ ⟨v,vc⟩ t x) i =
      SingleArcCycleSlope.score q (SingleArcCommonTilt.hits E C i)
        (tiltedPrices q E ⟨a,ac⟩ ⟨v,vc⟩ t x) := by
  let z := tiltedPrices q E ⟨a,ac⟩ ⟨v,vc⟩ t x
  let l (j : ℕ) := if h : j∈C then z ⟨j,h⟩ else 0
  let e (j : ℕ) : ℝ := (if i.val=j then 1 else 0)+(if E i j=true then (q:ℝ) else 0)-1
  have restr : (∑j : V,e j*l j)=∑j : C,e j*z j := by
    calc
      _ = ∑j∈V,e j*l j := by conv_rhs => rw [←sum_coe_sort]
      _ = ∑j∈C,e j*l j := (sum_subset sub (fun j _ hj=>by simp [l,hj])).symm
      _ = _ := by
        conv_lhs => rw [←sum_coe_sort]
        exact sum_congr rfl (fun j _=>by simp [l,j.property])
  have ij (j : C) : i.val≠j.val := fun eq=>off (eq ▸ j.property)
  have iv : i≠v := fun eq=>off (eq ▸ vc)
  have ia : i≠a := fun eq=>off (eq ▸ ac)
  simp only [residual,realMatrix_entry,Subtype.ext_iff] 
  change (∑j : V,e j*l j)-(if i.val=v.val then 1 else 0)+(if i.val=a.val then t else 0)=_
  rw [restr]
  have iv' : i.val≠v.val := fun eq=>iv (Subtype.ext eq)
  have ia' : i.val≠a.val := fun eq=>ia (Subtype.ext eq)
  simp only [e,ij,iv',ia',ite_false,zero_add,sub_zero,add_zero,sub_mul,one_mul,
    ite_mul,zero_mul,sum_sub_distrib,SingleArcCycleSlope.score,SingleArcCommonTilt.hits,sum_filter,mul_sum,mul_ite,mul_zero,z]

/-- For the actual two old cycles the fixed row can be repaired
exactly, preserving both anchor values, at any admissible tilt. -/
theorem on_cycles {q E V C K} (hq : 3≤q) (free : QFree E V q) (cy : Cycle E V q C)
    (second : Cycle E V q K) (a v b i : V) (ac : a.val∈C) (vc : v.val∈C)
    (off : i.val∉C) (ik : i.val∈K) (vk : v.val∈K) (av : E a v=true)
    (ia : E i a=true) (iv : E i v=true) (x : ℝ) (heavy : 1<((q:ℝ)-1)*x) :
    ∃y : V,y.val∈K ∧ y≠i ∧ y≠v ∧ y≠b ∧ E i y=false ∧ ∀t : ℝ,1≤t →
      let phi := cyclePrice (V:=V) q E ⟨a,ac⟩ ⟨v,vc⟩ t x
      let c := -residual q E V a v t phi i
      0<c ∧ edit phi y c v=phi v ∧ edit phi y c b=phi b ∧ residual q E V a v t (edit phi y c) i=0 := by
  obtain ⟨y,yk,yi,yv,yb,miss⟩ := repair_label hq second i v b ik iv vk
  refine ⟨y,yk,yi,yv,yb,miss,?_⟩
  intro t one phi c
  have neg : residual q E V a v t phi i<0 := by
    rw [show phi=cyclePrice (V:=V) q E ⟨a,ac⟩ ⟨v,vc⟩ t x from rfl,exterior_row cy.sub a v i ac vc off]
    exact SingleArcCommonParent.veto (by omega) free cy ⟨a,ac⟩ ⟨v,vc⟩ av x heavy
      (SingleArcCommonTilt.hits E C i) (mem_filter.mpr ⟨mem_univ _,ia⟩) (mem_filter.mpr ⟨mem_univ _,iv⟩) t one
  have loop := Bool.eq_false_iff.mpr (loopfree free (by omega : 1≤q) y.property)
  exact ⟨neg_pos.mpr neg,by simp [edit,yv.symm],by simp [edit,yb.symm],
    (fixed_row a v i y t phi loop yi.symm miss neg).1⟩

/-- Subtracting the exact deficit at y pays the fixed vertex i.
On the remaining labels the only new costs occur at old parents of y. -/
theorem one_column {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀j∈X.V,0<w j ∧ 0<p j) (wm : mass X.V w=1)
    (wr : ∀j∈X.V,WeightedSD.row q (graph X.D F) X.V w j=1)
    (pc : ∀j∈X.V,WeightedSD.col q (graph X.D F) X.V p j=1)
    (f : SharedArcFlatCut.Missing X F) (v i y : X.V) (t : ℝ) (phi : X.V→ℝ)
    (head : phi f.val.2=0) (anchor : phi v= -(t*(w v:ℝ))/((q:ℝ)*(w f.val.2:ℝ)))
    (yv : y≠v) (yb : y≠f.val.2) (iy : i≠y) (miss : graph X.D F i y=false)
    (deficit : residual q (graph X.D F) X.V f.val.1 v t phi i<0)
    (pay : let E := graph X.D F
           let B := residual q E X.V f.val.1 v t phi
           0≤B y ∧ (∀j : X.V,E j y=true → ((q:ℝ)-1)*(-B i)≤B j) ∧
              ∀j : X.V,j≠y → E j y=false → B i≤B j) :
    ∃phi' : X.V→ℝ,phi' f.val.2=0 ∧ phi' v=phi v ∧
      residual q (graph X.D F) X.V f.val.1 v t phi' i=0 ∧
      (∀j,residual q (graph X.D F) X.V f.val.1 v t phi j+
        (if j=y then 0 else if graph X.D F j y=true then ((q:ℝ)-1)*
          residual q (graph X.D F) X.V f.val.1 v t phi i else -residual q (graph X.D F) X.V f.val.1 v t phi i)=
        residual q (graph X.D F) X.V f.val.1 v t phi' j) ∧
      test (realMatrix q (graph X.D F) X.V)⁻¹ (fun j : X.V=>(w j:ℝ)) (fun j : X.V=>(p j:ℝ))
        q f.val.1 f.val.2 v v≤0 := by
  let E := graph X.D F
  let B := residual q E X.V f.val.1 v t phi
  let c := -B i
  let phi' := edit phi y c
  have old := PrivateArcEndpoints.graph_free X F
  have loop : E y y=false := Bool.eq_false_iff.mpr (loopfree old (by omega) y.property)
  have eq (j) := change_at (q:=q) f.val.1 v y t c phi loop j
  have ends : phi' f.val.2=0 ∧ phi' v=phi v := by simp [phi',edit,yb.symm,yv.symm,head]
  refine ⟨phi',ends.1,ends.2,?_,?_,?_⟩
  · exact (fixed_row f.val.1 v i y t phi loop iy miss deficit).1
  · intro j
    simpa only [phi',B,c,neg_mul, mul_neg,neg_neg] using (eq j).symm
  · apply flexible_bound X hq small F wp wm wr pc f v t phi' ends.1 (ends.2.trans anchor)
    intro j
    change 0≤residual q E X.V f.val.1 v t phi' j
    rw [show phi'=edit phi y c from rfl,eq j]
    rcases pay with ⟨self,incoming,other⟩
    by_cases same : j=y
    · subst j; simpa using self
    · rw [ite_eq_right same]
      by_cases ed : E j y=true
      · rw [ite_eq_left ed]
        change 0≤B j+(-((q:ℝ)-1))*c
        have bill : ((q:ℝ)-1)*c≤B j := incoming j ed
        linarith only [bill]
      · rw [ite_eq_right ed]
        change 0≤B j-B i
        exact sub_nonneg.mpr (other j same (Bool.eq_false_iff.mpr ed))

/-- The corrected row budgets feed the capstone's diagonal exit. -/
theorem progress {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) (F : Family)
    {w p : ℕ→ℚ} (wp : ∀j∈X.V,0<w j ∧ 0<p j) (wm : mass X.V w=1)
    (wr : ∀j∈X.V,WeightedSD.row q (graph X.D F) X.V w j=1)
    (pc : ∀j∈X.V,WeightedSD.col q (graph X.D F) X.V p j=1)
    (B : Finset ℕ) (J : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (value : ℚ)
    (f : SharedArcFlatCut.Missing X F) (v i y : X.V) (t : ℝ) (phi : X.V→ℝ)
    (head : phi f.val.2=0) (anchor : phi v= -(t*(w v:ℝ))/((q:ℝ)*(w f.val.2:ℝ)))
    (yv : y≠v) (yb : y≠f.val.2) (iy : i≠y) (miss : graph X.D F i y=false)
    (deficit : residual q (graph X.D F) X.V f.val.1 v t phi i<0)
    (pay : let E := graph X.D F
           let R := residual q E X.V f.val.1 v t phi
           0≤R y ∧ (∀j : X.V,E j y=true → ((q:ℝ)-1)*(-R i)≤R j) ∧
              ∀j : X.V,j≠y → E j y=false → R i≤R j) :
    SharedArcPivotGate.ProgressAt X F B J prices value := by
  obtain ⟨_,_,_,_,_,bound⟩ := one_column X hq small F wp wm wr pc f v i y t phi head anchor yv yb iy miss deficit pay
  have nz := SharedArcFlatArithmetic.nonzero hq (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) f.val.1 f.val.2 v v
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,wp,wm,wr,pc,f,v,v,lt_of_le_of_ne bound nz⟩)))

end LeanCH.BR.Closure.CommonParentRepair
#print axioms LeanCH.BR.Closure.CommonParentRepair.change_at
#print axioms LeanCH.BR.Closure.CommonParentRepair.mixture
#print axioms LeanCH.BR.Closure.CommonParentRepair.fixed_row
#print axioms LeanCH.BR.Closure.CommonParentRepair.repair_label
#print axioms LeanCH.BR.Closure.CommonParentRepair.exterior_row
#print axioms LeanCH.BR.Closure.CommonParentRepair.on_cycles
#print axioms LeanCH.BR.Closure.CommonParentRepair.one_column
#print axioms LeanCH.BR.Closure.CommonParentRepair.progress
