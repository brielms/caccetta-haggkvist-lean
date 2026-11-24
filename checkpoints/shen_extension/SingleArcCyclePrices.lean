import checkpoints.shen_extension.SingleArcMidpointSign

namespace LeanCH.BR.Closure.SingleArcCyclePrices
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse SharedArcFlatResponse ShenCycleSuccessor
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open scoped Matrix

private def spike {I : Type*} [DecidableEq I] (j i : I) : ℝ := if i=j then 1 else 0

/-- The local solve uses only the old induced cycle. The added constant
fixes the price at the specified successor. -/
noncomputable def prices {I : Type*} [Fintype I] [DecidableEq I] (R : Matrix I I ℝ)
    (a v : I) (anchor : ℝ) (i : I) : ℝ :=
  let h := R⁻¹ *ᵥ (spike v-spike a)
  h i + (anchor-h v)

private theorem inside {I : Type*} [Fintype I] [DecidableEq I] (R : Matrix I I ℝ)
    (unit : IsUnit R.det) (rowSum : ∀i,∑j,R i j=(Fintype.card I:ℝ))
    (colSum : ∀j,∑i,R i j=(Fintype.card I:ℝ))
    (a v : I) (anchor : ℝ) (i : I) :
    (∑j,(R i j-1)*prices R a v anchor j)=spike v i-spike a i := by
  let h := R⁻¹ *ᵥ (spike v-spike a)
  have eq : R *ᵥ h=spike v-spike a := by
    rw [show h=R⁻¹ *ᵥ (spike v-spike a) from rfl,mulVec_mulVec,mul_nonsing_inv R unit,one_mulVec]
  have hsum : (∑j,h j)=0 := by
    have total := congrArg (fun u : I→ℝ=>∑j,u j) eq
    change (∑j,∑k,R j k*h k)=∑j,(spike v j-spike a j) at total
    rw [sum_comm] at total
    simp only [←sum_mul,colSum,←mul_sum,sum_sub_distrib,spike] at total
    simp at total
    let _ : Nonempty I := ⟨a⟩
    rcases total with z|z
    · exact (Fintype.card_ne_zero z).elim
    · exact z
  have hi := congrFun eq i
  change (∑j,R i j*h j)=spike v i-spike a i at hi
  change (∑j,(R i j-1)*(h j+(anchor-h v)))=_
  simp only [sub_mul,one_mul,mul_add,sum_sub_distrib,sum_add_distrib,←sum_mul,rowSum,hsum,
    sum_const,card_univ,nsmul_eq_mul,hi]
  ring

/-- The contribution of a label to the cycle price, with the two known
internal coefficients removed. It is zero everywhere on the cycle. -/
noncomputable def exterior (q : ℕ) (E : CH.Digraph) {C : Finset ℕ} (a v : C)
    (anchor : ℝ) (i : ℕ) : ℝ :=
  let h := prices (realMatrix q E C) a v anchor
  (∑j : C, ((if i=j.val then 1 else 0)+(if E i j=true then (q:ℝ) else 0)-1)*h j)
    -(if i=v.val then 1 else 0)+(if i=a.val then 1 else 0)

theorem exterior_on {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ}
    (cy : Cycle E V q C) (a v : C) (anchor : ℝ) (i : C) :
    exterior q E a v anchor i=0 := by
  have outs (j : C) : WeightedSD.row q E C (fun _=>1) j=(C.card:ℚ) := by
    have eq := cy.heads j j.property
    simp [WeightedSD.row,outW_eq_mass,mass,eq,cy.size,add_comm]
  have ins (j : C) : WeightedSD.col q E C (fun _=>1) j=(C.card:ℚ) := by
    have eq := cy.incoming j j.property
    change (C.filter (fun i=>E i j=true)).card=1 at eq
    simp [WeightedSD.col,inW,eq,cy.size,add_comm]
  have rowSum (j : C) := realMatrix_rational_rows (q:=q) (D:=E) (fun _=>1) (C.card:ℚ)
    (fun i hi=>outs ⟨i,hi⟩) j
  have colSum (j : C) := realMatrix_rational_columns (q:=q) (D:=E) (fun _=>1) (C.card:ℚ)
    (fun i hi=>ins ⟨i,hi⟩) j
  have h := inside (realMatrix q E C) (matrix_unit hq E C)
    (fun j=>by simpa [mulVec,dotProduct] using rowSum j)
    (fun j=>by simpa [vecMul,dotProduct] using colSum j) a v anchor i
  simp only [realMatrix_entry,spike,Subtype.ext_iff] at h
  unfold exterior
  linarith only [h]

section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (F : Family) {w p : ℕ→ℚ}
  (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
  (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

include hq wp wm wr pc in
/-- Every old cycle probe missing the inserted head gives the *same*
off-cycle tensor sum. The right side involves only old outgoing incidences,
the induced cycle matrix and the ratio of two old weights. -/
theorem account (f : SharedArcFlatCut.Missing X F) (v : X.V) {C : Finset ℕ}
    (sub : C⊆X.V) (ac : f.val.1.val∈C) (vc : v.val∈C) (bc : f.val.2.val∉C) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q a b
    T v v = -∑i : X.V,T v i*exterior q E ⟨a,ac⟩ ⟨v,vc⟩ (-(w v:ℝ)/((q:ℝ)*(w b:ℝ))) i := by
  intro E a b T
  let d := (q:ℝ)*(p a:ℝ)*(w b:ℝ)
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have bp : 0<(w b:ℝ) := by exact_mod_cast (wp b b.property).1
  have ap : 0<(p a:ℝ) := by exact_mod_cast (wp a a.property).2
  have dp : 0<d := mul_pos (mul_pos qp ap) bp
  let J := realMatrix q (insertArc E a b) X.V
  have inv := SingleArcPunctureSign.signed_right (matrix_unit hq E X.V)
    (realMatrix_insert_difference (q:=q) a b (show ¬E a b=true by simp [E,a,b,f.property.2]))
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc))
    (real_mass_of_rational_probability w wm) dp.ne'
  let lift (j : C) : X.V := ⟨j,sub j.property⟩
  let ac' : C := ⟨a,ac⟩
  let vc' : C := ⟨v,vc⟩
  let anchor := -(w v:ℝ)/((q:ℝ)*(w b:ℝ))
  let h := prices (realMatrix q E C) ac' vc' anchor
  let entry (i : X.V) (j : C) := (if i.val=j.val then (1:ℝ) else 0)+(if E i j=true then (q:ℝ) else 0)-1
  have pay (j : C) : (∑i : X.V,T v i*entry i j)=(if vc'=j then d else 0) := by
    have left : (Matrix.of (fun i j : X.V=>T i j/d))*excess J=1 := mul_eq_one_comm.mp inv
    have col := congrFun (congrFun left v) (lift j)
    change (∑i : X.V,(T v i/d)*(J i (lift j)-1))=(1:Matrix X.V X.V ℝ) v (lift j) at col
    have old (i : X.V) : J i (lift j)-1=entry i j := by
      have jb : j.val≠b.val := fun eq=>bc (eq ▸ j.property)
      have keep : insertArc E a b i (lift j)=E i j := by
        change (if i.val=a.val ∧ j.val=b.val then true else E i j)=E i j
        rw [if_neg (fun hh=>jb hh.2)]
      change realMatrix q (insertArc E a b) X.V i (lift j)-1=_
      rw [realMatrix_entry,keep]
      simp only [entry,Subtype.ext_iff,lift]
    simp_rw [old,div_mul_eq_mul_div,←sum_div] at col
    have z := (div_eq_iff dp.ne').mp col
    simpa [one_apply,ite_mul,Subtype.ext_iff,lift,vc'] using z
  have priced : (∑i : X.V,T v i*(∑j : C,entry i j*h j))=d*h vc' := by
    simp only [mul_sum,←mul_assoc]
    rw [sum_comm]
    simp_rw [←sum_mul,pay]
    simp [ite_mul]
  have spikeSum (j : X.V) : (∑i : X.V,T v i*(if i.val=j.val then 1 else 0))=T v j := by
    simp [mul_ite]
  have base : T v a=(w v:ℝ)*(p a:ℝ) := by dsimp [T,test]; ring
  have ha : h vc'=anchor := by simp [h,prices]
  have scale : d*anchor= -(T v a) := by rw [base]; dsimp [d,anchor]; field_simp
  change T v v= -(∑i : X.V,T v i*(((∑j : C,entry i j*h j)-(if i.val=v.val then 1 else 0))+
    (if i.val=a.val then 1 else 0)))
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,spikeSum,priced,ha,scale]
  ring

include hq wp wm wr pc in
/-- An affine combination of exterior prices which is nonnegative at
every exterior label closes the actual diagonal. Coefficients may be signed.
Each column of the finite feasibility test is computed on an old cycle.
No tensor entry occurs in the cover hypothesis. -/
theorem cover_progress (small : SmallerSmallRow q X.V.card) (B : Finset ℕ)
    (J : Matrix X.V X.V ℝ) (prices₀ : ℕ→ℚ) (c : ℚ) (f : SharedArcFlatCut.Missing X F) (v : X.V)
    {K : Type*} [Fintype K] (C : K→Finset ℕ) (cy : ∀k,Cycle (graph X.D F) X.V q (C k))
    (ac : ∀k,f.val.1.val∈C k) (vc : ∀k,v.val∈C k) (bc : ∀k,f.val.2.val∉C k)
    (weights : K→ℝ) (unit : ∑k,weights k=1)
    (cover : ∀i : X.V,i≠v → 0≤∑k,weights k*exterior q (graph X.D F) ⟨f.val.1,ac k⟩
      ⟨v,vc k⟩ (-(w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))) i) :
    SharedArcPivotGate.ProgressAt X F B J prices₀ c := by
  let E := graph X.D F
  let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
  let z (k : K) (i : X.V) := exterior q E ⟨f.val.1,ac k⟩ ⟨v,vc k⟩ (-(w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))) i
  have eq (k) : ∑i : X.V,T v i*z k i= -T v v := by
    have h := account X hq F wp wm wr pc f v (cy k).sub (ac k) (vc k) (bc k)
    change T v v= -(∑i : X.V,T v i*z k i) at h
    linarith only [h]
  have mix : (∑i : X.V,T v i*(∑k,weights k*z k i))= -T v v := by
    simp only [mul_sum]
    rw [sum_comm]
    have regroup (k : K) : (∑i : X.V,T v i*(weights k*z k i))=weights k*(∑i : X.V,T v i*z k i) := by
      rw [mul_sum]; exact sum_congr rfl (fun i _=>mul_left_comm ..)
    simp_rw [regroup,eq,←sum_mul,unit,one_mul]
  have nonneg : 0≤∑i : X.V,T v i*(∑k,weights k*z k i) := by
    apply sum_nonneg
    intro i _
    by_cases same : i=v
    · subst i
      have zero (k) : z k v=0 := exterior_on hq (cy k) _ _ _ ⟨v,vc k⟩
      simp [zero]
    · exact mul_nonneg (SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f v i).le (cover i same)
  rw [mix,neg_nonneg] at nonneg
  have nz := SharedArcFlatArithmetic.nonzero hq (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) f.val.1 f.val.2 v v
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,wp,wm,wr,pc,f,v,v,lt_of_le_of_ne nonneg nz⟩)))

end Native
end LeanCH.BR.Closure.SingleArcCyclePrices
#print axioms LeanCH.BR.Closure.SingleArcCyclePrices.exterior_on
#print axioms LeanCH.BR.Closure.SingleArcCyclePrices.account
#print axioms LeanCH.BR.Closure.SingleArcCyclePrices.cover_progress
