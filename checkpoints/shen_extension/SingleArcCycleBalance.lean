import checkpoints.shen_extension.SingleArcCycleHead

namespace LeanCH.BR.Closure.SingleArcCycleBalance
open Finset Matrix BRq2 BRq3 WeightedSD FiniteCutInverse SingleArcCyclePrices
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling ShenCycleSuccessor

/-- The old column law is a second, explicit test of every exterior
column. Its weighted total is independent of the cycle and the anchor. -/
theorem balance {q : ℕ} {E : CH.Digraph} {V C : Finset ℕ} (sub : C⊆V)
    (a v : C) (anchor : ℝ) {p : ℕ→ℚ} (pm : mass V p=1)
    (pc : ∀i∈V,WeightedSD.col q E V p i=1) :
    (∑i : V,(p i:ℝ)*SingleArcCyclePrices.exterior q E a v anchor i)=(p a:ℝ)-(p v:ℝ) := by
  let z := prices (realMatrix q E C) a v anchor
  let entry (i : V) (j : C) := (if i.val=j.val then (1:ℝ) else 0)+(if E i j=true then (q:ℝ) else 0)-1
  have col (j : C) : (∑i : V,(p i:ℝ)*entry i j)=0 := by
    let k : V := ⟨j,sub j.property⟩
    have one := realMatrix_rational_columns p 1 pc k
    change (∑i : V,(p i:ℝ)*realMatrix q E V i k)=((1:ℚ):ℝ) at one
    have equal (i : V) : entry i j=realMatrix q E V i k-1 := by
      simp only [entry,realMatrix_entry,Subtype.ext_iff,k]
    simp only [equal,mul_sub,mul_one,sum_sub_distrib,one,real_mass_of_rational_probability p pm,Rat.cast_one,sub_self]
  have zero : (∑i : V,(p i:ℝ)*(∑j : C,entry i j*z j))=0 := by
    simp only [mul_sum,←mul_assoc]
    rw [sum_comm]
    simp_rw [←sum_mul,col,zero_mul,sum_const_zero]
  have spike (j : C) : (∑i : V,(p i:ℝ)*(if i.val=j.val then 1 else 0))=(p j:ℝ) := by
    let k : V := ⟨j,sub j.property⟩
    have same (i : V) : i.val=j.val ↔ i=k := ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    simp only [same,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true,k]
  change (∑i : V,(p i:ℝ)*(((∑j : C,entry i j*z j)-(if i.val=v.val then 1 else 0))+
    (if i.val=a.val then 1 else 0)))=_
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,zero,spike]
  ring

/-- Any nonnegative affine cover of the diagonal must pass the old
column-weight ordering test, even when negative coefficients are allowed. -/
theorem cover_requires_order {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} {p : ℕ→ℚ}
    (pm : mass V p=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1) (pos : ∀i∈V,0≤p i)
    (a v : V) (anchor : ℝ) {K : Type*} [Fintype K] (C : K→Finset ℕ)
    (sub : ∀k,C k⊆V) (ac : ∀k,a.val∈C k) (vc : ∀k,v.val∈C k)
    (l : K→ℝ) (unit : ∑k,l k=1) (cover : ∀i : V,0≤∑k,l k*
      SingleArcCyclePrices.exterior q E ⟨a,ac k⟩ ⟨v,vc k⟩ anchor i) : p v≤p a := by
  let z (k : K) (i : V) := SingleArcCyclePrices.exterior q E ⟨a,ac k⟩ ⟨v,vc k⟩ anchor i
  have mean (k : K) : (∑i : V,(p i:ℝ)*z k i)=(p a:ℝ)-(p v:ℝ) := balance (sub k) _ _ _ pm pc
  have h := sum_nonneg (s:=univ) (fun (i : V) _=>mul_nonneg (show (0:ℝ)≤p i by exact_mod_cast pos i i.property) (cover i))
  change 0≤∑i : V,(p i:ℝ)*(∑k,l k*z k i) at h
  simp only [mul_sum] at h
  rw [sum_comm] at h
  have swap (k : K) : (∑i : V,(p i:ℝ)*(l k*z k i))=l k*(∑i : V,(p i:ℝ)*z k i) := by
    rw [mul_sum]; exact sum_congr rfl (fun i _=>mul_left_comm ..)
  simp_rw [swap,mean,←sum_mul,unit,one_mul] at h
  exact_mod_cast sub_nonneg.mp h

/-- A local cycle test may also choose the coefficient of the tail.
The price vector may be supported on any desired collection of old
cycles. Only its midpoint value is prescribed and its head value is zero. -/
theorem flexible_bound {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    (f : SharedArcFlatCut.Missing X F) (v : X.V) (t : ℝ) (phi : X.V→ℝ) (head : phi f.val.2=0)
    (anchor : phi v= -(t*(w v:ℝ))/((q:ℝ)*(w f.val.2:ℝ)))
    (cover : ∀i : X.V,0≤ (∑j : X.V,(realMatrix q (graph X.D F) X.V i j-1)*phi j)
      -(if i=v then 1 else 0)+(if i=f.val.1 then t else 0)) :
    SharedArcFlatResponse.test (realMatrix q (graph X.D F) X.V)⁻¹ (fun i : X.V=>(w i:ℝ))
      (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2 v v≤0 := by
  let E := graph X.D F
  let a := f.val.1
  let b := f.val.2
  let J := realMatrix q (insertArc E a b) X.V
  let d := (q:ℝ)*(p a:ℝ)*(w b:ℝ)
  let T := SharedArcFlatResponse.test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q a b
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have bp : 0<(w b:ℝ) := by exact_mod_cast (wp _ b.property).1
  have dp : 0<d := mul_pos (mul_pos qp (by exact_mod_cast (wp _ a.property).2)) bp
  have delta := realMatrix_insert_difference (q:=q) a b (show ¬E a b=true by simp [E,a,b,f.property.2])
  have inv := SingleArcPunctureSign.signed_right (SharedArcFlatResponse.matrix_unit hq E X.V) delta
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc))
    (real_mass_of_rational_probability w wm) dp.ne'
  have left : (Matrix.of (fun i j : X.V=>T i j/d))*excess J=1 := mul_eq_one_comm.mp inv
  have outer : (Matrix.of (fun i j : X.V=>T i j/d) *ᵥ (excess J *ᵥ phi)) v=phi v := by
    rw [mulVec_mulVec,left,one_mulVec]
  have old (i j : X.V) : (J i j-1)*phi j=(realMatrix q E X.V i j-1)*phi j := by
    by_cases hj : j=b
    · subst j; simp [b,head]
    have eq := delta i j
    have miss : ¬(i=a ∧ j=b) := fun h=>hj h.2
    simp only [ite_eq_right miss,sub_eq_zero] at eq
    rw [show J i j=realMatrix q E X.V i j from eq]
  change (∑i : X.V,(T v i/d)*(∑j : X.V,(J i j-1)*phi j))=phi v at outer
  simp_rw [old,div_mul_eq_mul_div,←sum_div] at outer
  have total := (div_eq_iff dp.ne').mp outer
  have pos (i : X.V) := (SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f v i).le
  have sumOK := sum_nonneg (s:=univ) (fun (i : X.V) _=>mul_nonneg (pos i) (cover i))
  change 0≤∑i : X.V,T v i*((∑j : X.V,(realMatrix q E X.V i j-1)*phi j)-
    (if i=v then 1 else 0)+(if i=a then t else 0)) at sumOK
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,mul_ite,mul_one,mul_zero,
    sum_ite_eq',mem_univ,ite_true,total] at sumOK
  have base : T v a=(w v:ℝ)*(p a:ℝ) := by dsimp [T,SharedArcFlatResponse.test]; ring
  have cancel : phi v*d= -(T v a*t) := by
    rw [anchor,base]
    dsimp [d]
    change -(t*(w v:ℝ))/((q:ℝ)*(w b:ℝ))*((q:ℝ)*(p a:ℝ)*(w b:ℝ))=_
    field_simp
  change T v v≤0
  linarith only [sumOK,cancel]

/-- The free tail coefficient requires only a one-dimensional exterior
test on each chosen cycle. The internal residual is constant (t−1)/|C|. -/
theorem tilted_cycle {I : Type*} [Fintype I] [DecidableEq I] (R : Matrix I I ℝ)
    (unit : IsUnit R.det) (rows : ∀i,∑j,R i j=(Fintype.card I:ℝ))
    (cols : ∀j,∑i,R i j=(Fintype.card I:ℝ)) (v a : I) (t anchor : ℝ) :
    let rhs (j : I) := (if j=v then (1:ℝ) else 0)-(if j=a then t else 0)
    let h := R⁻¹ *ᵥ rhs
    let z (j : I) := h j+(anchor-h v)
    z v=anchor ∧ ∀i,(∑j,(R i j-1)*z j)-rhs i=(t-1)/(Fintype.card I:ℝ) := by
  intro rhs h z
  have eq : R *ᵥ h=rhs := by rw [show h=R⁻¹ *ᵥ rhs from rfl,mulVec_mulVec,mul_nonsing_inv R unit,one_mulVec]
  have total := congrArg (fun u : I→ℝ=>∑i,u i) eq
  change (∑i,∑j,R i j*h j)=∑i,rhs i at total
  rw [sum_comm] at total
  simp only [←sum_mul,cols,←mul_sum,rhs,sum_sub_distrib,sum_ite_eq',mem_univ,ite_true] at total
  let _ : Nonempty I := ⟨v⟩
  have nn : (Fintype.card I:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨by dsimp [z]; ring,?_⟩
  intro i
  have one := congrFun eq i
  change (∑j,R i j*h j)=rhs i at one
  dsimp only [z]
  simp only [sub_mul,one_mul,mul_add,sum_sub_distrib,sum_add_distrib,←sum_mul,rows,one,
    sum_const,card_univ,nsmul_eq_mul]
  apply (eq_div_iff nn).mpr
  nlinarith only [total]

noncomputable def tiltedPrices (q : ℕ) (E : CH.Digraph) {C : Finset ℕ} (a v : C) (t x : ℝ) : C→ℝ :=
  let rhs (j : C) := (if j=v then (1:ℝ) else 0)-(if j=a then t else 0)
  let h := (realMatrix q E C)⁻¹ *ᵥ rhs
  fun j => h j+(-t*x-h v)

private def coefficient (q : ℕ) (E : CH.Digraph) (i j : ℕ) : ℝ :=
  (if i=j then 1 else 0)+(if E i j=true then (q:ℝ) else 0)-1

/-- At a fixed cycle the single real parameter t only needs to satisfy
t ≥ 1 and one affine inequality for each exterior label. -/
theorem exterior_test {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    (f : SharedArcFlatCut.Missing X F) (v : X.V) {C : Finset ℕ}
    (cy : Cycle (graph X.D F) X.V q C) (ac : f.val.1.val∈C) (vc : v.val∈C)
    (bc : f.val.2.val∉C) (t : ℝ) (one : 1≤t)
    (outside : let E := graph X.D F
               let z := tiltedPrices q E ⟨f.val.1,ac⟩ ⟨v,vc⟩ t ((w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ)))
               ∀i : X.V,i.val∉C → 0≤(∑j : C,if E i j=true then (q:ℝ)*z j else 0)-∑j,z j) :
    SharedArcFlatResponse.test (realMatrix q (graph X.D F) X.V)⁻¹ (fun i : X.V=>(w i:ℝ))
      (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2 v v≤0 := by
  let E := graph X.D F
  let a := f.val.1
  let x := (w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))
  let z := tiltedPrices q E ⟨a,ac⟩ ⟨v,vc⟩ t x
  let l (j : ℕ) := if h : j∈C then z ⟨j,h⟩ else 0
  have port (i : X.V) : (∑j : X.V,(realMatrix q E X.V i j-1)*l j)=∑j : C,coefficient q E i j*z j := by
    calc
      _ = ∑j∈X.V,coefficient q E i j*l j := by
        conv_rhs => rw [←sum_coe_sort]
        simp only [realMatrix_entry,Subtype.ext_iff,coefficient]
      _ = ∑j∈C,coefficient q E i j*l j := (sum_subset cy.sub (fun j _ off=>by simp [l,off])).symm
      _ = _ := by
        conv_lhs => rw [←sum_coe_sort]
        exact sum_congr rfl (fun j _=>by simp [l,j.property])
  have outs (j : C) : WeightedSD.row q E C (fun _=>1) j=(C.card:ℚ) := by
    have eq : (outN E C j).card=1 := cy.heads j j.property
    simp [WeightedSD.row,outW_eq_mass,mass,eq,cy.size,add_comm]
  have ins (j : C) : WeightedSD.col q E C (fun _=>1) j=(C.card:ℚ) := by
    have eq := cy.incoming j j.property
    change (C.filter (fun i=>E i j=true)).card=1 at eq
    simp [WeightedSD.col,inW,eq,cy.size,add_comm]
  have rows (j : C) := realMatrix_rational_rows (q:=q) (D:=E) (fun _=>1) (C.card:ℚ) (fun i hi=>outs ⟨i,hi⟩) j
  have cols (j : C) := realMatrix_rational_columns (q:=q) (D:=E) (fun _=>1) (C.card:ℚ) (fun i hi=>ins ⟨i,hi⟩) j
  obtain ⟨atV,inner⟩ := tilted_cycle (realMatrix q E C) (SharedArcFlatResponse.matrix_unit hq E C)
    (fun j=>by simpa [mulVec,dotProduct] using rows j) (fun j=>by simpa [vecMul,dotProduct] using cols j)
    (⟨v,vc⟩ : C) (⟨a,ac⟩ : C) t (-t*x)
  apply flexible_bound X hq small F wp wm wr pc f v t (fun j=>l j) (by simp [l,bc])
  · change l v=_
    simp only [l,dite_eq_left vc]
    change z ⟨v,vc⟩= -(_*_)/_
    rw [show z ⟨v,vc⟩= -t*x from atV]
    dsimp [x]; ring
  · intro i
    change 0≤(∑j : X.V,(realMatrix q E X.V i j-1)*l j)-(if i=v then 1 else 0)+(if i=a then t else 0)
    rw [port]
    by_cases ic : i.val∈C
    · have eq := inner ⟨i,ic⟩
      change (∑j : C,(realMatrix q E C ⟨i,ic⟩ j-1)*z j)-
        ((if (⟨i,ic⟩ : C)=⟨v,vc⟩ then 1 else 0)-(if (⟨i,ic⟩ : C)=⟨a,ac⟩ then t else 0))=_ at eq
      have nn : 0≤(t-1)/(Fintype.card C:ℝ) := div_nonneg (sub_nonneg.mpr one) (Nat.cast_nonneg _)
      simp only [realMatrix_entry,Subtype.ext_iff] at eq
      simp only [coefficient,Subtype.ext_iff]
      linarith only [eq,nn]
    · have off (j : C) : i.val≠j.val := fun eq=>ic (eq ▸ j.property)
      have iv : i≠v := fun eq=>ic (eq ▸ vc)
      have ia : i≠a := fun eq=>ic (eq ▸ ac)
      simpa only [coefficient,off,ite_false,zero_add,sub_mul,one_mul,ite_mul,zero_mul,
        sum_sub_distrib,ite_eq_right iv,ite_eq_right ia,sub_zero,add_zero] using (show
        0≤(∑j : C,if E i j=true then (q:ℝ)*z j else 0)-∑j,z j from outside i ic)

end LeanCH.BR.Closure.SingleArcCycleBalance
#print axioms LeanCH.BR.Closure.SingleArcCycleBalance.balance
#print axioms LeanCH.BR.Closure.SingleArcCycleBalance.cover_requires_order
#print axioms LeanCH.BR.Closure.SingleArcCycleBalance.flexible_bound
#print axioms LeanCH.BR.Closure.SingleArcCycleBalance.tilted_cycle
#print axioms LeanCH.BR.Closure.SingleArcCycleBalance.exterior_test
