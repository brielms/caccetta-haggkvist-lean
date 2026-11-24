import checkpoints.shen_extension.PunctureWalkCertificate

namespace LeanCH.BR.Closure.OneStepColumnMerge
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse
open SingleArcPunctureSign PunctureWalkCertificate
open scoped Matrix

/-- Native separation and saturation put every interior launch within horizon one. -/
theorem launch {q n} (X : Model q n) (hq : 2≤q) {a v : X.V} (va : v≠a) :
    ∃s,0<s ∧ s+1≤q+1 ∧ Walk X.D X.V a v s := by
  obtain ⟨z,zv,zvEdge,za⟩ := X.separated v v.property a a.property (fun e => va (Subtype.ext e.symm))
  obtain ⟨_,d,len,path⟩ := mem_ball.mp (X.sat a a.property z zv (by simp [za]))
  exact ⟨d+1,by omega,by omega,path.snoc v.property zvEdge⟩

/-- Only horizon one and coefficient zero are tested. -/
def OneStep {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (a b : V) (p : ℕ→ℚ)
    (k : rest a b) (h : rest a b→ℝ) : Prop :=
  ∀i : rest a b,(∑j : rest a b,residual q E a b i.val 1 0 j*h j)=
    -walkSum q E V 1 i.val k.val-price q E a b i.val 1 0 p*(p k.val:ℝ)

private theorem start {q : ℕ} {V : Finset ℕ} {E : CH.Digraph} (v b j : V) :
    probe q E 1 0 v b j= -(1:Matrix V V ℝ) v j := by simp [probe,walkSum]

private theorem unit_price {q : ℕ} {V : Finset ℕ} {E : CH.Digraph} (a b v : V) (p : ℕ→ℚ) :
    price q E a b v 1 0 p= -excess (realMatrix q E V) v b / ((q:ℝ)*(p a:ℝ)) := by
  rw [price,show boundary q E 1 0 v b b= -realMatrix q E V v b by
    simp only [boundary,zero_mul,zero_sub,pow_one,step,Matrix.sub_apply,sub_sub_cancel]]
  simp only [start,sum_neg_distrib,one_apply]
  simp [excess]; ring

/-- The rank-one correction to the negative identity cannot annihilate a
nonzero vector when its scalar contraction differs from minus one. -/
private theorem separate {I : Type*} [Fintype I] [DecidableEq I] (P β g : I→ℝ)
    (det : (∑i,P i*β i)≠ -1)
    (zero : ∀i : I,(∑j : I,(-(1:Matrix I I ℝ) i j-β i*P j)*g j)=0) : g=0 := by
  let c := ∑j,P j*g j
  have eq (i : I) : g i= -β i*c := by
    have e := zero i
    simp only [sub_mul,neg_mul,mul_assoc,sum_sub_distrib,sum_neg_distrib,←mul_sum,one_apply,ite_mul,one_mul,zero_mul] at e
    simp only [sum_ite_eq,mem_univ,ite_true] at e
    change _-β i*c=0 at e
    linarith only [e]
  have id : c= -(∑i,P i*β i)*c := by
    calc
      c=∑i,P i*(-β i*c) := sum_congr rfl fun i _ => congrArg (P i*·) (eq i)
      _=_ := by simp only [mul_neg,←mul_assoc,←sum_mul,neg_mul,sum_neg_distrib]
  have cz : c=0 := by
    by_contra cn
    apply det
    exact (mul_right_cancel₀ cn (show (∑i,P i*β i)*c=(-1)*c by linarith only [id]))
  funext i; simp [eq i,cz]

section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (F : Family)
  {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
  (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

include hq in
theorem one_of_fits (f : SharedArcFlatCut.Missing X F) (k : rest f.val.1 f.val.2) (h : rest f.val.1 f.val.2→ℝ)
    (fit : Fits q X.D (graph X.D F) f.val.1 f.val.2 p k h) :
    OneStep q (graph X.D F) f.val.1 f.val.2 p k h :=
  fun i => fit i.val 1 (by omega) (launch X hq (inside i).1) 0 (Or.inl rfl)

include hq pos wm wr pc in
/-- At horizon one the projection rows span the whole puncture. Hence the
walk equations fix every coordinate, even without assuming positivity. -/
theorem unique (f : SharedArcFlatCut.Missing X F) (k : rest f.val.1 f.val.2)
    (u v : rest f.val.1 f.val.2→ℝ)
    (fu : OneStep q (graph X.D F) f.val.1 f.val.2 p k u)
    (fv : OneStep q (graph X.D F) f.val.1 f.val.2 p k v) : u=v := by
  let a := f.val.1
  let b := f.val.2
  let E := graph X.D F
  let R := realMatrix q E X.V
  let C := excess R
  let P (i : X.V) : ℝ := p i
  let β (i : rest a b) := price q E a b i.val 1 0 p
  let K := puncture q E a b
  let g := K *ᵥ (u-v)
  have col : P ᵥ* R=1 := funext fun i => by simpa [P,R,E] using realMatrix_rational_columns p 1 pc i
  have row : R *ᵥ (fun i : X.V => (w i:ℝ))=1 := funext fun i => by simpa [R,E] using realMatrix_rational_rows w 1 wr i
  have total : (∑i,P i)=1 := by
    have h := dotProduct_mulVec P R (fun i : X.V => (w i:ℝ))
    rw [col,row,dotProduct_one,one_dotProduct] at h
    exact h.trans (real_mass_of_rational_probability w wm)
  have pzero : (P ᵥ* C) b=0 := by rw [show C=excess R from rfl,vecMul_excess,col,total]; simp
  have ab : a≠b := by
    intro eq
    have ed : X.D a b=true := f.property.1
    rw [eq] at ed
    exact loopfree X.free (by omega) b.property ed
  have bb : E b b=false := Bool.eq_false_iff.mpr (fun e => loopfree (PrivateArcEndpoints.graph_free X F) (by omega) b.property e)
  have splitB := split_sum a b ab (fun i=>P i*C i b)
  change (P ᵥ* C) b=_ at splitB
  rw [pzero,show C a b= -1 by simp [C,R,E,excess,realMatrix_entry,ab,show E a b=false from f.property.2],
    show C b b=0 by simp [C,R,excess,realMatrix_entry,bb]] at splitB
  have ppos : 0<P a := by change 0<(p a:ℝ); exact_mod_cast (pos _ a.property).2
  have qpos : (1:ℝ)<q := by exact_mod_cast (by omega : 1<q)
  have den : (q:ℝ)*P a≠0 := (mul_pos (zero_lt_one.trans qpos) ppos).ne'
  have det : (∑i : rest a b,P i.val*β i)≠ -1 := by
    have term (i : rest a b) : P i.val*β i= -(P i.val*C i.val b)/((q:ℝ)*P a) := by
      simp only [β,unit_price,C,R,P]; ring
    simp_rw [term]
    rw [←sum_div,sum_neg_distrib,show (∑i : rest a b,P i.val*C i.val b)=P a by linarith only [splitB]]
    intro eq
    have mul := (div_eq_iff den).mp eq
    nlinarith only [mul,mul_pos (sub_pos.mpr qpos) ppos]
  have ann (i : rest a b) : (∑j : rest a b,(-(1:Matrix (rest a b) (rest a b) ℝ) i j-β i*P j.val)*g j)=0 := by
    let z := candidate q E a b i.val 1 0 p
    have acc := accounts X hq F pos wm wr pc f i.val 1 (by omega) 0 (launch X hq (inside i).1)
    have id (j : rest a b) : z j= -(1:Matrix (rest a b) (rest a b) ℝ) i j-β i*P j.val := by
      simp only [z,candidate,start,one_apply,β,P,Subtype.val_inj]
    simp_rw [←id]
    change z ⬝ᵥ (K *ᵥ (u-v))=0
    rw [dotProduct_mulVec]
    change (∑j : rest a b,(z ᵥ* K) j*(u j-v j))=0
    simp_rw [show ∀j,(z ᵥ* K) j=residual q E a b i.val 1 0 j from acc.1,mul_sub]
    rw [sum_sub_distrib,fu i,fv i,sub_self]
  have zg := separate (fun i : rest a b => P i.val) β g det ann
  obtain ⟨J,right⟩ : ∃J : Matrix (rest a b) (rest a b) ℝ,K*J=1 := ⟨_,native_right X hq F pos wm wr pc f⟩
  have recover := congrArg (fun z => J *ᵥ z) zg
  change J *ᵥ (K *ᵥ (u-v))=J *ᵥ 0 at recover
  rwa [mulVec_mulVec,mul_eq_one_comm.mp right,one_mulVec,mulVec_zero,sub_eq_zero] at recover

include hq pos wm wr pc in
theorem one_iff (f : SharedArcFlatCut.Missing X F) (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (u : rest f.val.1 f.val.2→ℝ) :
    OneStep q (graph X.D F) f.val.1 f.val.2 p k u ↔ Fits q X.D (graph X.D F) f.val.1 f.val.2 p k u := by
  have fit := column_fits X hq F pos wm wr pc f k kb
  exact ⟨fun one => (unique X hq F pos wm wr pc f k u _ one (one_of_fits X hq F f k _ fit)) ▸ fit,
    one_of_fits X hq F f k u⟩


/-- The b-row pins the missing tail coordinate. Its coefficient there is
minus one; the separate old-price equation pins the b-coordinate. -/
def Column {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (a b : V) (p : ℕ→ℚ)
    (k : rest a b) (h : V→ℚ) : Prop :=
  OneStep q E a b p k (fun j=> (h j.val:ℝ)) ∧
    (q:ℚ)*p a*h b=p k.val ∧ (SingleArcTensorMerge.center q (insertArc E a b) V *ᵥ h) b=0

private theorem center_entry {q : ℕ} {V : Finset ℕ} {G : CH.Digraph} (i j : V) :
    SingleArcTensorMerge.center q G V i j=(if i=j then 1 else 0)+(if G i j=true then (q:ℚ) else 0)-1 := by
  by_cases ij : i=j <;> by_cases ed : G i j=true <;>
    simp [SingleArcTensorMerge.center,WeightedArithmetic.rationalMatrix,WeightedArithmetic.closedMatrix,adjacencyMatrix,ed,ij]

include hq pos wm wr pc in
theorem canonical (f : SharedArcFlatCut.Missing X F) (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let A := SingleArcTensorMerge.center q (insertArc E a b) X.V
    Column q E a b p k (fun i=>A⁻¹ i k.val) ∧
      ∀h : X.V→ℚ, Column q E a b p k h → h=(fun i=>A⁻¹ i k.val) := by
  intro E a b A
  let H := A⁻¹
  let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
  let d := (q:ℝ)*(p a:ℝ)*(w b:ℝ)
  have wb : 0<(w b:ℝ) := by exact_mod_cast (pos _ b.property).1
  have pa : 0<(p a:ℝ) := by exact_mod_cast (pos _ a.property).2
  have dp : 0<d := mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q)) pa) wb
  obtain ⟨inv,values⟩ := SingleArcTensorMerge.identify X hq F pos wm wr pc f
  have val (i : X.V) : T i k.val=d*(H i k.val:ℝ) := values i k.val
  have fit := column_fits X hq F pos wm wr pc f k kb
  have interior : (fun j : rest a b => T j.val k.val/d)=(fun j : rest a b => (H j.val k.val:ℝ)) := by
    funext j; rw [val]; field_simp [dp.ne']
  change Fits q X.D E a b p k (fun j : rest a b => T j.val k.val/d) at fit
  rw [interior] at fit
  have first := one_of_fits X hq F f k _ fit
  have hb : (q:ℚ)*p a*H b k.val=p k.val := by
    have e : T b k.val=(w b:ℝ)*(p k.val:ℝ) := by dsimp [T,test]; ring
    rw [val] at e
    have eq : (q:ℝ)*(p a:ℝ)*(H b k.val:ℝ)=(p k.val:ℝ) := by
      apply mul_left_cancel₀ wb.ne'
      dsimp [d] at e
      linear_combination e
    exact_mod_cast eq
  have pin : (A *ᵥ (fun j=>H j k.val)) b=0 := by
    change (A*H) b k.val=0
    rw [show A*H=1 from inv,one_apply_ne (inside k).2.symm]
  refine ⟨⟨first,hb,pin⟩,?_⟩
  intro h fact
  have eq := unique X hq F pos wm wr pc f k _ _ fact.1 first
  have eqb : h b=H b k.val := mul_left_cancel₀
    (mul_pos (by exact_mod_cast (by omega : 0<q)) (pos a a.property).2).ne' (fact.2.1.trans hb.symm)
  have away (j : X.V) (ja : j≠a) : h j=H j k.val := by
    by_cases jb : j=b
    · exact jb ▸ eqb
    · have jmem : j∈rest a b := by simp [rest,ja,jb]
      exact_mod_cast congrFun eq (⟨j,jmem⟩ : rest a b)
  have ab : a≠b := by
    intro same
    have native : X.D a b=true := f.property.1
    rw [same] at native
    exact loopfree X.free (by omega) b.property native
  have ed (i j) (e : E i j=true) : X.D i j=true := (mem_col.mp (active.mp e).choose_spec).2.2.2
  have ba : E b a=false := Bool.eq_false_iff.mpr fun e => digonfree X.free hq a.property b.property f.property.1 (ed _ _ e)
  have unit : A b a= -1 := by
    have no : insertArc E a b b a=false := by
      simp [insertArc,ba,show (b:ℕ)≠(a:ℕ) from fun e=>ab.symm (Subtype.ext e)]
    simp only [A,center_entry,ite_eq_right ab.symm,no,Bool.false_eq_true,ite_false]; norm_num
  have diff : (∑j : X.V,A b j*(h j-H j k.val))=0 := by
    simp only [mul_sub,sum_sub_distrib]
    change (A *ᵥ h) b-(A *ᵥ (fun j=>H j k.val)) b=0
    rw [fact.2.2,pin,sub_self]
  rw [sum_eq_single a (fun j _ ja => by rw [away j ja,sub_self,mul_zero]) (by simp),unit] at diff
  funext j
  by_cases ja : j=a
  · subst j; linarith only [diff]
  · exact away j ja

include hq pos wm wr pc in
/-- On the pinned one-step system, a positive solution automatically passes
all strict native merges. The proof uses only positivity of this column. -/
theorem cuts_of_column (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (h : X.V→ℚ)
    (col : Column q (graph X.D F) f.val.1 f.val.2 p k h) (live : ∀i,0<h i) :
    ∀S⊆X.V,2≤S.card → S≠X.V → SingleArcTensorMerge.cut q X.D X.V S h<0 := by
  obtain ⟨_,uniq⟩ := canonical X hq F pos wm wr pc f k kb
  rw [uniq h col] at live ⊢
  have subG (i j) (e : insertArc (graph X.D F) f.val.1 f.val.2 i j=true) : X.D i j=true := by
    by_cases pair : i=f.val.1.val ∧ j=f.val.2.val
    · exact pair.1 ▸ pair.2 ▸ f.property.1
    · have old : graph X.D F i j=true := by simpa [insertArc,pair] using e
      exact (mem_col.mp (active.mp old).choose_spec).2.2.2
  intro S sub size proper
  exact (SingleArcTensorMerge.ray_bound X hq small subG
    (SingleArcTensorMerge.identify X hq F pos wm wr pc f).1 sub size proper k.val).1 live

include hq pos wm wr pc in
/-- Excluding a positive solution to the pinned one-step system forces an
old successor in the specified parent's column. -/
theorem sign_of_exclusion (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (none : ∀h : X.V→ℚ, Column q (graph X.D F) f.val.1 f.val.2 p k h → (∀i,0<h i) →
      (∀S⊆X.V,2≤S.card → S≠X.V → SingleArcTensorMerge.cut q X.D X.V S h<0) → False) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v : X.V,E f.val.1 v=true ∧ T v k.val<0 := by
  intro E T
  let A := SingleArcTensorMerge.center q (insertArc E f.val.1 f.val.2) X.V
  let h (i : X.V) := A⁻¹ i k.val
  have col := (canonical X hq F pos wm wr pc f k kb).1
  by_contra! miss
  have live (i : X.V) : 0<h i := by
    have ht : 0<T i k.val := by
      by_cases ed : E f.val.1 i=true
      · exact lt_of_le_of_ne (miss i ed) (Ne.symm (SharedArcFlatArithmetic.nonzero hq
          (by simpa using funext (realMatrix_rational_rows w 1 wr))
          (by simpa using funext (realMatrix_rational_columns p 1 pc)) _ _ i k.val))
      · exact SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f i k.val
    have e := (SingleArcTensorMerge.identify X hq F pos wm wr pc f).2 i k.val
    change T i k.val=_ at e
    rw [e] at ht
    exact_mod_cast pos_of_mul_pos_right ht (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg q) (by exact_mod_cast (pos _ f.val.1.property).2.le))
      (by exact_mod_cast (pos _ f.val.2.property).1.le))
  exact none h col live (cuts_of_column X hq F pos wm wr pc small f k kb h col live)


/-- Old heads of k other than the edited head that at least one row in L
misses in the native host. -/
def missed (E D : CH.Digraph) (V L : Finset ℕ) (k b : ℕ) : Finset ℕ :=
  (outN E V k).erase b \ StrictFlatSubsetMerge.common D V L

include hq pos wm wr pc in
/-- Subtract a strict merge from the unit-excess row k of the pinned
column. The additive one is the column spike, and q*h(b)=p(k)/p(a).
Both amounts are on the very same column. -/
theorem expansion (f : SharedArcFlatCut.Missing X F) (k : rest f.val.1 f.val.2)
    (kb : graph X.D F k.val f.val.2=true) (h : X.V→ℚ)
    (col : Column q (graph X.D F) f.val.1 f.val.2 p k h) (live : ∀i,0<h i)
    {L : Finset ℕ} (kl : k.val.val∉L)
    (cut : SingleArcTensorMerge.cut q X.D X.V (insert k.val.val L) h<0) :
    let W := extendWeight X.V h
    1+mass L W < (q:ℚ)*h f.val.2+(q:ℚ)*mass (missed (graph X.D F) X.D X.V L k.val f.val.2) W := by
  intro W
  let E := graph X.D F
  let a := f.val.1
  let b := f.val.2
  let G := insertArc E a b
  let A := SingleArcTensorMerge.center q G X.V
  let N := outN E X.V k.val
  let U := N.erase b.val
  let C := StrictFlatSubsetMerge.common X.D X.V L
  let S := insert k.val.val L
  let C' := StrictFlatSubsetMerge.common X.D X.V S
  have hk := (canonical X hq F pos wm wr pc f k kb).2 h col
  have right : A*A⁻¹=1 := (SingleArcTensorMerge.identify X hq F pos wm wr pc f).1
  have eq : (A *ᵥ h) k.val=1 := by
    rw [hk]
    change (A*A⁻¹) k.val k.val=1
    rw [right,one_apply_eq]
  change (∑i : X.V,(WeightedArithmetic.rationalMatrix q (adjacencyMatrix G X.V) k.val i-1)*h i)=1 at eq
  simp only [sub_mul,one_mul,sum_sub_distrib] at eq
  change (WeightedArithmetic.rationalMatrix q (adjacencyMatrix G X.V) *ᵥ h) k.val-(∑i,h i)=1 at eq
  rw [←row_extendWeight q G X.V h k.val,WeightedSD.row,outW_eq_mass] at eq
  have ka : k.val.val≠a.val := fun e=>(inside k).1 (Subtype.ext e)
  have same : outN G X.V k.val=N := by simp [G,N,outN,insertArc,ka]
  rw [same] at eq
  have bn : b.val∈N := mem_outN.mpr ⟨b.property,kb⟩
  have decomp : W b+mass U W=mass N W := by
    exact (add_comm ..).trans (sum_erase_add N W bn)
  have selected : U∩C⊆C' := by
    intro y hy
    obtain ⟨yu,yc⟩ := mem_inter.mp hy
    have old := (mem_outN.mp (mem_of_mem_erase yu)).2
    have ed : X.D k.val y=true := (mem_col.mp (active.mp old).choose_spec).2.2.2
    exact mem_filter.mpr ⟨(mem_filter.mp yc).1,fun s hs => (mem_insert.mp hs).elim
      (fun same => same ▸ ed) (fun sl => (mem_filter.mp yc).2 s sl)⟩
  have nonneg (y) (yv : y∈X.V) : 0≤W y := by
    change 0≤extendWeight X.V h y
    rw [extendWeight_on X.V h (⟨y,yv⟩ : X.V)]; exact (live _).le
  have lcm := mass_mono selected (fun y hy => nonneg y (mem_filter.mp hy).1)
  have diff : U \ (U∩C)=U \ C := by ext i; simp
  have split : mass (U \ C) W+mass (U∩C) W=mass U W := by
    unfold mass
    rw [←diff]
    exact sum_sdiff inter_subset_left
  have ins : mass S W=W k.val+mass L W := sum_insert kl
  change mass S W+q*mass C' W-(∑i,h i)<0 at cut
  rw [ins] at cut
  change W k.val+q*mass N W-(∑i,h i)=1 at eq
  change 1+mass L W < (q:ℚ)*h b+(q:ℚ)*mass (U \ C) W
  have wb : W b=h b := extendWeight_on X.V h b
  rw [wb] at decomp
  linarith only [eq,cut,mul_le_mul_of_nonneg_left lcm (Nat.cast_nonneg q : (0:ℚ)≤q),
    congrArg (fun x : ℚ=>(q:ℚ)*x) decomp,congrArg (fun x : ℚ=>(q:ℚ)*x) split]

/-- Any two labels form a proper subset since the punctured parent k
is distinct from both endpoints. -/
private theorem pair_proper {V : Finset ℕ} (a b : V) (ab : a≠b) (k : rest a b) (j : V) :
    insert k.val.val {j.val}≠V := by
  intro eq
  have inc : V⊆insert k.val.val {j.val} := eq.ge
  have am := inc a.property
  have bm := inc b.property
  simp only [mem_insert,mem_singleton] at am bm
  exact ab (Subtype.ext ((am.resolve_left (fun e=>(inside k).1 (Subtype.ext e.symm))).trans
    (bm.resolve_left (fun e=>(inside k).2 (Subtype.ext e.symm))).symm))

include hq pos wm wr pc in
/-- A cover of the reduced old head set at a parent of price no greater
than p(a) rules out the column and forces a strictly negative entry at an
actual old successor. The covering row can be anywhere in the native graph. -/
theorem cover_sign (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (cheap : p k.val≤p f.val.1)
    (j : X.V) (jk : j≠k.val)
    (cover : ∀x∈X.V,x≠f.val.2.val → graph X.D F k.val x=true → X.D j x=true) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v : X.V,E f.val.1 v=true ∧ T v k.val<0 := by
  apply sign_of_exclusion X hq F pos wm wr pc small f k kb
  intro h col live cuts
  let a := f.val.1
  let b := f.val.2
  have ab : a≠b := by
    intro eq
    have ed : X.D a b=true := f.property.1
    rw [eq] at ed
    exact loopfree X.free (by omega) b.property ed
  have kl : k.val.val∉({j.val}:Finset ℕ) := by simpa using (show k.val.val≠j.val from fun e=>jk (Subtype.ext e.symm))
  have sub : ({j.val}:Finset ℕ)⊆X.V := singleton_subset_iff.mpr j.property
  have strict := cuts _ (insert_subset_iff.mpr ⟨k.val.property,sub⟩)
    (by rw [card_insert_of_notMem kl,card_singleton]) (pair_proper a b ab k j)
  have gain := expansion X hq F pos wm wr pc f k kb h col live kl strict
  have empty : missed (graph X.D F) X.D X.V {j.val} k.val b=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨old,abs⟩ := mem_sdiff.mp hx
    obtain ⟨xb,xn⟩ := mem_erase.mp old
    obtain ⟨xv,ed⟩ := mem_outN.mp xn
    exact abs (mem_filter.mpr ⟨xv,by simpa using cover x xv xb ed⟩)
  change 1+mass {j.val} (extendWeight X.V h) <
    (q:ℚ)*h b+q*mass (missed (graph X.D F) X.D X.V {j.val} k.val b) (extendWeight X.V h) at gain
  rw [empty] at gain
  simp only [mass,sum_singleton,sum_empty,mul_zero,add_zero,extendWeight_on] at gain
  have low : (q:ℚ)*h b≤1 := by
    apply le_of_mul_le_mul_left _ (pos a a.property).2
    calc
      p a*((q:ℚ)*h b)=(q:ℚ)*p a*h b := by ring
      _=p k.val := col.2.1
      _≤p a*1 := by simpa using cheap
  linarith only [gain,low,live j]


include hq pos wm wr pc in
/-- A cheap old parent must distinguish its reduced head set from every
other native row. This formulation supplies an actual missing incidence. -/
theorem distinguishes (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (cheap : p k.val≤p f.val.1)
    (j : X.V) (jk : j≠k.val) :
    ∃x : X.V,x≠f.val.2 ∧ graph X.D F k.val x=true ∧ X.D j x=false := by
  by_contra! none
  have cover (x) (xv : x∈X.V) (xb : x≠f.val.2.val) (ed : graph X.D F k.val x=true) : X.D j x=true := by
    let u : X.V := ⟨x,xv⟩
    have ne : u≠f.val.2 := fun e=>xb (congrArg Subtype.val e)
    by_contra off
    exact none u ne ed (Bool.eq_false_iff.mpr off)
  obtain ⟨s,_,bad⟩ := cover_sign X hq F pos wm wr pc small f k kb cheap j jk cover
  exact bad.not_ge (SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f s k.val).le

include hq pos wm wr pc in
/-- Native separation supplies a second distinct ordinary head. One
other head alone would be covered by a different parent of that head. -/
theorem two_other_heads (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (cheap : p k.val≤p f.val.1) :
    ∃u v : X.V,u≠f.val.2 ∧ v≠f.val.2 ∧ u≠v ∧ graph X.D F k.val u=true ∧ graph X.D F k.val v=true := by
  obtain ⟨u,ub,ku,_⟩ := distinguishes X hq F pos wm wr pc small f k kb cheap f.val.2 (inside k).2.symm
  obtain ⟨j,jv,ju,jb⟩ := X.separated u u.property f.val.2 f.val.2.property (fun same=>ub (Subtype.ext same.symm))
  let z : X.V := ⟨j,jv⟩
  have zk : z≠k.val := by
    intro eq
    have ed : X.D z f.val.2=false := jb
    rw [eq] at ed
    exact Bool.noConfusion (ed.symm.trans (mem_col.mp (active.mp kb).choose_spec).2.2.2)
  obtain ⟨v,vb,kv,zv⟩ := distinguishes X hq F pos wm wr pc small f k kb cheap z zk
  exact ⟨u,v,ub,vb,fun eq=>by rw [←eq] at zv; exact Bool.noConfusion (zv.symm.trans ju),ku,kv⟩


/-- Coefficient of a native merge on a full label. -/
def mergeCoefficient (q : ℕ) (D : CH.Digraph) (V S : Finset ℕ) (i : V) : ℚ :=
  (if i.val∈S then 1 else 0)+(if i.val∈StrictFlatSubsetMerge.common D V S then (q:ℚ) else 0)-1

private theorem mask_mass {V U : Finset ℕ} (sub : U⊆V) (h : V→ℚ) :
    (∑i : V,if i.val∈U then h i else 0)=mass U (extendWeight V h) := by
  have same : V.filter (fun i=>i∈U)=U := by ext i; simp only [mem_filter]; exact and_iff_right_of_imp (fun hi=>sub hi)
  have eq (i : V) : (if i.val∈U then h i else 0)=(fun x=>if x∈U then extendWeight V h x else 0) i.val := by
    rw [←extendWeight_on V h i]
  rw [sum_congr rfl (fun i _=>eq i),sum_coe_sort V (fun x=>if x∈U then extendWeight V h x else 0),←sum_filter,same]; rfl

private theorem contract_cut {q : ℕ} {V S : Finset ℕ} (D : CH.Digraph) (sub : S⊆V) (h : V→ℚ) :
    (∑i : V,mergeCoefficient q D V S i*h i)=SingleArcTensorMerge.cut q D V S h := by
  let C := StrictFlatSubsetMerge.common D V S
  have term (i : V) : mergeCoefficient q D V S i*h i=
      (if i.val∈S then h i else 0)+q*(if i.val∈C then h i else 0)-h i := by
    change ((if i.val∈S then 1 else 0)+(if i.val∈C then (q:ℚ) else 0)-1)*h i=_
    by_cases si : i.val∈S <;> by_cases ci : i.val∈C <;> simp [si,ci]
    ring
  simp_rw [term]
  rw [sum_sub_distrib,sum_add_distrib,←mul_sum,mask_mass sub,mask_mass (show C⊆V from filter_subset ..)]
  rfl

include hq pos wm wr pc in
/-- Signed combinations of the recovered row equations may be paid for by
any nonnegative combination of strict merges and a multiple of the fixed
head coordinate. One positive merge gives a contradiction even at equality.
All certificate inputs are graph incidences, rational multipliers and prices. -/
theorem paid_sign (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    {I : Type*} [Fintype I] (sets : I→Finset ℕ) (coeff : I→ℚ)
    (legal : ∀i,sets i⊆X.V ∧ 2≤(sets i).card ∧ sets i≠X.V)
    (nn : ∀i,0≤coeff i) (used : ∃i,0<coeff i)
    (y : X.V→ℚ) (t : ℚ)
    (paid : ∀j : X.V,(y ᵥ* SingleArcTensorMerge.center q (insertArc (graph X.D F) f.val.1 f.val.2) X.V) j ≤
      (∑i,coeff i*mergeCoefficient q X.D X.V (sets i) j)+(if j=f.val.2 then t else 0))
    (gain : t*p k.val≤(q:ℚ)*p f.val.1*y k.val) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v : X.V,E f.val.1 v=true ∧ T v k.val<0 := by
  classical
  apply sign_of_exclusion X hq F pos wm wr pc small f k kb
  intro h col hp bounds
  let A := SingleArcTensorMerge.center q (insertArc (graph X.D F) f.val.1 f.val.2) X.V
  have hk := (canonical X hq F pos wm wr pc f k kb).2 h col
  have right : A*A⁻¹=1 := (SingleArcTensorMerge.identify X hq F pos wm wr pc f).1
  have spike : A *ᵥ h=(fun i=>(1:Matrix X.V X.V ℚ) i k.val) := by
    rw [hk]; funext i; exact congrFun (congrFun right i) k.val
  have left : (∑j,(y ᵥ* A) j*h j)=y k.val := by
    change (y ᵥ* A) ⬝ᵥ h=_
    rw [←dotProduct_mulVec,spike]
    simp [dotProduct,one_apply,mul_ite]
  have upper := sum_le_sum (s:=univ) fun j _ => mul_le_mul_of_nonneg_right (paid j) (hp j).le
  change (∑j,(y ᵥ* A) j*h j)≤_ at upper
  rw [left] at upper
  simp only [add_mul,sum_add_distrib,ite_mul,zero_mul,sum_ite_eq',mem_univ,ite_true] at upper
  have bank : (∑j : X.V,(∑i,coeff i*mergeCoefficient q X.D X.V (sets i) j)*h j)=
      ∑i,coeff i*SingleArcTensorMerge.cut q X.D X.V (sets i) h := by
    simp_rw [sum_mul,mul_assoc]
    rw [sum_comm]; simp_rw [←mul_sum,contract_cut X.D (legal _).1]
  rw [bank] at upper
  have neg : (∑i,coeff i*SingleArcTensorMerge.cut q X.D X.V (sets i) h)<0 := by
    apply sum_neg'
    · intro i _; exact mul_nonpos_of_nonneg_of_nonpos (nn i) (bounds _ (legal i).1 (legal i).2.1 (legal i).2.2).le
    · obtain ⟨i,hi⟩ := used
      exact ⟨i,mem_univ _,mul_neg_of_pos_of_neg hi (bounds _ (legal i).1 (legal i).2.1 (legal i).2.2)⟩
  have rate : 0<(q:ℚ)*p f.val.1 := mul_pos (by exact_mod_cast (by omega : 0<q)) (pos _ f.val.1.property).2
  have anchored := col.2.1
  have low : t*h f.val.2≤y k.val := by
    apply le_of_mul_le_mul_left _ rate
    calc
      (q:ℚ)*p f.val.1*(t*h f.val.2)=t*((q:ℚ)*p f.val.1*h f.val.2) := by ring
      _≤_ := anchored ▸ gain
  linarith only [upper,neg,low]


include hq pos wm wr pc in
/-- The cover witness exists on purely graph grounds if k has at most
one old head besides b. In this lemma the sign is obtained from the cover
directly, without first invoking positivity on the successor rectangle. -/
theorem thin_sign (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (cheap : p k.val≤p f.val.1)
    (thin : ((outN (graph X.D F) X.V k.val).erase f.val.2.val).card≤1) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v : X.V,E f.val.1 v=true ∧ T v k.val<0 := by
  let U := (outN (graph X.D F) X.V k.val).erase f.val.2.val
  by_cases live : U.Nonempty
  · obtain ⟨u,hu⟩ := live
    obtain ⟨ub,ou⟩ := mem_erase.mp hu
    obtain ⟨j,jv,ju,jb⟩ := X.separated u (outN_subset ou) f.val.2 f.val.2.property ub.symm
    let z : X.V := ⟨j,jv⟩
    have zk : z≠k.val := by
      intro eq
      have e : X.D z f.val.2=false := jb
      rw [eq] at e
      exact Bool.noConfusion (e.symm.trans (mem_col.mp (active.mp kb).choose_spec).2.2.2)
    apply cover_sign X hq F pos wm wr pc small f k kb cheap z zk
    intro x xv xb kx
    have eq := card_le_one.mp thin x (mem_erase.mpr ⟨xb,mem_outN.mpr ⟨xv,kx⟩⟩) u hu
    exact eq ▸ ju
  · apply cover_sign X hq F pos wm wr pc small f k kb cheap f.val.2 (inside k).2.symm
    exact fun x xv xb kx => (live ⟨x,mem_erase.mpr ⟨xb,mem_outN.mpr ⟨xv,kx⟩⟩⟩).elim

include hq pos wm wr pc in
/-- For any one chosen admissible merge (including the two endpoints),
the sign is equivalent to a rational full-label inequality. The right
side uses no inverse, prices, or tensor entries. -/
theorem fixed_merge_iff (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (S : Finset ℕ) (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V) :
    let E := graph X.D F
    let A := SingleArcTensorMerge.center q (insertArc E f.val.1 f.val.2) X.V
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    (∃v : X.V,E f.val.1 v=true ∧ T v k.val<0) ↔
      ∃y : X.V→ℚ,0≤y k.val ∧ ∀j,(y ᵥ* A) j≤mergeCoefficient q X.D X.V S j := by
  intro E A T
  constructor
  · rintro ⟨v,_,bad⟩
    obtain ⟨inv,eq⟩ := SingleArcTensorMerge.identify X hq F pos wm wr pc f
    let H := A⁻¹
    let M := mergeCoefficient q X.D X.V S
    have scale : 0<(q:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ) := mul_pos
      (mul_pos (by exact_mod_cast (by omega : 0<q)) (by exact_mod_cast (pos _ f.val.1.property).2))
      (by exact_mod_cast (pos _ f.val.2.property).1)
    have hv : H v k.val<0 := by
      change test _ _ _ _ _ _ _ _<0 at bad
      rw [eq] at bad
      exact_mod_cast neg_of_mul_neg_right bad scale.le
    let c := (M ᵥ* H) k.val
    let t := max 0 (-c/(-H v k.val))
    have tpos : 0≤t := le_max_left .. 
    have pay : -c≤t*(-H v k.val) := (div_le_iff₀ (neg_pos.mpr hv)).mp (le_max_right ..)
    let unit (j : X.V) := (1:Matrix X.V X.V ℚ) v j
    let y := (M-t • unit) ᵥ* H
    have atK : y k.val=c-t*H v k.val := by
      simp only [y,sub_vecMul,smul_vecMul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      have hit : (unit ᵥ* H) k.val=H v k.val := by
        change ((1:Matrix X.V X.V ℚ)*H) v k.val=_
        rw [one_mul]
      rw [hit]
    refine ⟨y,by rw [atK]; linarith only [pay],?_⟩
    intro j
    have left : H*A=1 := mul_eq_one_comm.mp inv
    simp only [y,vecMul_vecMul,left,vecMul_one,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    have uj : 0≤unit j := by simp only [unit,one_apply]; split <;> norm_num
    exact sub_le_self _ (mul_nonneg tpos uj)
  · rintro ⟨y,yk,le⟩
    apply paid_sign X hq F pos wm wr pc small f k kb (I:=Unit) (fun _=>S) (fun _=>1)
      (fun _=>⟨sub,size,proper⟩) (by intros; norm_num) ⟨(),by norm_num⟩ y 0
    · intro j; simpa using le j
    · simpa using mul_nonneg
        (mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) (pos _ f.val.1.property).2.le) yk

include hq pos wm wr pc in
/-- If the edited head supplies the cover, the same head also appears on
the left of the strict merge. This permits parent prices up to q/(q-1)
times the tail price, including equality. -/
theorem head_cover_sign (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (cost : ((q:ℚ)-1)*p k.val≤(q:ℚ)*p f.val.1)
    (cover : ∀x∈X.V,x≠f.val.2.val → graph X.D F k.val x=true → X.D f.val.2 x=true) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v : X.V,E f.val.1 v=true ∧ T v k.val<0 := by
  apply sign_of_exclusion X hq F pos wm wr pc small f k kb
  intro h col live cuts
  let b := f.val.2
  have ab : f.val.1≠b := by
    intro same
    have ed : X.D f.val.1 b=true := f.property.1
    rw [same] at ed
    exact loopfree X.free (by omega) b.property ed
  have outside : k.val.val∉({b.val}:Finset ℕ) := by
    simpa using (show k.val.val≠b.val from fun e=>(inside k).2 (Subtype.ext e))
  have strict := cuts _ (insert_subset_iff.mpr ⟨k.val.property,singleton_subset_iff.mpr b.property⟩)
    (by rw [card_insert_of_notMem outside,card_singleton]) (pair_proper _ b ab k b)
  have gain := expansion X hq F pos wm wr pc f k kb h col live outside strict
  have empty : missed (graph X.D F) X.D X.V {b.val} k.val b=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨old,abs⟩ := mem_sdiff.mp hx
    obtain ⟨xb,xn⟩ := mem_erase.mp old
    obtain ⟨xv,ed⟩ := mem_outN.mp xn
    exact abs (mem_filter.mpr ⟨xv,by simpa using cover x xv xb ed⟩)
  change 1+mass {b.val} (extendWeight X.V h) <
    (q:ℚ)*h b+q*mass (missed (graph X.D F) X.D X.V {b.val} k.val b) (extendWeight X.V h) at gain
  rw [empty] at gain
  simp only [mass,sum_singleton,sum_empty,mul_zero,add_zero,extendWeight_on] at gain
  have rate : 0<(q:ℚ)*p f.val.1 := mul_pos (by exact_mod_cast (by omega : 0<q)) (pos _ f.val.1.property).2
  have below : 1<((q:ℚ)-1)*h b := by linarith only [gain]
  have contradiction := mul_lt_mul_of_pos_left below rate
  have pin : (q:ℚ)*p f.val.1*h b=p k.val := col.2.1
  rw [mul_one,show (q:ℚ)*p f.val.1*(((q:ℚ)-1)*h b)=((q:ℚ)-1)*((q:ℚ)*p f.val.1*h b) by ring,pin] at contradiction
  exact (not_lt_of_ge cost) contradiction

include hq pos wm wr pc in
/-- The old column law budgets the entire parent set. A sufficiently
large set of parents covered by b supplies both indices of a negative
entry without specifying a parent of small price. -/
theorem covered_parents_sign (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (P : Finset ℕ) (live : P.Nonempty) (parents : P⊆inN (graph X.D F) X.V f.val.2)
    (cover : ∀k∈P,∀x∈X.V,x≠f.val.2.val → graph X.D F k x=true → X.D f.val.2 x=true)
    (size : ((q:ℚ)-1)*(1-p f.val.2)≤(q:ℚ)^2*P.card*p f.val.1) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃k : X.V,k.val∈P ∧ E k f.val.2=true ∧ ∃v : X.V,E f.val.1 v=true ∧ T v k<0 := by
  intro E T
  let a := f.val.1
  let b := f.val.2
  let N := inN E X.V b
  have inc : mass P p≤mass N p := mass_mono parents (fun i hi=>(pos i (mem_inN.mp hi).1).2.le)
  have balance : p b+(q:ℚ)*mass N p=1 := by
    simpa [N,E,b,WeightedSD.col,inW,inN,mass,sum_filter] using pc f.val.2 f.val.2.property
  have qpos : 0<(q:ℚ) := by exact_mod_cast (by omega : 0<q)
  have cheap : ∃i∈P,((q:ℚ)-1)*p i≤(q:ℚ)*p a := by
    by_contra! none
    have total := sum_lt_sum_of_nonempty live none
    simp only [sum_const,nsmul_eq_mul,←mul_sum] at total
    change (P.card:ℚ)*((q:ℚ)*p a)<((q:ℚ)-1)*mass P p at total
    have one : (1:ℚ)≤q := by exact_mod_cast (by omega : 1≤q)
    have upper := mul_le_mul_of_nonneg_left inc (sub_nonneg.mpr one)
    have strict := mul_lt_mul_of_pos_left (total.trans_le upper) qpos
    change ((q:ℚ)-1)*(1-p b)≤(q:ℚ)^2*P.card*p a at size
    rw [show 1-p b=(q:ℚ)*mass N p by linarith only [balance]] at size
    linarith only [strict,size]
  obtain ⟨i,mem,price⟩ := cheap
  obtain ⟨iv,edge⟩ := mem_inN.mp (parents mem)
  let v : X.V := ⟨i,iv⟩
  have va : v≠a := by
    intro same
    have ed : E v b=true := edge
    rw [same] at ed
    exact Bool.noConfusion (ed.symm.trans f.property.2)
  have vb : v≠b := by
    intro same
    have ed : X.D v b=true := (mem_col.mp (active.mp edge).choose_spec).2.2.2
    rw [same] at ed
    exact loopfree X.free (by omega) b.property ed
  let k : rest a b := ⟨v,mem_erase.mpr ⟨vb,mem_erase.mpr ⟨va,mem_univ _⟩⟩⟩
  exact ⟨v,mem,edge,head_cover_sign X hq F pos wm wr pc small f k edge price (cover i mem)⟩

include hq pos wm wr pc in
/-- The two endpoints are always an available merge in a parent column.
A multiplier for this one explicit merge discharges the capstone pivot. -/
theorem endpoint_progress (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (y : X.V→ℚ) (yk : 0≤y k.val)
    (bound : ∀j,(y ᵥ* SingleArcTensorMerge.center q (insertArc (graph X.D F) f.val.1 f.val.2) X.V) j≤
      mergeCoefficient q X.D X.V {f.val.1.val,f.val.2.val} j)
    (B : Finset ℕ) (K : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (c : ℚ) :
    SharedArcPivotGate.ProgressAt X F B K prices c := by
  let a := f.val.1
  let b := f.val.2
  have ab : a.val≠b.val := by
    intro same
    have ed : X.D a.val b.val=true := f.property.1
    rw [same] at ed
    exact loopfree X.free (by omega) b.property ed
  have sub : ({a.val,b.val}:Finset ℕ)⊆X.V := insert_subset_iff.mpr ⟨a.property,singleton_subset_iff.mpr b.property⟩
  have proper : ({a.val,b.val}:Finset ℕ)≠X.V := by
    intro eq
    have mem := eq.ge k.val.property
    simp only [mem_insert,mem_singleton] at mem
    exact mem.elim (fun h=>(inside k).1 (Subtype.ext h)) (fun h=>(inside k).2 (Subtype.ext h))
  obtain ⟨v,_,sign⟩ := (fixed_merge_iff X hq F pos wm wr pc small f k kb _ sub (by simp [ab]) proper).mpr ⟨y,yk,bound⟩
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,pos,wm,wr,pc,f,v,k.val,sign⟩)))

end Native
end LeanCH.BR.Closure.OneStepColumnMerge
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.unique
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.one_iff
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.canonical
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.cuts_of_column
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.sign_of_exclusion
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.expansion
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.cover_sign
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.two_other_heads
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.paid_sign
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.thin_sign
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.fixed_merge_iff
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.head_cover_sign
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.covered_parents_sign
#print axioms LeanCH.BR.Closure.OneStepColumnMerge.endpoint_progress
