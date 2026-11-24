import checkpoints.shen_extension.OneStepColumnMerge

namespace LeanCH.BR.Closure.EndpointLayerWitness
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse
open SingleArcPunctureSign OneStepColumnMerge
open scoped Matrix

section Layer
variable {V : Finset ℕ} (D : CH.Digraph) (q : ℕ) (a : V)

/-- Multiplicity of two-step walks to j when the first step a→s is
weighted by z(s). The support hypothesis in the results enforces that step. -/
def load (z : V→ℕ) (j : V) : ℕ := ∑s : V,if D s j then z s else 0

/-- A nonhead exterior to the tail's outgoing neighbourhood. -/
def Exterior (j : V) : Prop := j≠a ∧ D a j=false

/-- All exterior loads, with zero as a fallback for an empty exterior. -/
def peak (z : V→ℕ) : ℕ := (univ.filter (fun j : V=>j≠a ∧ D a j=false)).sup (load D z)

def weightTotal (z : V→ℕ) : ℕ := ∑s,z s

/-- The signed row is integer-valued. Every coordinate off the tail is nonnegative. -/
def multiplier (z : V→ℕ) (j : V) : ℚ :=
  (q:ℚ)*(z j:ℚ) - (if j=a then (q:ℚ)*((weightTotal z:ℚ)-(q:ℚ)*peak D a z)-1 else 0)

theorem apply_center (y : V→ℚ) (j : V) :
    (y ᵥ* SingleArcTensorMerge.center q D V) j =
    y j+(q:ℚ)*(∑s : V,if D s j then y s else 0)-∑s,y s := by
  change (∑i,y i*(WeightedArithmetic.rationalMatrix q (adjacencyMatrix D V) i j-1))=_
  simp_rw [mul_sub,mul_one]
  rw [sum_sub_distrib]
  change (y ᵥ* WeightedArithmetic.rationalMatrix q (adjacencyMatrix D V)) j-_ = _
  rw [WeightedArithmetic.rational_vecMul_apply]
  congr 2
  congr 1
  apply sum_congr rfl
  intro i _
  cases ed : D i j <;> simp [adjacencyMatrix,ed]

private theorem evaluate (z : V→ℕ) (j : V) :
    let d : ℚ := ∑s : V,(z s:ℚ)
    let c := (q:ℚ)*(d-q*peak D a z)-1
    (multiplier D q a z ᵥ* SingleArcTensorMerge.center q D V) j =
      (q:ℚ)*((z j:ℚ)+q*load D z j-d) -
      c*((if j=a then (1:ℚ) else 0)+(if D a j then (q:ℚ) else 0)-1) := by
  intro d c
  have castd : (weightTotal z:ℚ)=d := by simp [weightTotal,d]
  have val (i : V) : multiplier D q a z i=(q:ℚ)*z i-(if i=a then c else 0) := by
    simp only [multiplier,c,castd]
  have mass : (∑s : V,multiplier D q a z s)=(q:ℚ)*d-c := by
    simp_rw [val]; rw [sum_sub_distrib,←mul_sum]; simp [d]
  have bank : (∑s : V,if D s j then multiplier D q a z s else 0)=
      (q:ℚ)*load D z j-(if D a j then c else 0) := by
    have term (i : V) : (if D i j then multiplier D q a z i else 0)=
        (q:ℚ)*((if D i j then z i else 0:ℕ):ℚ)-(if i=a then (if D a j then c else 0) else 0) := by
      by_cases ia : i=a
      · subst i; cases e : D a j <;> simp [val]
      · cases e : D i j <;> simp [val,ia]
    simp_rw [term]
    rw [sum_sub_distrib,←mul_sum]; simp [load]
  rw [apply_center,bank,mass,val]
  split <;> split <;> ring

/-- Every exterior two-step arrival has a return of exactly q−1 to a.
The original two arcs followed by that return form a shortest closed walk. -/
theorem shell (free : QFree D V q) (sat : BRsub.Sat q D V) (hq : 2≤q)
    {j s : V} (outside : Exterior D a j) (first : D a s=true) (second : D s j=true) :
    Walk D V j a (q-1) ∧ ∀l,Walk D V j a l → q-1≤l := by
  obtain ⟨_,l,le,ret⟩ := mem_ball.mp (sat j j.property a a.property (by simp [outside.2]))
  have lower (t) (path : Walk D V j a t) : q-1≤t := by
    by_contra! short
    exact free a (t+1+1) (by omega) (by omega) (.step s.property first (.step j.property second path))
  exact ⟨le_antisymm le (lower l ret) ▸ ret,lower⟩

private theorem load_zero (z : V→ℕ) (off : ∀s : V,D a s=false → z s=0) (j : V)
    (none : ∀s : V,D a s=true → D s j=false) : load D z j=0 := by
  apply sum_eq_zero
  intro s _
  cases ed : D a s with
  | false => simp [off s ed]
  | true => simp [none s ed]

private theorem present (z : V→ℕ) (off : ∀s : V,D a s=false → z s=0) {j : V}
    (live : 0<load D z j) : ∃s : V,D a s=true ∧ D s j=true := by
  by_contra! none
  have vanish := load_zero D a z off j (fun s hs=>Bool.eq_false_iff.mpr (none s hs))
  omega

private theorem peak_le (z : V→ℕ) {j : V} (ext : Exterior D a j) :
    load D z j≤peak D a z := le_sup (f:=load D z) (mem_filter.mpr ⟨mem_univ _,ext⟩)

/-- A strictly positive peak is attained on the length-(q+1) cycle shell. -/
theorem peak_shell (free : QFree D V q) (sat : BRsub.Sat q D V) (hq : 2≤q)
    (z : V→ℕ) (off : ∀s : V,D a s=false → z s=0) (nz : 0<peak D a z) :
    ∃j s : V,Exterior D a j ∧ D a s=true ∧ D s j=true ∧ load D z j=peak D a z ∧
      Walk D V j a (q-1) ∧ ∀l,Walk D V j a l → q-1≤l := by
  classical
  let U := univ.filter (fun j : V=>j≠a ∧ D a j=false)
  have live : U.Nonempty := by
    by_contra e
    have empty := not_nonempty_iff_eq_empty.mp e
    change 0<U.sup (load D z) at nz
    simp [empty] at nz
  obtain ⟨j,hj,hmax⟩ := exists_max_image U (load D z) live
  have ext : Exterior D a j := (mem_filter.mp hj).2
  have eq := le_antisymm (peak_le D a z ext) (show peak D a z≤load D z j from Finset.sup_le (fun i hi=>hmax i hi))
  obtain ⟨s,hs,sj⟩ := present D a z off (eq.symm ▸ nz)
  exact ⟨j,s,ext,hs,sj,eq,shell D q a free sat hq ext hs sj⟩

/-- An incidence-only test gives the endpoint multiplier even when no old
parent is covered. Equality is allowed on common heads. -/
theorem witness (free : QFree D V q) (hq : 2≤q) (b : V) (z : V→ℕ)
    (off : ∀s : V,D a s=false → z s=0) (total : 0<∑s : V,z s)
    (pay : ∀s : V,D a s=true →
      let lhs := z s+q*(load D z s+(q-1)*peak D a z)
      let rhs := q*∑t : V,z t
      lhs<rhs ∨ (lhs=rhs ∧ D b s=true)) :
    (∀k : V,k≠a → 0≤multiplier D q a z k) ∧
    ∀j : V,(multiplier D q a z ᵥ* SingleArcTensorMerge.center q D V) j≤
      OneStepColumnMerge.mergeCoefficient q D V {a.val,b.val} j := by
  classical
  refine ⟨fun k ka=>by simp only [multiplier,ka,ite_false,sub_zero]; positivity,?_⟩
  let d : ℚ := ∑i : V,(z i:ℚ)
  let m : ℚ := peak D a z
  have qtwo : (2:ℚ)≤q := by exact_mod_cast hq
  have dp : (1:ℚ)≤d := by dsimp [d]; exact_mod_cast (show 1≤∑i : V,z i from total)
  intro j
  let M := OneStepColumnMerge.mergeCoefficient q D V {a.val,b.val} j
  have floor : -1≤M := by
    unfold M OneStepColumnMerge.mergeCoefficient
    split <;> split <;> linarith only [qtwo]
  rw [evaluate]
  change (q:ℚ)*(z j+q*load D z j-d)-(q*(d-q*m)-1)*
    ((if j=a then 1 else 0)+(if D a j then (q:ℚ) else 0)-1)≤M
  by_cases ja : j=a
  · subst j
    have loop : D a a=false := Bool.eq_false_iff.mpr (loopfree free (by omega) a.property)
    have zero := load_zero D a z off a (fun s ed => Bool.eq_false_iff.mpr (fun back =>
      free a 2 (by omega) (by omega) (.step s.property ed (.step a.property back (.refl _)))))
    simp [loop,off a loop,zero]
    exact le_trans (by nlinarith only [mul_le_mul_of_nonneg_left dp (qtwo.trans' (by norm_num : (0:ℚ)≤2)),qtwo]) floor
  · cases ed : D a j with
    | false =>
      have bound : (load D z j:ℚ)≤m := by dsimp [m]; exact_mod_cast peak_le D a z ⟨ja,ed⟩
      simp only [ja,ite_false,Bool.false_eq_true,off j ed,Nat.cast_zero,zero_add]
      apply le_trans _ floor
      nlinarith only [mul_le_mul_of_nonneg_left bound (sq_nonneg (q:ℚ))]
    | true =>
      have sub : (1:ℕ)≤q := by omega
      have castm : ((q-1:ℕ):ℚ)=(q:ℚ)-1 := by rw [Nat.cast_sub sub,Nat.cast_one]
      let g := z j+q*(load D z j+(q-1)*peak D a z)
      let r := q*∑t : V,z t
      have gap : (g:ℚ)-(r:ℚ)=z j+q*((load D z j:ℚ)+(q-1)*m-d) := by
        simp [g,r,m,d,castm]; ring
      simp only [ja,ite_false,ite_true,zero_add]
      rcases pay j ed with lt|⟨eq,common⟩
      · have diff : (g:ℚ)+1≤(r:ℚ) := by exact_mod_cast (show g+1≤r from lt)
        apply le_trans _ floor
        nlinarith only [mul_le_mul_of_nonneg_left (show (g:ℚ)-r≤ -1 by linarith only [diff]) (by positivity : (0:ℚ)≤q),
          congrArg (fun v : ℚ=>(q:ℚ)*v) gap]
      · have hi : (q:ℚ)-1≤M := by
          have mem : j.val∈StrictFlatSubsetMerge.common D V {a.val,b.val} :=
            mem_filter.mpr ⟨j.property,by simpa [and_comm] using And.intro ed common⟩
          simp only [M,OneStepColumnMerge.mergeCoefficient,mem,ite_true]
          split <;> linarith
        have gz : (g:ℚ)=(r:ℚ) := by exact_mod_cast eq
        apply le_trans _ hi
        nlinarith only [congrArg (fun v : ℚ=>(q:ℚ)*v) gap,gz,congrArg (fun v : ℚ=>(q:ℚ)*v) gz]


/-- On a shortest return from an exterior two-step arrival j, the last
vertex t before a misses j and every intermediate s of every path a→s→j.
When q≥3, t is distinct from j, so adding mass at t lowers the j column. -/
theorem return_row (free : QFree D V q) (sat : BRsub.Sat q D V) (hq : 2≤q)
    {j u : V} (outside : Exterior D a j) (au : D a u=true) (uj : D u j=true) :
    ∃t : V,Walk D V j t (q-2) ∧ D t a=true ∧ D t j=false ∧ (3≤q → t≠j) ∧
      ∀s : V,D a s=true → D s j=true → t≠s ∧ D t s=false := by
  obtain ⟨ret,minimal⟩ := shell D q a free sat hq outside au uj
  rw [show q-1=(q-2)+1 by omega] at ret
  obtain ⟨x,path,_,xa⟩ := ret.unsnoc
  let t : V := ⟨x,path.end_mem_or.elim (fun e=>e ▸ j.property) id⟩
  have pre : Walk D V j t (q-2) := path
  refine ⟨t,pre,xa,Bool.eq_false_iff.mpr (fun tj=>free j ((q-2)+1) (by omega) (by omega)
    (pre.snoc j.property tj)),?_,?_⟩
  · intro three eq
    have edge : D j a=true := eq ▸ xa
    have low := minimal 1 (.step a.property edge (.refl _))
    omega
  · intro s _ sj
    refine ⟨fun eq=>free j ((q-2)+1) (by omega) (by omega)
      (pre.snoc j.property (show D t j=true from eq ▸ sj)),?_⟩
    exact Bool.eq_false_iff.mpr (fun ts=>free j ((q-2)+1+1) (by omega) (by omega)
      ((pre.snoc s.property ts).snoc j.property sj))

def bump (y : V→ℚ) (t : V) (c : ℚ) (i : V) := y i+(if i=t then c else 0)

theorem bump_action (y : V→ℚ) (t : V) (c : ℚ) (j : V) :
    (bump y t c ᵥ* SingleArcTensorMerge.center q D V) j =
    (y ᵥ* SingleArcTensorMerge.center q D V) j+
    c*((if t=j then 1 else 0)+(if D t j then (q:ℚ) else 0)-1) := by
  let A := SingleArcTensorMerge.center q D V
  have coeff : A t j=(if t=j then 1 else 0)+(if D t j then (q:ℚ) else 0)-1 := by
    by_cases eq : t=j
    · subst j; cases ed : D t t <;> simp [A,SingleArcTensorMerge.center,WeightedArithmetic.rationalMatrix,WeightedArithmetic.closedMatrix,adjacencyMatrix,ed]
    · cases ed : D t j <;> simp [A,SingleArcTensorMerge.center,WeightedArithmetic.rationalMatrix,WeightedArithmetic.closedMatrix,adjacencyMatrix,eq,ed]
  change (∑i,(y i+(if i=t then c else 0))*A i j)=_+_
  simp_rw [add_mul]
  rw [sum_add_distrib]
  simp only [ite_mul,zero_mul,sum_ite_eq',mem_univ,ite_true,coeff]
  rfl

/-- Exact criterion for adding one nonnegative coefficient to the
multiplier. Its least possible size is the largest positive unpaid amount.
Only t and the heads of t then have to be checked. -/
theorem one_row_iff (free : QFree D V q) (hq : 2≤q) (y : V→ℚ) (m : V→ℚ) (t : V) :
    let A := SingleArcTensorMerge.center q D V
    let e := fun j=>(y ᵥ* A) j-m j
    let δ := max 0 (univ.sup' (⟨t,mem_univ _⟩ : (univ : Finset V).Nonempty) e)
    (∃c : ℚ,0≤c ∧ ∀j,(bump y t c ᵥ* A) j≤m j) ↔
      (e t≤0 ∧ ∀j : V,D t j=true → e j+((q:ℚ)-1)*δ≤0) := by
  intro A e δ
  have loop : D t t=false := Bool.eq_false_iff.mpr (loopfree free (by omega) t.property)
  have diag (c : ℚ) : (bump y t c ᵥ* A) t=(y ᵥ* A) t := by
    rw [bump_action]; simp [loop,A]
  have value (c : ℚ) {j : V} (neq : t≠j) : (bump y t c ᵥ* A) j=
      (y ᵥ* A) j+c*((if D t j then (q:ℚ) else 0)-1) := by
    rw [bump_action]; simp [neq,A]
  have nonneg : 0≤(q:ℚ)-1 := by
    apply sub_nonneg.mpr; exact_mod_cast (by omega : 1≤q)
  constructor
  · rintro ⟨c,cp,fits⟩
    have et : e t≤0 := sub_nonpos.mpr (diag c ▸ fits t)
    have minpay : δ≤c := by
      apply max_le cp
      apply Finset.sup'_le
      intro j _
      by_cases eq : t=j
      · subst j; exact et.trans cp
      have bound := fits j
      rw [value c eq] at bound
      change (y ᵥ* A) j-m j≤c
      cases ed : D t j <;> simp [ed] at bound
      · linarith
      · nlinarith only [bound,cp,mul_nonneg cp nonneg]
    refine ⟨et,fun j edge=>?_⟩
    have ne : t≠j := by rintro rfl; simp [loop] at edge
    have bound := fits j
    rw [value c ne] at bound
    simp [edge] at bound
    change (y ᵥ* A) j-m j+_≤0
    nlinarith only [bound,mul_le_mul_of_nonneg_left minpay nonneg]
  · rintro ⟨et,heads⟩
    refine ⟨δ,le_max_left ..,fun j=>?_⟩
    by_cases eq : t=j
    · subst j; rw [diag]; exact sub_nonpos.mp et
    rw [value δ eq]
    cases ed : D t j with
    | true =>
      have h := heads j ed
      change (y ᵥ* A) j-m j+_≤0 at h
      simp; linarith only [h]
    | false =>
      have le : e j≤δ := (Finset.le_sup' _ (mem_univ j)).trans (le_max_right ..)
      change (y ᵥ* A) j-m j≤δ at le
      simp; linarith only [le]


/-- If an exterior vertex receives an arc from every first-layer vertex,
no rational weighting supported there, nonnegative there, and arbitrary
at a can pay the endpoint merge. This uses just columns b and j. -/
theorem common_exterior (free : QFree D V q) (hq : 2≤q) {b j : V}
    (ab : D a b=true) (out : Exterior D a j) (all : ∀s : V,D a s=true → D s j=true)
    (z : V→ℚ) (nn : ∀s,0≤z s) (off : ∀s : V,D a s=false → z s=0) (c : ℚ) :
    ¬∀i,(bump z a c ᵥ* SingleArcTensorMerge.center q D V) i≤mergeCoefficient q D V {a.val,b.val} i := by
  intro bound
  have bb : D b b=false := Bool.eq_false_iff.mpr (loopfree free (by omega) b.property)
  have ne : a≠b := by rintro rfl; simp [bb] at ab
  have jb : j≠b := fun eq => Bool.noConfusion (out.2.symm.trans (eq ▸ ab))
  have ma : b.val∉StrictFlatSubsetMerge.common D V {a.val,b.val} := by
    intro h
    have e := (mem_filter.mp h).2 b.val (by simp)
    simp [bb] at e
  have mj : j.val∉StrictFlatSubsetMerge.common D V {a.val,b.val} := by
    intro h
    have e := (mem_filter.mp h).2 a.val (by simp)
    simp [out.2] at e
  have ns : j.val∉({a.val,b.val}:Finset ℕ) := by
    simpa only [mem_insert,mem_singleton,not_or] using
      And.intro (show j.val≠a.val from fun e=>out.1 (Subtype.ext e)) (show j.val≠b.val from fun e=>jb (Subtype.ext e))
  have full : (∑s : V,if D s j then z s else 0)=∑s,z s := by
    apply sum_congr rfl
    intro s _
    cases ed : D a s with
    | false => simp [off s ed]
    | true => simp [all s ed]
  have eb := bound b
  have ej := bound j
  rw [bump_action,apply_center] at eb ej
  simp [mergeCoefficient,ma,ne,ab] at eb
  rw [full] at ej
  simp [mergeCoefficient,ns,mj,out.1.symm,out.2,off j out.2] at ej
  have qone : (1:ℚ)≤q := by exact_mod_cast (by omega : 1≤q)
  have qtwo : (2:ℚ)≤q := by exact_mod_cast hq
  have total : 0≤∑s,z s := sum_nonneg (fun s _=>nn s)
  have incoming : 0≤∑s : V,if D s b then z s else 0 := sum_nonneg (fun s _=>by split <;> simp [nn])
  change z b+(q:ℚ)*(∑s : V,if D s b then z s else 0)-(∑s,z s)+c*(q-1)≤0 at eb
  change 1+((q:ℚ)*(∑s,z s)-(∑s,z s))≤c at ej
  nlinarith only [eb,mul_le_mul_of_nonneg_left ej (sub_nonneg.mpr qone),nn b,qtwo,
    mul_nonneg (by positivity : (0:ℚ)≤q) incoming,
    mul_nonneg (mul_nonneg (by positivity : (0:ℚ)≤q) (sub_nonneg.mpr qtwo)) total]

end Layer

section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (F : Family)
  {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
  (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

theorem center_singleton (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) :
    SingleArcTensorMerge.center q (insertArc (graph X.D F) f.val.1 f.val.2) X.V =
    SingleArcTensorMerge.center q X.D X.V := by
  have edge (i j : X.V) : insertArc (graph X.D F) f.val.1 f.val.2 i j=X.D i j := by
    by_cases pair : i.val=f.val.1.val ∧ j.val=f.val.2.val
    · rw [pair.1,pair.2]; simp [insertArc,f.property.1]
    · rw [show insertArc (graph X.D F) f.val.1 f.val.2 i j=graph X.D F i j by unfold insertArc; rw [ite_eq_right pair]]
      by_cases old : graph X.D F i j=true
      · have on := (mem_col.mp (active.mp old).choose_spec).2.2.2
        exact old.trans on.symm
      · have off := Bool.eq_false_iff.mpr old
        apply off.trans
        symm; apply Bool.eq_false_iff.mpr
        intro on
        let g : SharedArcFlatCut.Missing X F := ⟨(i,j),on,off⟩
        exact pair ⟨congrArg (fun t : SharedArcFlatCut.Missing X F=>t.val.1.val) (single g),
          congrArg (fun t : SharedArcFlatCut.Missing X F=>t.val.2.val) (single g)⟩
  ext i j
  simp [SingleArcTensorMerge.center,WeightedArithmetic.rationalMatrix,WeightedArithmetic.closedMatrix,
    adjacencyMatrix,edge]

include hq pos wm wr pc in
/-- In a flat family the edited head has an actual old parent. -/
theorem parent (f : SharedArcFlatCut.Missing X F) :
    ∃k : rest f.val.1 f.val.2,graph X.D F k.val f.val.2=true := by
  let a := f.val.1
  let b := f.val.2
  let E := graph X.D F
  let R := realMatrix q E X.V
  let P (i : X.V) : ℝ := p i
  let W (i : X.V) : ℝ := w i
  have row : R *ᵥ W=1 := funext fun i=>by simpa [W,R,E] using realMatrix_rational_rows w 1 wr i
  have col : P ᵥ* R=1 := funext fun i=>by simpa [P,R,E] using realMatrix_rational_columns p 1 pc i
  have balance := dotProduct_mulVec P R W
  rw [row,col,dotProduct_one,one_dotProduct] at balance
  have pm : (∑i : X.V,P i)=1 := balance.trans (real_mass_of_rational_probability w wm)
  have ab : a≠b := by
    intro eq
    have on : X.D a b=true := f.property.1
    rw [eq] at on
    exact loopfree X.free (by omega) b.property on
  have pa : 0<P a := by dsimp [P]; exact_mod_cast (pos _ a.property).2
  have part : P a≤∑i∈univ.erase b,P i := single_le_sum
    (fun i _=>by change 0≤(p i:ℝ); exact_mod_cast (pos _ i.property).2.le) (mem_erase.mpr ⟨ab,mem_univ _⟩)
  have split := add_sum_erase univ P (mem_univ b)
  have low : p b<1 := by
    have : P b<1 := by linarith only [pa,part,split,pm]
    dsimp [P] at this; exact_mod_cast this
  by_contra! no
  have absent (i : X.V) : E i b=false := by
    by_cases ia : i=a
    · exact ia ▸ f.property.2
    by_cases ib : i=b
    · subst i; exact Bool.eq_false_iff.mpr (loopfree (PrivateArcEndpoints.graph_free X F) (by omega) b.property)
    exact Bool.eq_false_iff.mpr (no ⟨i,mem_erase.mpr ⟨ib,mem_erase.mpr ⟨ia,mem_univ _⟩⟩⟩)
  have zero : inW E X.V p b=0 := sum_eq_zero (fun i hi=>by simp [(show E i b=false from absent ⟨i,hi⟩)])
  have h := pc b b.property
  change p b+q*inW E X.V p b=1 at h
  rw [zero,mul_zero,add_zero] at h
  exact low.ne h

/-- An entirely finite test on the first layer. -/
def FitsLayer (D : CH.Digraph) {V : Finset ℕ} (q : ℕ) (a b : V) (z : V→ℕ) : Prop :=
  ∀s : V,D a s=true →
    let lhs := z s+q*(load D z s+(q-1)*peak D a z)
    let rhs := q*∑t : V,z t
    lhs<rhs ∨ (lhs=rhs ∧ D b s=true)

include hq pos wm wr pc in
theorem sign_of_bound (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (y : X.V→ℚ) (yk : 0≤y k.val)
    (checked : ∀j,(y ᵥ* SingleArcTensorMerge.center q (insertArc (graph X.D F) f.val.1 f.val.2) X.V) j≤
      mergeCoefficient q X.D X.V {f.val.1.val,f.val.2.val} j) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v : X.V,E f.val.1 v=true ∧ T v k.val<0 := by
  let a := f.val.1
  let b := f.val.2
  have sub : ({a.val,b.val}:Finset ℕ)⊆X.V := insert_subset_iff.mpr ⟨a.property,singleton_subset_iff.mpr b.property⟩
  have ab : a.val≠b.val := by
    intro same
    have on : X.D a.val b.val=true := f.property.1
    rw [same] at on
    exact loopfree X.free (by omega) b.property on
  have proper : ({a.val,b.val}:Finset ℕ)≠X.V := by
    intro eq
    have mem := eq.ge k.val.property
    simp only [mem_insert,mem_singleton] at mem
    exact mem.elim (fun h=>(inside k).1 (Subtype.ext h)) (fun h=>(inside k).2 (Subtype.ext h))
  exact (fixed_merge_iff X hq F pos wm wr pc small f k kb _ sub (by simp [ab]) proper).mpr
    ⟨y,yk,checked⟩

include hq pos wm wr pc in
/-- A single explicit multiplier works for every old parent. An actual
parent is also supplied, so the test needs no parent or covering input. -/
theorem singleton (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (z : X.V→ℕ)
    (off : ∀s : X.V,X.D f.val.1 s=false → z s=0) (live : 0<∑s : X.V,z s)
    (pay : FitsLayer X.D q f.val.1 f.val.2 z) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let y := multiplier X.D q a z
    let A := SingleArcTensorMerge.center q (insertArc E a b) X.V
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q a b
    (∀j,(y ᵥ* A) j≤mergeCoefficient q X.D X.V {a.val,b.val} j) ∧
    (∃k : rest a b,E k.val b=true) ∧
    ∀k : rest a b,E k.val b=true → 0≤y k.val ∧ ∃v : X.V,E a v=true ∧ T v k.val<0 := by
  intro E a b y A T
  obtain ⟨outside,upper⟩ := witness X.D q a X.free hq b z off live pay
  have native : A=SingleArcTensorMerge.center q X.D X.V := center_singleton X F f single
  have checked : ∀j,(y ᵥ* A) j≤mergeCoefficient q X.D X.V {a.val,b.val} j := by rw [native]; exact upper
  refine ⟨checked,parent X hq F pos wm wr pc f,?_⟩
  intro k kb
  have yk := outside k.val (inside k).1
  exact ⟨yk,sign_of_bound X hq F pos wm wr pc small f k kb y yk checked⟩

include hq pos wm wr pc in
theorem progress (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (z : X.V→ℕ)
    (off : ∀s : X.V,X.D f.val.1 s=false → z s=0) (live : 0<∑s : X.V,z s)
    (pay : FitsLayer X.D q f.val.1 f.val.2 z)
    (B : Finset ℕ) (K : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (c : ℚ) :
    SharedArcPivotGate.ProgressAt X F B K prices c := by
  obtain ⟨_,⟨k,kb⟩,every⟩ := singleton X hq F pos wm wr pc small f single z off live pay
  obtain ⟨v,_,bad⟩ := (every k kb).2
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,pos,wm,wr,pc,f,v,k.val,bad⟩)))


include hq pos wm wr pc in
/-- A loaded exterior supplies a specific return row. If the row and its
heads can afford the largest unpaid amount, the repaired vector pays the
endpoint merge and is nonnegative at every old parent. -/
theorem return_payment (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (z : X.V→ℕ) (debit : ℚ)
    (off : ∀s : X.V,X.D f.val.1 s=false → z s=0) (loaded : 0<peak X.D f.val.1 z)
    (B : Finset ℕ) (K : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (c : ℚ) :
    let a := f.val.1
    let b := f.val.2
    let y := bump (fun i : X.V=>(q:ℚ)*z i) a (-debit)
    let m := mergeCoefficient q X.D X.V {a.val,b.val}
    let A := SingleArcTensorMerge.center q (insertArc (graph X.D F) a b) X.V
    let e := fun i=>(y ᵥ* A) i-m i
    let δ := max 0 (univ.sup' (⟨a,mem_univ _⟩ : (univ : Finset X.V).Nonempty) e)
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q a b
    ∃j t : X.V,Exterior X.D a j ∧ load X.D z j=peak X.D a z ∧
      Walk X.D X.V j t (q-2) ∧ X.D t a=true ∧ X.D t j=false ∧ (3≤q → t≠j) ∧
      (∀s : X.V,X.D a s=true → X.D s j=true → t≠s ∧ X.D t s=false) ∧
      (e t≤0 → (∀i : X.V,X.D t i=true → e i+((q:ℚ)-1)*δ≤0) →
        (∃h : ℚ,0≤h ∧ (∀k : X.V,k≠a → 0≤bump y t h k) ∧ ∀i,(bump y t h ᵥ* A) i≤m i) ∧
        (∃v k : X.V,E a v=true ∧ E k b=true ∧ T v k<0) ∧ SharedArcPivotGate.ProgressAt X F B K prices c) := by
  intro a b y m A e δ E T
  obtain ⟨j,u,ext,au,uj,hit,_,_⟩ := peak_shell X.D q a X.free X.sat hq z off loaded
  obtain ⟨t,path,ta,tj,ne,miss⟩ := return_row X.D q a X.free X.sat hq ext au uj
  refine ⟨j,t,ext,hit,path,ta,tj,ne,miss,fun et budget=>?_⟩
  have native : A=SingleArcTensorMerge.center q X.D X.V := center_singleton X F f single
  have pay : ∃h : ℚ,0≤h ∧ ∀i,(bump y t h ᵥ* A) i≤m i := by
    rw [native]
    apply (one_row_iff X.D q X.free hq y m t).mpr
    dsimp only [e,δ] at et budget
    rw [native] at et budget
    exact ⟨et,budget⟩
  obtain ⟨h,nn,le⟩ := pay
  have posOff (k : X.V) (ka : k≠a) : 0≤bump y t h k := by
    unfold bump
    have start : 0≤y k := by simp only [y,bump,ka,ite_false,add_zero]; positivity
    exact add_nonneg start (by split <;> simp [nn])
  obtain ⟨k,kb⟩ := parent X hq F pos wm wr pc f
  obtain ⟨v,av,bad⟩ := sign_of_bound X hq F pos wm wr pc small f k kb _ (posOff _ (inside k).1) le
  exact ⟨⟨h,nn,posOff,le⟩,⟨v,k.val,av,kb,bad⟩,Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,pos,wm,wr,pc,f,v,k.val,bad⟩)))⟩

end Native

end LeanCH.BR.Closure.EndpointLayerWitness
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.witness
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.singleton
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.progress
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.peak_shell
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.return_row
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.one_row_iff
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.return_payment
#print axioms LeanCH.BR.Closure.EndpointLayerWitness.common_exterior

