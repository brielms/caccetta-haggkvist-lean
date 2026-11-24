import checkpoints.shen_extension.SingleArcHeirMidpoint
import checkpoints.shen_extension.SingleArcTensorMerge

namespace LeanCH.BR.Closure.SingleArcMidpointSign
open Finset Matrix FiniteCutInverse BRq2 BRq3 BR45 WeightedSD SharedArcFlatResponse
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open scoped Matrix

private theorem weighted_column {I : Type*} [Fintype I] [DecidableEq I] {R L : Matrix I I ℝ}
    (left : L*R=1) (w p : I→ℝ) (pc : p ᵥ* R=fun _=>1) (t : ℝ) (a b v j : I) :
    (∑i,test L w p t a b v i*R i j) =
    t*p a*w b*((1:Matrix I I ℝ) v j)+(w v*(1+t*L b a)-t*w b*L v a)-
    t*w v*p a*((1:Matrix I I ℝ) b j) := by
  have h (i) : test L w p t a b v i*R i j =
      (t*p a*w b)*(L v i*R i j)+(w v*(1+t*L b a)-t*w b*L v a)*(p i*R i j)-
      (t*w v*p a)*(L b i*R i j) := by unfold test; ring
  simp only [h,sum_sub_distrib,sum_add_distrib,←mul_sum]
  change _*(L*R) v j+_*(p ᵥ* R) j-_*(L*R) b j=_
  rw [left,pc]; simp

/-- The only unsigned term left in the diagonal identity is the tensor
mass of old parents of the tail that fail to point to its heir. -/
theorem diagonal {q : ℕ} (hq : 2≤q) (E : CH.Digraph) (V : Finset ℕ)
    (a b v : V) (va : v≠a) (vb : v≠b) (ab : a≠b) (aa : E a a=false)
    (av : E a v=true) (heir : ∀i : V,i≠a → E i v=true → E i a=true)
    (w p : V→ℝ) (pc : p ᵥ* realMatrix q E V=fun _=>1) :
    let T := test (realMatrix q E V)⁻¹ w p q a b
    let U := univ.filter (fun i : V=>E i a=true ∧ E i v=false)
    T v v = (q:ℝ)*(∑i∈U,T v i)-p a*(((q:ℝ)-1)*w v-(q:ℝ)*w b) := by
  intro T U
  let R := realMatrix q E V
  have col := weighted_column (nonsing_inv_mul R (matrix_unit hq E V)) w p pc (q:ℝ) a b v
  have diff : (∑i,T v i*(R i v-R i a))=(q:ℝ)*p a*w b := by
    simp_rw [mul_sub,sum_sub_distrib]
    have h1 := col v
    have h2 := col a
    simp only [one_apply,ite_true,vb.symm,va,ab.symm,ite_false,mul_zero,mul_one,sub_zero,zero_add] at h1 h2
    change (∑i,test R⁻¹ w p q a b v i*R i v)-(∑i,test R⁻¹ w p q a b v i*R i a)=_
    linarith only [h1,h2]
  have term (i : V) : T v i*(R i v-R i a) =
      (if i=v then T v i else 0)+(if i=a then ((q:ℝ)-1)*T v i else 0)-
      (if E i a=true ∧ E i v=false then (q:ℝ)*T v i else 0) := by
    by_cases ia : i=a
    · subst i
      simp [R,realMatrix_entry,va.symm,aa,av]; ring
    · have par := heir i ia
      cases ivE : E i v <;> cases iaE : E i a <;> by_cases iv : i=v <;>
        simp_all [R,realMatrix_entry] <;> ring
  simp_rw [term,sum_sub_distrib,sum_add_distrib] at diff
  have bank : (∑i : V,if E i a=true ∧ E i v=false then (q:ℝ)*T v i else 0)=
      (q:ℝ)*∑i∈U,T v i := by rw [mul_sum]; exact (sum_filter ..).symm
  rw [bank] at diff
  simp only [sum_ite_eq',mem_univ,ite_true] at diff
  have base : T v a=w v*p a := by dsimp [T,test]; ring
  rw [base] at diff
  linarith only [diff]

theorem sign_iff {q : ℕ} (hq : 2≤q) (E : CH.Digraph) (V : Finset ℕ)
    (a b v : V) (va : v≠a) (vb : v≠b) (ab : a≠b) (aa : E a a=false)
    (av : E a v=true) (heir : ∀i : V,i≠a → E i v=true → E i a=true)
    (w p : V→ℝ) (pc : p ᵥ* realMatrix q E V=fun _=>1) :
    let T := test (realMatrix q E V)⁻¹ w p q a b
    T v v≤0 ↔ (q:ℝ)*(∑i∈univ.filter (fun i : V=>E i a=true ∧ E i v=false),T v i) ≤
      p a*(((q:ℝ)-1)*w v-(q:ℝ)*w b) := by
  intro T
  have h := diagonal hq E V a b v va vb ab aa av heir w p pc
  change T v v=_ at h
  rw [h]
  exact sub_nonpos

/-- The head-side version uses old children of the head that its coheir misses,
and the entries come from a single tensor column. -/
theorem co_diagonal {q : ℕ} (hq : 2≤q) (E : CH.Digraph) (V : Finset ℕ)
    (a b v : V) (va : v≠a) (vb : v≠b) (ab : a≠b) (bb : E b b=false)
    (parent : E v b=true) (coheir : ∀i : V,i≠b → E v i=true → E b i=true)
    (w p : V→ℝ) (wr : realMatrix q E V *ᵥ w=fun _=>1) :
    let T := test (realMatrix q E V)⁻¹ w p q a b
    let U := univ.filter (fun i : V=>E b i=true ∧ E v i=false)
    T v v = (q:ℝ)*(∑i∈U,T i v)-w b*(((q:ℝ)-1)*p v-(q:ℝ)*p a) := by
  have eq := diagonal hq (fun i j=>E j i) V b a v vb va ab.symm bb parent coheir p w
    (by rw [realMatrix_reverse,vecMul_transpose]; exact wr)
  rw [realMatrix_reverse,←transpose_nonsing_inv] at eq
  have trans (i j : V) : test ((realMatrix q E V)⁻¹)ᵀ p w q b a i j =
      test (realMatrix q E V)⁻¹ w p q a b j i := by unfold test; simp only [transpose_apply]; ring
  simpa only [trans] using eq

/-- For the singleton, the parent set in the formula is exactly the set
of old parents that close an old walk of length q+1 through a→v. -/
theorem return_layer {q n} (X : Model q n) (hq : 2≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (v i : X.V) (av : graph X.D F f.val.1 v=true) (ia : graph X.D F i f.val.1=true) :
    graph X.D F i v=false ↔ Walk (graph X.D F) X.V v i (q-1) := by
  let E := graph X.D F
  let a := f.val.1
  let b := f.val.2
  have sub (j k) (ed : E j k=true) : X.D j k=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have only (j) (jv : j∈X.V) (k) (kv : k∈X.V) (ed : X.D j k=true) : E j k=true ∨ (j=a.val ∧ k=b.val) := by
    by_cases old : E j k=true
    · exact Or.inl old
    · let g : SharedArcFlatCut.Missing X F := ⟨(⟨j,jv⟩,⟨k,kv⟩),ed,Bool.eq_false_iff.mpr old⟩
      exact Or.inr ⟨congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.1.val) (single g),
        congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.2.val) (single g)⟩
  have free := PrivateArcEndpoints.graph_free X F
  constructor
  · intro miss
    have vb : v.val≠b.val := fun e=>Bool.noConfusion (f.property.2.symm.trans ((congrArg (E a) e).symm.trans av))
    have off : ¬X.D i v=true := fun ed=>Bool.noConfusion (miss.symm.trans
      ((only _ i.property _ v.property ed).resolve_right (fun h=>vb h.2)))
    have ballEq := (SingleArcReturnProfile.balls (by omega : 1≤q) X.free X.sat sub only v.property (sub _ _ av)).2
    have hit : i.val∈ball E X.V v (q-1) := by
      rw [ballEq]
      exact mem_sdiff.mpr ⟨i.property,fun h=>off (mem_inN.mp h).2⟩
    obtain ⟨_,m,le,path⟩ := mem_ball.mp hit
    have min : q<m+2 := by
      by_contra! bad
      exact free a (m+1+1) (by omega) (by omega) (.step v.property av (path.snoc a.property ia))
    exact (by omega : m=q-1) ▸ path
  · intro path
    exact Bool.eq_false_iff.mpr (fun edge=>free i (q-1+1) (by omega) (by omega) (.step v.property edge path))

/-- A bound on this one named parent set pays the diagonal tensor exit
at an actual old successor and predecessor. No smaller-order hypothesis
is used to turn the bound into a sign. -/
theorem progress {q n} (X : Model q n) (hq : 2≤q) (F : Family) (B : Finset ℕ)
    (J : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (c : ℚ) {w p : ℕ→ℚ}
    (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    (f : SharedArcFlatCut.Missing X F) (v : X.V) (av : graph X.D F f.val.1 v=true)
    (vb : graph X.D F v f.val.2=true)
    (heir : ∀i : X.V,i≠f.val.1 → graph X.D F i v=true → graph X.D F i f.val.1=true)
    (bound : let E := graph X.D F
             let a := f.val.1
             let b := f.val.2
             let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q a b
             (q:ℝ)*(∑i∈univ.filter (fun i : X.V=>E i a=true ∧ E i v=false),T v i) ≤
               (p a:ℝ)*(((q:ℝ)-1)*(w v:ℝ)-(q:ℝ)*(w b:ℝ))) :
    SharedArcPivotGate.ProgressAt X F B J prices c := by
  let E := graph X.D F
  let a := f.val.1
  let b := f.val.2
  have free := PrivateArcEndpoints.graph_free X F
  have aa : E a a=false := Bool.eq_false_iff.mpr (loopfree free (by omega) a.property)
  have va : v≠a := fun e=>loopfree free (by omega) a.property ((congrArg (fun j : X.V=>E a j) e).symm.trans av)
  have ne : v≠b := fun e=>loopfree free (by omega) b.property ((congrArg (fun i : X.V=>E i b) e).symm.trans vb)
  have ab : a≠b := fun e=>loopfree X.free (by omega) b.property ((congrArg (fun i : X.V=>X.D i b) e).symm.trans f.property.1)
  have col := funext (realMatrix_rational_columns p 1 pc)
  have sign := (sign_iff hq E X.V a b v va ne ab aa av heir (fun i : X.V=>(w i:ℝ))
    (fun i : X.V=>(p i:ℝ)) (by simpa using col)).mpr bound
  have nz := SharedArcFlatArithmetic.nonzero hq
    (by simpa using funext (realMatrix_rational_rows w 1 wr)) (by simpa using col) a b v v
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,pos,wm,wr,pc,f,v,v,lt_of_le_of_ne sign nz⟩)))

end LeanCH.BR.Closure.SingleArcMidpointSign
#print axioms LeanCH.BR.Closure.SingleArcMidpointSign.diagonal
#print axioms LeanCH.BR.Closure.SingleArcMidpointSign.sign_iff
#print axioms LeanCH.BR.Closure.SingleArcMidpointSign.co_diagonal
#print axioms LeanCH.BR.Closure.SingleArcMidpointSign.return_layer
#print axioms LeanCH.BR.Closure.SingleArcMidpointSign.progress
