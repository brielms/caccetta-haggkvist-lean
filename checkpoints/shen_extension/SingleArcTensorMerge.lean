import checkpoints.shen_extension.StrictFlatSubsetMerge
import checkpoints.shen_extension.SingleArcPunctureSign

namespace LeanCH.BR.Closure.SingleArcTensorMerge
open Finset Matrix FiniteCutInverse BRq2 BRq3 BR45 BRsub WeightedSD WeightedArithmetic
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse StrictFlatSubsetMerge
open scoped Matrix

/-- Centered adjacency of the inserted graph. Its inverse can be used without
first solving for either of the old flat weights. -/
noncomputable def center (q : ℕ) (G : CH.Digraph) (V : Finset ℕ) : Matrix V V ℚ :=
  fun i j => rationalMatrix q (adjacencyMatrix G V) i j-1

private theorem cast_inverse {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℚ)
    {J : Matrix I I ℝ} (right : (Rat.castHom ℝ).mapMatrix A * J=1) :
    A*A⁻¹=1 ∧ J=(Rat.castHom ℝ).mapMatrix A⁻¹ := by
  let g := Rat.castHom ℝ
  have unit : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    have h := congrArg Matrix.det right
    rw [det_mul,←RingHom.map_det,zero,map_zero,zero_mul,det_one] at h
    exact zero_ne_one h
  have inv := mul_nonsing_inv A unit
  refine ⟨inv,?_⟩
  have both : g.mapMatrix A * g.mapMatrix A⁻¹=1 := by rw [←map_mul,inv,map_one]
  exact (inv_eq_right_inv right).symm.trans (inv_eq_right_inv both)

def cut (q : ℕ) (G : CH.Digraph) (V S : Finset ℕ) (u : V→ℚ) : ℚ :=
  mass S (extendWeight V u) + q*mass (common G V S) (extendWeight V u) - ∑i,u i

private theorem cut_sum {I : Type*} [Fintype I] (q : ℕ) (G : CH.Digraph) (V S : Finset ℕ)
    (c : I→ℚ) (B : I→V→ℚ) :
    cut q G V S (fun i=>∑j,c j*B j i) = ∑j,c j*cut q G V S (B j) := by
  classical
  have extend (i : ℕ) : extendWeight V (fun i=>∑j,c j*B j i) i = ∑j,c j*extendWeight V (B j) i := by
    by_cases h : i∈V <;> simp [extendWeight,h]
  have m (U : Finset ℕ) : mass U (extendWeight V (fun i=>∑j,c j*B j i)) =
      ∑j,c j*mass U (extendWeight V (B j)) := by
    simp only [mass,extend,mul_sum]
    rw [sum_comm]
  unfold cut
  rw [m,m,sum_comm (s:=univ (α:=V)) (t:=univ (α:=I)),mul_sum,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [←mul_sum]
  ring

/-- Checking the inverse columns suffices for every feasible nonzero weighting:
the coefficients of a weighting in these columns are precisely its row excesses.
Apply the same statement to the transposed matrices for incoming merges. -/
theorem bounds_span (q : ℕ) (G : CH.Digraph) (V S : Finset ℕ) (A H : Matrix V V ℚ)
    (right : A*H=1) (bounds : ∀j,cut q G V S (fun i=>H i j)<0)
    (u : V→ℚ) (nonzero : u≠0) (feasible : ∀i,0≤(A *ᵥ u) i) :
    cut q G V S u<0 := by
  let c := A *ᵥ u
  have recover : H *ᵥ c=u := by rw [show c=A *ᵥ u from rfl,mulVec_mulVec,mul_eq_one_comm.mp right,one_mulVec]
  have live : ∃j,0<c j := by
    by_contra! zero
    have vanished : c=0 := funext (fun j=>le_antisymm (zero j) (feasible j))
    rw [vanished,mulVec_zero] at recover
    exact nonzero recover.symm
  have repr : u=fun i=>∑j,c j*H i j := by
    rw [←recover]
    funext i
    exact sum_congr rfl (fun j _=>mul_comm _ _)
  rw [repr,cut_sum]
  apply sum_neg'
  · intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (feasible j) (bounds j).le
  · obtain ⟨j,pos⟩ := live
    exact ⟨j,mem_univ _,mul_neg_of_pos_of_neg pos (bounds j)⟩

private theorem feasible {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℚ} (right : center q G V*H=1) (k : V) :
    (∀i∈V,mass V (extendWeight V (fun j=>H j k))≤WeightedSD.row q G V (extendWeight V (fun j=>H j k)) i) ∧
    (∀i∈V,mass V (extendWeight V (H k))≤WeightedSD.col q G V (extendWeight V (H k)) i) := by
  have left := mul_eq_one_comm.mp right
  constructor
  · intro i iv
    let j : V := ⟨i,iv⟩
    rw [mass_extendWeight,row_extendWeight q G V _ j]
    have eq := congrFun (congrFun right j) k
    simp only [mul_apply,center,sub_mul,one_mul,sum_sub_distrib] at eq
    have lo : 0≤(1 : Matrix V V ℚ) j k := by rw [one_apply]; split <;> norm_num
    change _≤∑h,rationalMatrix q (adjacencyMatrix G V) j h*H h k
    linarith only [eq,lo]
  · intro i iv
    let j : V := ⟨i,iv⟩
    rw [mass_extendWeight,col_extendWeight q G V _ j]
    have eq := congrFun (congrFun left k) j
    simp only [mul_apply,center,mul_sub,mul_one,sum_sub_distrib] at eq
    have lo : 0≤(1 : Matrix V V ℚ) k j := by rw [one_apply]; split <;> norm_num
    change _≤∑h,H k h*rationalMatrix q (adjacencyMatrix G V) h j
    linarith only [eq,lo]

/-- A common inverse of a graph matrix has rational columns and rows.
    Each gives a nonnegative weight satisfying the corresponding weak law. -/
theorem rational_rays {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : CommonInverse (realMatrix q G V) H) (k : V) :
    ∃u v : ℕ→ℚ,(∀i∈V,0≤u i ∧ 0≤v i) ∧
      (∀i∈V,mass V u≤WeightedSD.row q G V u i ∧ mass V v≤WeightedSD.col q G V v i) ∧
      (∀i : V,(u i:ℝ)=H i k ∧ (v i:ℝ)=H k i) := by
  let A := center q G V
  have cast : (Rat.castHom ℝ).mapMatrix A=excess (realMatrix q G V) := by
    ext i j; change ((rationalMatrix q _ i j-1:ℚ):ℝ)=_
    push_cast; rfl
  have right : (Rat.castHom ℝ).mapMatrix A*H=1 := cast ▸ inv.right
  obtain ⟨ai,h⟩ := cast_inverse A right
  obtain ⟨rows,cols⟩ := feasible ai k
  let u := extendWeight V (fun j=>A⁻¹ j k)
  let v := extendWeight V (A⁻¹ k)
  have eq (i : V) : (u i:ℝ)=H i k ∧ (v i:ℝ)=H k i := by
    dsimp only [u,v]; rw [extendWeight_on,extendWeight_on,h]; exact ⟨rfl,rfl⟩
  refine ⟨u,v,?_,fun i iv=>⟨rows i iv,cols i iv⟩,eq⟩
  intro i iv
  have id := eq ⟨i,iv⟩
  have a := (id.1.symm ▸ inv.nonneg ⟨i,iv⟩ k : (0:ℝ)≤(u i:ℝ))
  have b := (id.2.symm ▸ inv.nonneg k ⟨i,iv⟩ : (0:ℝ)≤(v i:ℝ))
  exact ⟨by exact_mod_cast a,by exact_mod_cast b⟩

/-- Each column and each row of the inverse is individually eligible
for a merge as soon as that column or row is positive. -/
theorem ray_bound {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {G : CH.Digraph} (subG : ∀i j,G i j=true → X.D i j=true)
    {H : Matrix X.V X.V ℚ} (right : center q G X.V*H=1)
    {S : Finset ℕ} (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V) (k : X.V) :
    ((∀i,0<H i k) → cut q X.D X.V S (fun i=>H i k)<0) ∧
    ((∀i,0<H k i) → cut q (fun x y=>X.D y x) X.V S (H k)<0) := by
  have pay := feasible right k
  constructor
  · intro pos
    let u := extendWeight X.V (fun i=>H i k)
    have up (i) (iv : i∈X.V) : 0<u i := by simpa only [u,extendWeight_on X.V _ (⟨i,iv⟩ : X.V)] using pos ⟨i,iv⟩
    have rows (i) (iv : i∈X.V) : mass X.V u≤WeightedSD.row q X.D X.V u i :=
      (pay.1 i iv).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (outW_mono_graph (fun i _ j _=>subG i j) (fun i hi=>(up i hi).le) iv) (Nat.cast_nonneg q)))
    apply sub_neg.mpr
    rw [←mass_extendWeight]
    apply lt_of_not_ge
    intro h
    have inc := uniform_of_merge_feasible hq X.free small sub size up rows h
    exact X.prime S sub size proper ⟨outUniform_inUniform (D:=fun i j=>X.D j i) X.free.reverse
      (SerialChain.sat_reverse X.sat) sub inc,inc⟩
  · intro pos
    let u := extendWeight X.V (H k)
    have up (i) (iv : i∈X.V) : 0<u i := by simpa only [u,extendWeight_on X.V _ (⟨i,iv⟩ : X.V)] using pos ⟨i,iv⟩
    have cols (i) (iv : i∈X.V) : mass X.V u≤WeightedSD.col q X.D X.V u i :=
      (pay.2 i iv).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (inW_mono_graph (fun i _ j _=>subG i j) (fun i hi=>(up i hi).le) iv) (Nat.cast_nonneg q)))
    apply sub_neg.mpr
    rw [←mass_extendWeight]
    apply lt_of_not_ge
    intro h
    have out := uniform_of_merge_feasible (D:=fun i j=>X.D j i) hq X.free.reverse small sub size up cols h
    exact X.prime S sub size proper ⟨out,outUniform_inUniform X.free X.sat sub out⟩

section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
  (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

include hq wp wm wr pc in
theorem identify (f : SharedArcFlatCut.Missing X F) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let A := center q (insertArc E a b) X.V
    A*A⁻¹=1 ∧ ∀i j : X.V,test (realMatrix q E X.V)⁻¹ (fun x : X.V=>(w x:ℝ)) (fun x : X.V=>(p x:ℝ))
      q a b i j=((q:ℝ)*(p a:ℝ)*(w b:ℝ))*(A⁻¹ i j:ℝ) := by
  intro E a b A
  have d : 0<(q:ℝ)*(p a:ℝ)*(w b:ℝ) := mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q))
    (by exact_mod_cast (wp a a.property).2)) (by exact_mod_cast (wp b b.property).1)
  have h := SingleArcPunctureSign.signed_right (matrix_unit hq E X.V)
    (realMatrix_insert_difference (q:=q) a b (show ¬E a b=true by simp [E,a,b,f.property.2]))
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc))
    (real_mass_of_rational_probability w wm) d.ne'
  have cast : (Rat.castHom ℝ).mapMatrix A=excess (realMatrix q (insertArc E a b) X.V) := by
    ext i j
    change ((rationalMatrix q _ i j-1:ℚ):ℝ)=_
    push_cast; rfl
  rw [←cast] at h
  obtain ⟨inv,eq⟩ := cast_inverse A h
  refine ⟨inv,fun i j => ?_⟩
  have val := congrFun (congrFun eq i) j
  exact (div_eq_iff d.ne').mp val |>.trans (mul_comm ..)

private theorem included (f : SharedArcFlatCut.Missing X F) :
    ∀i j,insertArc (graph X.D F) f.val.1 f.val.2 i j=true → X.D i j=true := by
  intro i j ed
  by_cases pair : i=f.val.1.val ∧ j=f.val.2.val
  · exact pair.1 ▸ pair.2 ▸ f.property.1
  have old : graph X.D F i j=true := by simpa [insertArc,pair] using ed
  exact (mem_col.mp (active.mp old).choose_spec).2.2.2

include hq small wp wm wr pc in
theorem all_cuts (f : SharedArcFlatCut.Missing X F) {S : Finset ℕ} (sub : S⊆X.V)
    (size : 2≤S.card) (proper : S≠X.V) (k : X.V) :
    let H := (center q (insertArc (graph X.D F) f.val.1 f.val.2) X.V)⁻¹
    cut q X.D X.V S (fun i=>H i k)<0 ∧ cut q (fun x y=>X.D y x) X.V S (H k)<0 := by
  intro H
  obtain ⟨inv,eq⟩ := identify X hq F wp wm wr pc f
  have positive (i j : X.V) : 0<H i j := by
    have h := SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f i j
    rw [eq i j] at h
    have hp : 0≤(q:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ) := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (wp _ f.val.1.property).2.le)) (by exact_mod_cast (wp _ f.val.2.property).1.le)
    exact_mod_cast pos_of_mul_pos_right h hp
  have cuts := ray_bound X hq small (included X F f) inv sub size proper k
  exact ⟨cuts.1 (fun i=>positive i k),cuts.2 (positive k)⟩

/-- A nonnegative merge score supplies a nonpositive entry of the tested
row or column. Only the complementary entries need an independent sign
to put the witness in a prescribed set of coordinates. -/
theorem locate {I : Type*} (u : I→ℚ) (eligible : I→Prop) {score : ℚ}
    (bound : (∀i,0<u i) → score<0) (bad : 0≤score)
    (outside : ∀i,¬eligible i → 0<u i) : ∃i,eligible i ∧ u i≤0 := by
  classical
  by_contra! none
  apply bad.not_gt
  apply bound
  intro i
  by_cases h : eligible i
  · exact none i h
  · exact outside i h

include hq small wp wm wr pc in
theorem rectangle_of_failed_cut (f : SharedArcFlatCut.Missing X F) {S : Finset ℕ}
    (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V)
    (bad : let E := graph X.D F
           let H := (center q (insertArc E f.val.1 f.val.2) X.V)⁻¹
           (∃v : X.V,E f.val.1 v=true ∧ 0≤cut q (fun x y=>X.D y x) X.V S (H v)) ∨
           (∃k : X.V,E k f.val.2=true ∧ 0≤cut q X.D X.V S (fun i=>H i k))) :
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
    ∃v k : X.V,E f.val.1 v=true ∧ E k f.val.2=true ∧ T v k<0 := by
  intro E T
  let H := (center q (insertArc E f.val.1 f.val.2) X.V)⁻¹
  obtain ⟨inv,eq⟩ := identify X hq F wp wm wr pc f
  have coeff : 0<(q:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ) := mul_pos (mul_pos
    (by exact_mod_cast (by omega : 0<q)) (by exact_mod_cast (wp _ f.val.1.property).2))
    (by exact_mod_cast (wp _ f.val.2.property).1)
  have positive (i j : X.V) (h : 0<T i j) : 0<H i j := by
    rw [show T i j=_ from eq i j] at h
    exact_mod_cast pos_of_mul_pos_right h coeff.le
  have neg (i j : X.V) (le : H i j≤0) : T i j<0 := by
    have nonpos : T i j≤0 := by
      rw [show T i j=_ from eq i j]
      exact mul_nonpos_of_nonneg_of_nonpos coeff.le (by exact_mod_cast le)
    exact lt_of_le_of_ne nonpos (SharedArcFlatArithmetic.nonzero hq
      (by simpa using funext (realMatrix_rational_rows w 1 wr))
      (by simpa using funext (realMatrix_rational_columns p 1 pc)) _ _ i j)
  rcases bad with ⟨v,edge,fail⟩ | ⟨k,edge,fail⟩
  · obtain ⟨k,ek,hk⟩ := locate (H v) (fun k=>E k f.val.2=true)
      (ray_bound X hq small (included X F f) inv sub size proper v).2 fail
      (fun k _=>positive v k (SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f v k))
    exact ⟨v,k,edge,ek,neg _ _ hk⟩
  · obtain ⟨v,ev,hv⟩ := locate (fun v=>H v k) (fun v=>E f.val.1 v=true)
      (ray_bound X hq small (included X F f) inv sub size proper k).1 fail
      (fun v _=>positive v k (SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f v k))
    exact ⟨v,k,ev,edge,neg _ _ hv⟩

include hq small wp wm wr pc in
theorem progress (B : Finset ℕ) (J : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (c : ℚ)
    (f : SharedArcFlatCut.Missing X F) {S : Finset ℕ}
    (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V)
    (bad : let E := graph X.D F
           let H := (center q (insertArc E f.val.1 f.val.2) X.V)⁻¹
           (∃v : X.V,E f.val.1 v=true ∧ 0≤cut q (fun x y=>X.D y x) X.V S (H v)) ∨
           (∃k : X.V,E k f.val.2=true ∧ 0≤cut q X.D X.V S (fun i=>H i k))) :
    SharedArcPivotGate.ProgressAt X F B J prices c := by
  obtain ⟨v,k,_,_,neg⟩ := rectangle_of_failed_cut X hq small F wp wm wr pc f sub size proper bad
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,wp,wm,wr,pc,f,v,k,neg⟩)))
end Native
end LeanCH.BR.Closure.SingleArcTensorMerge
#print axioms LeanCH.BR.Closure.SingleArcTensorMerge.identify
#print axioms LeanCH.BR.Closure.SingleArcTensorMerge.bounds_span
#print axioms LeanCH.BR.Closure.SingleArcTensorMerge.ray_bound
#print axioms LeanCH.BR.Closure.SingleArcTensorMerge.all_cuts
#print axioms LeanCH.BR.Closure.SingleArcTensorMerge.rectangle_of_failed_cut
#print axioms LeanCH.BR.Closure.SingleArcTensorMerge.progress
