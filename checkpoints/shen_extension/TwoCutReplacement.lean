import checkpoints.shen_extension.PunctureParentFlow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

namespace LeanCH.BR.Closure.TwoCutReplacement
open Finset Matrix FiniteCutInverse
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend a ray to the boundary of the singleton mixture. Mix the two rays
until a coordinate in each prescribed block reaches zero simultaneously. -/
private theorem tie (S T : Finset ι) (hs : S.Nonempty) (ht : T.Nonempty)
    (l u v f g : ι→ℝ) (lp : ∀i,0<l i) (us : ∑i,u i=1) (vs : ∑i,v i=1)
    {d : ℝ} (dp : 0<d) (offS : ∀i,i∉S → f i≤0) (offT : ∀i,i∉T → g i≤0)
    (sep : Disjoint S T)
    (boundary : ∀ a b : ℝ,0≤a → 0≤b → (∀i,a*u i+b*v i≤l i) →
      ∀i,a*u i+b*v i=l i → d≤a*f i+b*g i) :
    ∃a b : ℝ,0<a ∧ 0<b ∧ (∀i,a*u i+b*v i≤l i) ∧
      ∃y∈S,∃z∈T,a*u y+b*v y=l y ∧ a*u z+b*v z=l z ∧ d≤a*f y ∧ d≤b*g z := by
  classical
  let rate (i : ι) (t : ℝ) := ((1-t)*u i+t*v i)/l i
  let maxS (t : ℝ) := S.sup' hs (fun i => rate i t)
  let maxT (t : ℝ) := T.sup' ht (fun i => rate i t)
  have rc (i) : Continuous (rate i) := by dsimp [rate]; fun_prop
  have sc : Continuous maxS := Continuous.finset_sup'_apply hs (fun i _ => rc i)
  have tc : Continuous maxT := Continuous.finset_sup'_apply ht (fun i _ => rc i)
  have allLive : (univ : Finset ι).Nonempty := hs.mono (subset_univ S)
  let top (t : ℝ) := univ.sup' allLive (fun i => rate i t)
  have leTop (i) (t) : rate i t≤top t := le_sup' (s:=univ) (fun i => rate i t) (mem_univ i)
  have tp (t : ℝ) : 0<top t := by
    by_contra! no
    have zero (i : ι) : (1-t)*u i+t*v i≤0 := by
      have z := (div_le_iff₀ (lp i)).mp ((leTop i t).trans no)
      simpa only [zero_mul] using z
    have bad := sum_nonpos (s:=univ) (fun i _ => zero i)
    rw [sum_add_distrib,←mul_sum,←mul_sum,us,vs] at bad
    linarith
  let a (t : ℝ) := (1-t)/top t
  let b (t : ℝ) := t/top t
  have bound (t) (i) : a t*u i+b t*v i≤l i := by
    have rel := (div_le_iff₀ (lp i)).mp (leTop i t)
    dsimp only [a,b]
    field_simp [tp t]
    linarith only [rel]
  have hit (t) (i) (eq : rate i t=top t) : a t*u i+b t*v i=l i := by
    have rel := (div_eq_iff (lp i).ne').mp eq
    dsimp only [a,b]
    field_simp [(tp t).ne']
    linarith only [rel]
  have paid (t : ℝ) (h : t∈Set.Icc (0:ℝ) 1) (i) (win : rate i t=top t) :
      d≤a t*f i+b t*g i := boundary _ _ (div_nonneg (sub_nonneg.mpr h.2) (tp t).le)
        (div_nonneg h.1 (tp t).le) (bound t) i (hit t i win)
  have zeroIn (i) (win : rate i 0=top 0) : i∈S := by
    by_contra outside
    have p := paid 0 ⟨le_rfl,zero_le_one⟩ i win
    have n := mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) (tp 0).le : 0≤a 0) (offS i outside)
    simp only [b,zero_div,zero_mul,add_zero] at p
    change a 0*f i≤0 at n
    linarith
  have oneIn (i) (win : rate i 1=top 1) : i∈T := by
    by_contra outside
    have p := paid 1 ⟨zero_le_one,le_rfl⟩ i win
    have n := mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_one (tp 1).le : 0≤b 1) (offT i outside)
    simp only [a,sub_self,zero_div,zero_mul,zero_add] at p
    linarith
  have left : maxT 0<maxS 0 := by
    obtain ⟨i,_,hi⟩ := exists_mem_eq_sup' allLive (fun i => rate i 0)
    have inside := zeroIn i hi.symm
    obtain ⟨j,jT,hj⟩ := exists_mem_eq_sup' ht (fun i => rate i 0)
    have lt : rate j 0<top 0 := lt_of_le_of_ne (leTop j 0) fun eq => disjoint_left.mp sep (zeroIn j eq) jT
    change maxT 0=rate j 0 at hj
    change top 0=rate i 0 at hi
    rw [hj]
    exact lt.trans_le (hi.trans_le (le_sup' (fun i => rate i 0) inside))
  have right : maxS 1<maxT 1 := by
    obtain ⟨i,_,hi⟩ := exists_mem_eq_sup' allLive (fun i => rate i 1)
    have inside := oneIn i hi.symm
    obtain ⟨j,jS,hj⟩ := exists_mem_eq_sup' hs (fun i => rate i 1)
    have lt : rate j 1<top 1 := lt_of_le_of_ne (leTop j 1) fun eq => disjoint_left.mp sep jS (oneIn j eq)
    change maxS 1=rate j 1 at hj
    change top 1=rate i 1 at hi
    rw [hj]
    exact lt.trans_le (hi.trans_le (le_sup' (fun i => rate i 1) inside))
  obtain ⟨t,ht0,equal⟩ := intermediate_value_Icc zero_le_one (tc.sub sc).continuousOn
    (show (0:ℝ)∈Set.Icc (maxT 0-maxS 0) (maxT 1-maxS 1) from ⟨sub_nonpos.mpr left.le,sub_nonneg.mpr right.le⟩)
  change maxT t-maxS t=0 at equal
  have ti : 0<t ∧ t<1 := by
    refine ⟨lt_of_le_of_ne ht0.1 ?_,lt_of_le_of_ne ht0.2 ?_⟩
    · rintro rfl; linarith
    · rintro rfl; linarith
  have ap : 0<a t := div_pos (sub_pos.mpr ti.2) (tp t)
  have bp : 0<b t := div_pos ti.1 (tp t)
  obtain ⟨i,_,hi⟩ := exists_mem_eq_sup' allLive (fun i => rate i t)
  have inST : i∈S ∨ i∈T := by
    by_contra! neither
    have p := paid t ht0 i hi.symm
    linarith only [p,dp,mul_nonpos_of_nonneg_of_nonpos ap.le (offS i neither.1),
      mul_nonpos_of_nonneg_of_nonpos bp.le (offT i neither.2)]
  have ms : top t≤maxS t := by
    rcases inST with ins|int
    · exact (show top t=rate i t from hi).trans_le (le_sup' (fun i => rate i t) ins)
    · have le : rate i t≤maxT t := le_sup' (fun i => rate i t) int
      change top t=rate i t at hi
      linarith
  obtain ⟨y,ys,hy⟩ := exists_mem_eq_sup' hs (fun i => rate i t)
  obtain ⟨z,zt,hz⟩ := exists_mem_eq_sup' ht (fun i => rate i t)
  change maxS t=rate y t at hy
  change maxT t=rate z t at hz
  have yw : rate y t=top t := le_antisymm (leTop _ _) (ms.trans_eq hy)
  have zw : rate z t=top t := le_antisymm (leTop _ _) (by linarith)
  refine ⟨a t,b t,ap,bp,bound t,y,ys,z,zt,hit t y yw,hit t z zw,?_,?_⟩
  · linarith only [paid t ht0 y yw,mul_nonpos_of_nonneg_of_nonpos bp.le (offT y (disjoint_left.mp sep ys))]
  · linarith only [paid t ht0 z zw,mul_nonpos_of_nonneg_of_nonpos ap.le (offS z (disjoint_right.mp sep zt))]

/-- Two prescribed disjoint-block deletion laws coexist in an exact convex
decomposition of p. One singleton is retired in each block, and each retired
column has to pay its own full excess out of its own block's law. -/
theorem replace_two (R M : Matrix ι ι ℝ) (unitM : IsUnit M) (massM : ∀i,∑j,M i j=1)
    (off : ∀i j,i≠j → ((M i) ᵥ* R) j≤1) (p l : ι→ℝ) (lp : ∀i,0<l i)
    (lm : ∑i,l i=1) (recov : l ᵥ* M=p) {c : ℝ} (high : 1<c) (cols : ∀i,(p ᵥ* R) i=c)
    (S T : Finset ι) (hs : S.Nonempty) (ht : T.Nonempty) (sep : Disjoint S T)
    (u v : ι→ℝ) (um : ∑i,u i=1) (vm : ∑i,v i=1)
    (us : ∀i,i∉S → (u ᵥ* R) i≤1) (vt : ∀i,i∉T → (v ᵥ* R) i≤1) :
    ∃a b : ℝ,∃s : ι→ℝ,0<a ∧ 0<b ∧ (∀i,0≤s i) ∧ a+b+(∑i,s i)=1 ∧
      (∀i,p i=a*u i+b*v i+(s ᵥ* M) i) ∧
      ∃y∈S,∃z∈T,s y=0 ∧ s z=0 ∧ c-1≤a*((u ᵥ* R) y-1) ∧ c-1≤b*((v ᵥ* R) z-1) := by
  classical
  let U := u ᵥ* M⁻¹
  let W := v ᵥ* M⁻¹
  have invert (w : ι→ℝ) : (w ᵥ* M⁻¹) ᵥ* M=w := by
    rw [Matrix.vecMul_vecMul,M.nonsing_inv_mul (M.isUnit_iff_isUnit_det.mp unitM),Matrix.vecMul_one]
  have mass (w : ι→ℝ) : (∑j,(w ᵥ* M) j)=∑i,w i := by
    change (∑j,∑i,w i*M i j)=_
    rw [sum_comm]
    simp only [←mul_sum,massM,mul_one]
  have eu : ∑i,U i=1 := by rw [←mass U,show U ᵥ* M=u from invert u,um]
  have ev : ∑i,W i=1 := by rw [←mass W,show W ᵥ* M=v from invert v,vm]
  let B := M*excess R
  have price (w : ι→ℝ) (h : ∑i,w i=1) (i) : (w ᵥ* excess R) i=(w ᵥ* R) i-1 := by rw [vecMul_excess,h]
  have bound (a b : ℝ) (_ : 0≤a) (_ : 0≤b) (cap : ∀j,a*U j+b*W j≤l j)
      (i) (eq : a*U i+b*W i=l i) : c-1≤a*((u ᵥ* R) i-1)+b*((v ᵥ* R) i-1) := by
    have pm : ∑j,p j=1 := recov ▸ (mass l).trans lm
    have lcol : (l ᵥ* B) i=c-1 := by
      dsimp only [B]; rw [←Matrix.vecMul_vecMul,recov,price p pm,cols]
    have ucol : (U ᵥ* B) i=(u ᵥ* R) i-1 := by
      dsimp only [B]; rw [←Matrix.vecMul_vecMul,show U ᵥ* M=u from invert u,price u um]
    have wcol : (W ᵥ* B) i=(v ᵥ* R) i-1 := by
      dsimp only [B]; rw [←Matrix.vecMul_vecMul,show W ᵥ* M=v from invert v,price v vm]
    rw [←lcol,←ucol,←wcol]
    change (∑j,l j*B j i)≤a*(∑j,U j*B j i)+b*(∑j,W j*B j i)
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro j _
    rw [←mul_assoc,←mul_assoc,←add_mul]
    by_cases ji : j=i
    · subst j; rw [eq]
    · have col : B j i≤0 := by
        change ((M j) ᵥ* excess R) i≤0
        rw [price _ (massM j)]; exact sub_nonpos.mpr (off j i ji)
      exact mul_le_mul_of_nonpos_right (cap j) col
  obtain ⟨a,b,ap,bp,cap,y,ys,z,zt,ey,ez,fy,fz⟩ := tie S T hs ht l U W
    (fun i => (u ᵥ* R) i-1) (fun i => (v ᵥ* R) i-1) lp eu ev (sub_pos.mpr high)
    (fun i hi => sub_nonpos.mpr (us i hi)) (fun i hi => sub_nonpos.mpr (vt i hi)) sep bound
  let s := fun i => l i-(a*U i+b*W i)
  have norm : a+b+(∑i,s i)=1 := by
    dsimp only [s]
    rw [sum_sub_distrib,sum_add_distrib,←mul_sum,←mul_sum,eu,ev,lm]
    ring
  refine ⟨a,b,s,ap,bp,fun i => sub_nonneg.mpr (cap i),norm,?_,y,ys,z,zt,
    sub_eq_zero.mpr ey.symm,sub_eq_zero.mpr ez.symm,fy,fz⟩
  intro i
  rw [←recov,←invert u,←invert v]
  change (∑j,l j*M j i)=a*(∑j,U j*M j i)+b*(∑j,W j*M j i)+(∑j,s j*M j i)
  rw [mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib]
  exact sum_congr rfl fun j _ => by dsimp only [s]; ring

#print axioms replace_two

end LeanCH.BR.Closure.TwoCutReplacement
