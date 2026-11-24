import checkpoints.shen_extension.GlobalFamilyDual
import LeanCH.BR.BRWeightedInverseComparison

namespace LeanCH.BR.Closure.PunctureLawMixture
open Finset Matrix FiniteCutInverse
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The omitted column in each row may differ. The same positive right-hand
test still gives an order-reflecting matrix when all other entries are nonpositive. -/
private theorem reflect (B : Matrix ι ι ℝ) (x : ι→ℝ) (xp : ∀i,0<x i)
    (sign : ∀i j,i≠j → B i j≤0) (up : ∀i,0<(B *ᵥ x) i)
    (v : ι→ℝ) (u : ∀i,0≤(B *ᵥ v) i) (a : ι) : 0≤v a := by
  classical
  by_contra! neg
  obtain ⟨k,_,least⟩ := exists_min_image (univ : Finset ι) (fun i => v i/x i) ⟨a,mem_univ a⟩
  let t := v k/x k
  have tn : t<0 := (least a (mem_univ a)).trans_lt (div_neg_of_neg_of_pos neg (xp a))
  have eq : v k=t*x k := (div_mul_cancel₀ _ (xp k).ne').symm
  have le (j) : B k j*v j≤B k j*(t*x j) := by
    by_cases same : k=j
    · subst j; rw [←eq]
    · exact mul_le_mul_of_nonpos_left ((le_div_iff₀ (xp j)).mp (least j (mem_univ j))) (sign k j same)
  have sum := sum_le_sum (s:=univ) (fun j _ => le j)
  have calcEq : (∑j,B k j*(t*x j))=t*(B *ᵥ x) k := by
    change _=t*∑j,B k j*x j
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  exact ((u k).trans (sum.trans_eq calcEq)).not_gt (mul_neg_of_neg_of_pos tn (up k))

private theorem inverse_pos (B : Matrix ι ι ℝ) (x : ι→ℝ) (xp : ∀i,0<x i)
    (sign : ∀i j,i≠j → B i j≤0) (up : ∀i,0<(B *ᵥ x) i) :
    IsUnit B ∧ ∀i j,0≤B⁻¹ i j := by
  classical
  have inj : Function.Injective (B *ᵥ ·) := by
    intro v w same
    change B *ᵥ v=B *ᵥ w at same
    have zero : B *ᵥ (v-w)=0 := by rw [Matrix.mulVec_sub,same,sub_self]
    have rev : B *ᵥ (w-v)=0 := by rw [Matrix.mulVec_sub,same,sub_self]
    funext i
    have a := reflect B x xp sign up (v-w) (fun j => by rw [zero]; exact le_rfl) i
    have b := reflect B x xp sign up (w-v) (fun j => by rw [rev]; exact le_rfl) i
    change 0≤v i-w i at a
    change 0≤w i-v i at b
    linarith
  have unit := Matrix.mulVec_injective_iff_isUnit.mp inj
  have inv := B.mul_nonsing_inv (B.isUnit_iff_isUnit_det.mp unit)
  refine ⟨unit,fun i j => reflect B x xp sign up (fun k => B⁻¹ k j) (fun k => ?_) i⟩
  change 0≤(B*B⁻¹) k j
  rw [inv]
  by_cases e : k=j <;> simp [Matrix.one_apply,e]

/-- For every simultaneous choice of puncture laws, a strictly positive
mixture recovers the prescribed column equalizer exactly at every vertex. -/
theorem glue (R H M : Matrix ι ι ℝ) (inverse : CommonInverse R H) (x p : ι→ℝ) (c : ℝ)
    (high : 1<c) (xp : ∀i,0<x i) (xm : ∑i,x i=1) (pm : ∑i,p i=1)
    (rows : ∀i,(R *ᵥ x) i=c) (cols : ∀j,(p ᵥ* R) j=c)
    (unit : ∀i,∑j,M i j=1) (offDiag : ∀i j,i≠j → ((M i) ᵥ* R) j≤1) :
    let B := M * excess R
    IsUnit M ∧ ∃ l : ι→ℝ, (∀i,0<l i) ∧ (∑i,l i)=1 ∧ l ᵥ* M=p ∧
      (∀i,c-1≤l i*B i i) ∧ ∀i, l i*B i i=(c-1)+∑j∈univ.erase i,l j*(-B j i) := by
  classical
  intro B
  have orig : excess R *ᵥ x = fun _ => c-1 := by
    funext i; rw [FiniteCutInverse.mulVec_excess,rows,xm]
  have bval (i j) : B i j=((M i) ᵥ* R) j-1 := by
    change ((M i) ᵥ* excess R) j=_
    rw [vecMul_excess,unit]
  have off (i j) (ne : i≠j) : B i j≤0 := by rw [bval]; exact sub_nonpos.mpr (offDiag i j ne)
  have bx : B *ᵥ x=fun _ => c-1 := by
    change (M*excess R) *ᵥ x=_
    rw [←Matrix.mulVec_mulVec,orig]
    funext i
    change (∑j,M i j*(c-1))=_
    rw [←sum_mul,unit,one_mul]
  obtain ⟨ub,nneg⟩ := inverse_pos B x xp off (fun i => by rw [bx]; exact sub_pos.mpr high)
  have um : IsUnit M := by
    have both : IsUnit (M * excess R) := ub
    apply M.isUnit_iff_isUnit_det.mpr
    have det := (M*excess R).isUnit_iff_isUnit_det.mp both
    rw [Matrix.det_mul] at det
    exact isUnit_of_mul_isUnit_left det
  let l := (fun _ : ι => c-1) ᵥ* B⁻¹
  have ln (i) : 0≤l i := sum_nonneg (fun j _ => mul_nonneg (sub_nonneg.mpr high.le) (nneg j i))
  have eq : l ᵥ* B=fun _ => c-1 := by
    dsimp only [l]
    rw [Matrix.vecMul_vecMul,B.nonsing_inv_mul (B.isUnit_iff_isUnit_det.mp ub),Matrix.vecMul_one]
  have pe : p ᵥ* excess R=fun _ => c-1 := by funext j; rw [vecMul_excess,cols,pm]
  have recover : l ᵥ* M=p := by
    have same : (l ᵥ* M) ᵥ* excess R=p ᵥ* excess R := by rw [Matrix.vecMul_vecMul,pe]; exact eq
    have := congrArg (fun v => v ᵥ* H) same
    simpa only [Matrix.vecMul_vecMul,Matrix.mul_assoc,inverse.right,Matrix.vecMul_one,Matrix.mul_one] using this
  have total : (∑i,l i)=1 := by
    rw [←pm,←recover]
    change _=∑j,∑i,l i*M i j
    rw [sum_comm]; simp only [←mul_sum,unit,mul_one]
  have bal (i) : l i*B i i=(c-1)+∑j∈univ.erase i,l j*(-B j i) := by
    have part := sum_erase_add univ (fun j => l j*B j i) (mem_univ i)
    have all : (∑j,l j*B j i)=c-1 := congrFun eq i
    rw [all] at part
    simp only [mul_neg,sum_neg_distrib]
    linarith
  have flo (i) : c-1≤l i*B i i := by
    rw [bal]
    exact le_add_of_nonneg_right (sum_nonneg (fun j hj => mul_nonneg (ln j) (neg_nonneg.mpr (off j i (mem_erase.mp hj).1))))
  refine ⟨um,l,fun i => lt_of_le_of_ne (ln i) (fun zero => ?_),total,recover,flo,bal⟩
  have low := flo i
  rw [←zero,zero_mul] at low
  linarith

#print axioms glue
end LeanCH.BR.Closure.PunctureLawMixture
