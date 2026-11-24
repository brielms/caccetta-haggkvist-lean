import LeanCH.BR.BRWeightedArithmetic
import LeanCH.BR.BRWeightedOrderArithmetic
import Mathlib.Basic.Real.Basic

/-! Zero inverse diagonals retain arithmetic information about the original
integer coefficient. No girth or induction premise occurs here. -/
namespace LeanCH.BR.InverseDiagonal
open Finset Matrix WeightedArithmetic
open scoped Matrix
set_option maxHeartbeats 40000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def centeredInteger (q : ℕ) (A : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then 1 else 0) + q*(A i j : ℝ)-1

theorem real_unit_card_mod {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ)
    (x : ι → ℝ) (hm : ∑ i, x i = 1)
    (hr : ∀ i, x i + (q : ℝ) * ∑ j, (A i j : ℝ) * x j = 1) :
    (Fintype.card ι : ZMod q) = 1 := by
  obtain ⟨r,hrat⟩ := rational_surjective hq A (fun _ => 1)
  let C : Matrix ι ι ℝ := (Rat.castHom ℝ).mapMatrix (rationalMatrix q A)
  have hdet : C.det ≠ 0 := by
    dsimp only [C]
    rw [← RingHom.map_det]
    change ((rationalMatrix q A).det : ℝ) ≠ 0
    exact_mod_cast rational_det_ne_zero hq A
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have heR : C *ᵥ (fun i => (r i : ℝ)) = fun _ => 1 := by
    funext i
    have hh := congrFun hrat i
    change (∑ j, rationalMatrix q A i j * r j) = 1 at hh
    change (∑ j, (rationalMatrix q A i j : ℝ) * (r j : ℝ)) = 1
    exact_mod_cast hh
  have hex : C *ᵥ x = fun _ => 1 := by
    funext i
    simpa [C,rationalMatrix,closedMatrix,Matrix.mulVec,dotProduct,
      Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_assoc,ite_mul,apply_ite] using hr i
  have he : (fun i => (r i : ℝ)) = x :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hu) (heR.trans hex.symm)
  apply WeightedOrderArithmetic.card_mod q A r
  · intro i
    simpa only [rational_mulVec_apply] using congrFun hrat i
  · have hh : ∑ i, (r i : ℝ) = 1 := by rw [he]; exact hm
    exact_mod_cast hh

/-- A zero diagonal and a nonzero column sum suffice; the inverse and the
column may be signed. The omitted-coordinate unit law is exact. -/
theorem zero_diagonal_card_mod {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ)
    (H : Matrix ι ι ℝ)
    (hH : centeredInteger q A * H = 1)
    (j : ι) (hz : H j j = 0) (hm : (∑ i, H i j) ≠ 0) :
    (Fintype.card ι : ZMod q) = 2 := by
  let U : Finset ι := univ.erase j
  let S : ℝ := ∑ i, H i j
  have hs : ∑ i ∈ U, H i j = S := by
    have he := sum_erase_add (s := univ) (f := fun i => H i j) (mem_univ j)
    simpa only [hz,add_zero] using he
  have hrow (i : ι) (hij : i ≠ j) :
      H i j + (q : ℝ)*(∑ k, (A i k : ℝ)*H k j) = S := by
    have he := congrArg (fun M : Matrix ι ι ℝ => M i j) hH
    simp only [Matrix.mul_apply,Matrix.one_apply,hij,ite_false,centeredInteger] at he
    simp only [sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ite_mul,one_mul,zero_mul,mul_assoc] at he
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum] at he
    dsimp only [S]
    linarith
  have hmod := real_unit_card_mod hq (fun i k : U => A i.val k.val)
    (fun i : U => H i.val j / S) (by
      rw [show (∑ i : U, H i.val j / S) = ∑ i ∈ U, H i j / S from
        Finset.sum_coe_sort U (fun i => H i j / S)]
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul,hs]
      exact mul_inv_cancel₀ hm) (by
      intro i
      change H i.val j / S + (q : ℝ)*(∑ k : U, (A i.val k.val : ℝ)*(H k.val j / S)) = 1
      have hi : (i : ι) ≠ j := (mem_erase.mp i.property).1
      have ht : ∑ k : U, (A i.val k.val : ℝ)*H k.val j = ∑ k, (A i.val k : ℝ)*H k j := by
        rw [Finset.sum_coe_sort U (fun k => (A i.val k : ℝ)*H k j)]
        have he := sum_erase_add (s := univ) (f := fun k => (A i k : ℝ)*H k j) (mem_univ j)
        simpa only [hz,mul_zero,add_zero] using he
      have hsdiv : (∑ k : U, (A i.val k.val : ℝ)*(H k.val j / S)) =
          (∑ k : U, (A i.val k.val : ℝ)*H k.val j)/S := by
        simp only [div_eq_mul_inv,← mul_assoc,← sum_mul]
      rw [hsdiv,ht,← mul_div_assoc,← add_div,hrow i hi]
      exact div_self hm)
  have hj : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  have hcard : Fintype.card U + 1 = Fintype.card ι := by
    simp only [Fintype.card_coe,U,card_erase_of_mem (mem_univ j),card_univ]
    omega
  have he := congrArg (fun n : ℕ => (n : ZMod q)) hcard
  push_cast at he
  rw [hmod] at he
  exact he.symm.trans (by norm_num)

end LeanCH.BR.InverseDiagonal
