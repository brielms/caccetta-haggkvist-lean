import LeanCH.BR.BRFiniteInverseDiagonal
import LeanCH.BR.BRWeightedInverseComparison
import LeanCH.BR.BRFiniteDeletionThreshold

namespace LeanCH.BR.InverseOffDiagonal
open Finset Matrix InverseDiagonal FiniteCutInverse WeightedSD
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Replace equation j by the value of coordinate i. -/
private def bordered (q : ℕ) (A : Matrix ι ι ℤ) (i j : ι) : Matrix ι ι ℤ :=
  fun k l => if k = j then (if i = l then 1 else 0)
    else (if k = l then 1 else 0) + (q : ℤ) * A k l - 1

private theorem bordered_det_ne {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ)
    {i j : ι} (hne : i ≠ j) : (bordered q A i j).det ≠ 0 := by
  classical
  let : Fact (1 < q) := ⟨by omega⟩
  let f := Int.castRingHom (ZMod q)
  let M := f.mapMatrix (bordered q A i j)
  have entry (k l : ι) : M k l = if k = j then (if i = l then 1 else 0)
      else (if k = l then 1 else 0) - 1 := by
    change (((bordered q A i j k l : ℤ) : ZMod q)) = _
    unfold bordered
    split_ifs <;> simp
  have eval (x : ι → ZMod q) (k : ι) : (M *ᵥ x) k =
      if k = j then x i else x k - ∑ l, x l := by
    by_cases hk : k = j <;> simp [mulVec,dotProduct,entry,hk,ite_mul,sub_mul,sum_sub_distrib]
  have onto : Function.Surjective M.mulVec := by
    intro y
    let s := y j - y i
    let x : ι → ZMod q := fun k => if k = j then
      s - ∑ l ∈ univ.erase j, (y l + s) else y k + s
    have tot : ∑ l, x l = s := by
      rw [← sum_erase_add (s := univ) x (mem_univ j)]
      have he : ∑ l ∈ univ.erase j, x l = ∑ l ∈ univ.erase j, (y l + s) :=
        sum_congr rfl fun l hl => ite_eq_right (mem_erase.mp hl).1
      rw [he]
      simp [x]
    refine ⟨x,funext fun k => ?_⟩
    rw [eval,tot]
    by_cases hk : k = j
    · subst k
      simp [x,hne,s]
    · simp [hk,x]
  have hunit := (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_surjective_iff_isUnit.mp onto)
  intro hz
  have hm : M.det = 0 := by
    change (f.mapMatrix (bordered q A i j)).det = 0
    rw [← RingHom.map_det,hz,map_zero]
  exact hunit.ne_zero hm

/-- No off-diagonal of a real inverse of I+qA-J can vanish, for integral A. -/
theorem ne_zero {q : ℕ} (hq : 2 ≤ q) (A : Matrix ι ι ℤ) (H : Matrix ι ι ℝ)
    (inverse : centeredInteger q A * H = 1) {i j : ι} (hne : i ≠ j) : H i j ≠ 0 := by
  classical
  let f := Int.castRingHom ℝ
  let M := f.mapMatrix (bordered q A i j)
  have hdet : M.det ≠ 0 := by
    change (f.mapMatrix (bordered q A i j)).det ≠ 0
    rw [← RingHom.map_det]
    change (((bordered q A i j).det : ℤ) : ℝ) ≠ 0
    exact_mod_cast bordered_det_ne hq A hne
  have inject := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))
  have entry (k l : ι) : M k l = if k = j then (if i = l then 1 else 0)
      else centeredInteger q A k l := by
    change (((bordered q A i j k l : ℤ) : ℝ)) = _
    unfold bordered centeredInteger
    split_ifs <;> simp
  intro hz
  have eq : M *ᵥ (fun l => H l j) = M *ᵥ 0 := by
    rw [mulVec_zero]
    funext k
    by_cases hk : k = j
    · simp [mulVec,dotProduct,entry,hk,ite_mul,hz]
    · have e := congrArg (fun N : Matrix ι ι ℝ => N k j) inverse
      simpa [mulVec,dotProduct,entry,hk,Matrix.mul_apply,Matrix.one_apply] using e
  have col := inject eq
  have e := congrArg (fun N : Matrix ι ι ℝ => N j j) inverse
  simp only [Matrix.mul_apply,Matrix.one_apply_eq] at e
  have zero (l : ι) : H l j = 0 := congrFun col l
  simp [zero] at e

theorem graph_positive {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H)
    {i j : V} (hne : i ≠ j) : 0 < H i j := by
  have e : centeredInteger q (adjacencyMatrix D V) = excess (realMatrix q D V) := by
    ext a b
    cases h : D a b <;> simp [centeredInteger,excess,realMatrix_entry,adjacencyMatrix,h]
  exact lt_of_le_of_ne (inv.nonneg i j) (Ne.symm (ne_zero hq _ H (e ▸ inv.right) hne))

end LeanCH.BR.InverseOffDiagonal

#print axioms LeanCH.BR.InverseOffDiagonal.graph_positive

