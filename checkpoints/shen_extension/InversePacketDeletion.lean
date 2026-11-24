import checkpoints.shen_extension.InverseOffDiagonal
import checkpoints.shen_extension.SharedArcPacketReturns

namespace LeanCH.BR.InverseOffDiagonal
open Finset Matrix FiniteCutInverse WeightedSD
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem recover {R H : Matrix ι ι ℝ} (inv : CommonInverse R H) (w : ι → ℝ) :
    H *ᵥ (excess R *ᵥ w) = w := by
  rw [mulVec_mulVec,mul_eq_one_comm.mp inv.right,one_mulVec]

/-- At a zero coordinate all the surplus is concentrated on that one label. -/
theorem single_ray {R H : Matrix ι ι ℝ} (inv : CommonInverse R H)
    (pos : ∀ i j, i ≠ j → 0 < H i j) (w : ι → ℝ) (hw : w ≠ 0)
    (good : ∀ i, 0 ≤ (excess R *ᵥ w) i) {b : ι} (hb : w b = 0) :
    ∃ t : ℝ, 0 < t ∧ H b b = 0 ∧ ∀ i, w i = t * H i b := by
  let g := excess R *ᵥ w
  have eq (i : ι) : ∑ k, H i k * g k = w i := congrFun (recover inv w) i
  have outside (k : ι) (ne : k ≠ b) : g k = 0 := by
    have le := single_le_sum (s := univ) (f := fun l => H b l * g l)
      (fun l _ => mul_nonneg (inv.nonneg b l) (good l)) (mem_univ k)
    rw [eq,hb] at le
    exact le_antisymm (nonpos_of_mul_nonpos_right le (pos b k ne.symm)) (good k)
  have ray (i : ι) : w i = g b * H i b := by
    rw [← eq i, sum_eq_single b, mul_comm]
    · intro k _ ne
      rw [outside k ne,mul_zero]
    · simp
  have live : 0 < g b := by
    by_contra! zero
    have z := le_antisymm zero (good b)
    exact hw (funext fun i => by simp [ray i,z])
  refine ⟨g b,live,?_,ray⟩
  exact (mul_eq_zero.mp ((ray b).symm.trans hb)).resolve_left live.ne'

/-- A missing entry of size t gives a multiplicative lower bound at its head. -/
private theorem head_bound {R S H : Matrix ι ι ℝ} (inv : CommonInverse R H)
    (w : ι → ℝ) (wn : ∀ i, 0 ≤ w i) (good : ∀ i, 0 ≤ (excess S *ᵥ w) i)
    (sub : ∀ i j, S i j ≤ R i j) (a b : ι) :
    (∀ i, 0 ≤ (excess R *ᵥ w) i) ∧ (R a b - S a b) * H b a * w b ≤ w b := by
  let g := excess R *ᵥ w
  have delta (i : ι) : g i = (excess S *ᵥ w) i + ∑ j, (R i j - S i j) * w j := by
    change (∑ j, (R i j - 1) * w j) = (∑ j, (S i j - 1) * w j) + _
    rw [←sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have nn (i j : ι) := mul_nonneg (sub_nonneg.mpr (sub i j)) (wn j)
  have gn (i : ι) : 0 ≤ g i := by
    rw [delta]; exact add_nonneg (good i) (sum_nonneg fun j _ => nn i j)
  have lower : (R a b - S a b) * w b ≤ g a := by
    rw [delta]; exact (single_le_sum (fun j _ => nn a j) (mem_univ b)).trans (le_add_of_nonneg_left (good a))
  have hi := single_le_sum (s := univ) (f := fun j => H b j * g j)
    (fun j _ => mul_nonneg (inv.nonneg b j) (gn j)) (mem_univ a)
  have atb : ∑ j, H b j * g j = w b := congrFun (recover inv w) b
  rw [atb] at hi
  refine ⟨gn,?_⟩
  calc
    _ = H b a * ((R a b - S a b) * w b) := by ring
    _ ≤ H b a * g a := mul_le_mul_of_nonneg_left lower (inv.nonneg b a)
    _ ≤ w b := hi

theorem single_strict {R S H : Matrix ι ι ℝ} (inv : CommonInverse R H)
    (pos : ∀ i j, i ≠ j → 0 < H i j) (sub : ∀ i j, S i j ≤ R i j)
    (a b : ι) (strict : 1 < (R a b - S a b) * H b a)
    (w : ι → ℝ) (wn : ∀ i, 0 ≤ w i) (live : w ≠ 0)
    (good : ∀ i, 0 ≤ (excess S *ᵥ w) i) :
    w b = 0 ∧ ∃ t : ℝ, 0 < t ∧ H b b = 0 ∧ ∀ i, w i = t * H i b := by
  obtain ⟨gn,le⟩ := head_bound inv w wn good sub a b
  have zero : w b = 0 := by
    by_contra nz
    exact (lt_mul_of_one_lt_left (lt_of_le_of_ne (wn b) (Ne.symm nz)) strict).not_ge le
  exact ⟨zero,single_ray inv pos w live gn zero⟩

theorem two_strict {R S H : Matrix ι ι ℝ} (inv : CommonInverse R H)
    (pos : ∀ i j, i ≠ j → 0 < H i j) (sub : ∀ i j, S i j ≤ R i j)
    {a b c d : ι} (ne : d ≠ b) (first : 1 < (R a b - S a b) * H b a)
    (second : 1 < (R c d - S c d) * H d c)
    (w : ι → ℝ) (wn : ∀ i, 0 ≤ w i) (good : ∀ i, 0 ≤ (excess S *ᵥ w) i) : w = 0 := by
  by_contra live
  obtain ⟨_,t,ht,_,ray⟩ := single_strict inv pos sub a b first w wn live good
  have zd := (single_strict inv pos sub c d second w wn live good).1
  exact (mul_pos ht (pos d b ne)).ne' ((ray d).symm.trans zd)

theorem strict_dual [Nonempty ι] (S : Matrix ι ι ℝ)
    (collapse : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ (excess S *ᵥ w) i) → w = 0) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ ∀ j, (p ᵥ* S) j < 1 := by
  let M : ι → ι → ℝ := fun i j => -S i j
  obtain ⟨w,hw,p,hp,saddle⟩ := FiniteDual.exists_saddle M
  have fail : ∃ i, (S *ᵥ w) i < 1 := by
    by_contra! ge
    have z := collapse w hw.1 (fun i => by
      have h : (excess S *ᵥ w) i = (S *ᵥ w) i - ∑ j, w j := by
        simp [excess,mulVec,dotProduct,sub_mul,sum_sub_distrib]
      rw [h,hw.2]; linarith [ge i])
    have mass := hw.2
    rw [z] at mass
    simp at mass
  obtain ⟨i,hi⟩ := fail
  refine ⟨p,hp.1,hp.2,fun j => ?_⟩
  have h := saddle (FiniteDual.point j) (FiniteDual.point_mem j)
    (FiniteDual.point i) (FiniteDual.point_mem i)
  rw [FiniteDual.payoff_point_right,FiniteDual.payoff_point_left] at h
  change (∑ k, (-S i k) * w k) ≤ ∑ k, p k * (-S k j) at h
  simp only [neg_mul,mul_neg,sum_neg_distrib,neg_le_neg_iff] at h
  exact h.trans_lt hi

end LeanCH.BR.InverseOffDiagonal

#print axioms LeanCH.BR.InverseOffDiagonal.single_strict
#print axioms LeanCH.BR.InverseOffDiagonal.two_strict
#print axioms LeanCH.BR.InverseOffDiagonal.strict_dual

