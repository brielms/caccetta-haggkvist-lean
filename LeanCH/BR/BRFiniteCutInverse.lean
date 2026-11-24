import LeanCH.BR.BRWeightedStrictNormal
import Mathlib.Basic.Real.Basic

/-! One common inverse constrains every induced-cut certificate. These are
finite matrix statements; no graph cycle hypothesis is hidden here. -/
namespace LeanCH.BR.FiniteCutInverse
open Finset Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def excess (R : Matrix V V ℝ) : Matrix V V ℝ := fun i j => R i j - 1

structure CommonInverse (R H : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ H i j
  right : excess R * H = 1

structure CutCertificate (R : Matrix V V ℝ) (M : Finset V) (p : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ p v
  mass : (∑ v, p v) = 1
  outside : ∀ v, v ∉ M → p v = 0
  columns : ∀ v ∈ M, (p ᵥ* R) v ≤ 1

theorem vecMul_excess (R : Matrix V V ℝ) (p : V → ℝ) (i : V) :
    (p ᵥ* excess R) i = (p ᵥ* R) i - ∑ v, p v := by
  simp [excess, Matrix.vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]

theorem recovery {R H : Matrix V V ℝ} (h : CommonInverse R H)
    (p : V → ℝ) (hm : (∑ v, p v) = 1) (k : V) :
    p k = ∑ z, ((p ᵥ* R) z - 1) * H z k := by
  have he := congrFun (show (p ᵥ* excess R) ᵥ* H = p from by
    rw [Matrix.vecMul_vecMul, h.right, Matrix.vecMul_one]) k
  calc
    p k = ((p ᵥ* excess R) ᵥ* H) k := he.symm
    _ = _ := by
      change (∑ z, (p ᵥ* excess R) z * H z k) = _
      simp only [vecMul_excess, hm]

theorem residual_columns {R H : Matrix V V ℝ} (h : CommonInverse R H)
    (b : V → ℝ) (hm : (∑ v, (b ᵥ* H) v) = 1) (k : V) :
    ((b ᵥ* H) ᵥ* R) k = 1 + b k := by
  have hl : H * excess R = 1 := mul_eq_one_comm.mp h.right
  have he : (b ᵥ* H) ᵥ* excess R = b := by
    rw [Matrix.vecMul_vecMul, hl, Matrix.vecMul_one]
  have hk := congrFun he k
  rw [vecMul_excess, hm] at hk
  linarith

/-- Exact characterization: these shared-inverse constraints reconstruct
an actual cut certificate, rather than merely bounding possible ones. -/
theorem cut_cone_iff {R H : Matrix V V ℝ} (h : CommonInverse R H)
    (M : Finset V) (b : V → ℝ) :
    ((∀ k, 0 ≤ (b ᵥ* H) k) ∧ (∑ k, (b ᵥ* H) k) = 1 ∧
      (∀ k, k ∉ M → (b ᵥ* H) k = 0) ∧ (∀ k ∈ M, b k ≤ 0)) ↔
    ∃ p, CutCertificate R M p ∧ ∀ k, (p ᵥ* R) k - 1 = b k := by
  constructor
  · rintro ⟨hn, hm, hz, hb⟩
    refine ⟨b ᵥ* H, ⟨hn, hm, hz, ?_⟩, ?_⟩
    · intro k hk
      rw [residual_columns h b hm k]
      linarith [hb k hk]
    · intro k
      rw [residual_columns h b hm k]
      ring
  · rintro ⟨p, hp, hb⟩
    have he : p = b ᵥ* H := by
      funext k
      rw [recovery h p hp.mass k]
      change (∑ z, ((p ᵥ* R) z - 1) * H z k) = ∑ z, b z * H z k
      exact Finset.sum_congr rfl (fun z hz => by rw [hb z])
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← he]; exact hp.nonneg
    · rw [← he]; exact hp.mass
    · rw [← he]; exact hp.outside
    · intro k hk
      rw [← hb k]
      linarith [hp.columns k hk]

theorem cut_identity {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {M : Finset V} {p : V → ℝ} (hp : CutCertificate R M p) (k : V) :
    (∑ z ∈ univ \ M, ((p ᵥ* R) z - 1) * H z k) =
      p k + ∑ z ∈ M, (1 - (p ᵥ* R) z) * H z k := by
  have hs := Finset.sum_sdiff (Finset.subset_univ M)
    (f := fun z => ((p ᵥ* R) z - 1) * H z k)
  have hr := recovery h p hp.mass k
  have hn : (∑ z ∈ M, (1 - (p ᵥ* R) z) * H z k) =
      -(∑ z ∈ M, ((p ᵥ* R) z - 1) * H z k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hn]
  linarith

theorem cut_packing {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {M : Finset V} {p : V → ℝ} (hp : CutCertificate R M p) (k : V) :
    (∑ z ∈ M, (1 - (p ᵥ* R) z) * H z k) ≤
      ∑ z ∈ univ \ M, ((p ᵥ* R) z - 1) * H z k := by
  rw [cut_identity h hp k]
  linarith [hp.nonneg k]

theorem omitted_identity {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {M : Finset V} {p : V → ℝ} (hp : CutCertificate R M p)
    {k : V} (hk : k ∉ M) :
    (∑ z ∈ univ \ M, ((p ᵥ* R) z - 1) * H z k) =
      ∑ z ∈ M, (1 - (p ᵥ* R) z) * H z k := by
  rw [cut_identity h hp k, hp.outside k hk, zero_add]

/-- A positive coordinate must be supplied by an actually overloaded
outside column through a positive entry of the SAME common inverse. -/
theorem positive_source {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {M : Finset V} {p : V → ℝ} (hp : CutCertificate R M p)
    {k : V} (hk : 0 < p k) :
    ∃ z, z ∉ M ∧ 1 < (p ᵥ* R) z ∧ 0 < H z k := by
  have hex : ∃ z, 0 < ((p ᵥ* R) z - 1) * H z k := by
    by_contra hn
    push Not at hn
    have hs := Finset.sum_nonpos (s := univ) (fun z _ => hn z)
    rw [← recovery h p hp.mass k] at hs
    linarith
  obtain ⟨z, hz⟩ := hex
  have hr : 0 < (p ᵥ* R) z - 1 :=
    (mul_pos_iff.mp hz).resolve_right (fun hh => (not_lt_of_ge (h.nonneg z k)) hh.2) |>.1
  have hh : 0 < H z k := by
    by_contra hn
    have he : H z k = 0 := le_antisymm (le_of_not_gt hn) (h.nonneg z k)
    rw [he, mul_zero] at hz
    exact (lt_irrefl 0) hz
  refine ⟨z, ?_, by linarith, hh⟩
  intro hm
  linarith [hp.columns z hm]

theorem deletion_identity {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {p : V → ℝ} {j : V} (hp : CutCertificate R (univ.erase j) p) (k : V) :
    ((p ᵥ* R) j - 1) * H j k =
      p k + ∑ z ∈ univ.erase j, (1 - (p ᵥ* R) z) * H z k := by
  have he : univ \ (univ.erase j) = {j} := by ext z; simp
  simpa only [he, Finset.sum_singleton] using cut_identity h hp k

theorem deletion_overload {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {p : V → ℝ} {j : V} (hp : CutCertificate R (univ.erase j) p) :
    1 < (p ᵥ* R) j := by
  have hex : ∃ k, 0 < p k := by
    by_contra hn
    push Not at hn
    have hs := Finset.sum_nonpos (s := univ) (fun k _ => hn k)
    rw [hp.mass] at hs
    norm_num at hs
  obtain ⟨k, hk⟩ := hex
  obtain ⟨z, hz, hc, _⟩ := positive_source h hp hk
  have he : z = j := by simpa using hz
  simpa only [he] using hc

theorem deletion_entry_bound {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {p : V → ℝ} {j u : V} (hp : CutCertificate R (univ.erase j) p)
    (hu : u ≠ j) (k : V) :
    (1 - (p ᵥ* R) u) * H u k ≤ ((p ᵥ* R) j - 1) * H j k := by
  have hs := Finset.single_le_sum (s := univ.erase j)
    (fun z hz => mul_nonneg (sub_nonneg.mpr (hp.columns z hz)) (h.nonneg z k))
    (show u ∈ univ.erase j by simp [hu])
  rw [deletion_identity h hp k]
  linarith [hp.nonneg k]

theorem zero_diagonal_separation {R H : Matrix V V ℝ} (h : CommonInverse R H)
    {p : V → ℝ} {j u : V} (hp : CutCertificate R (univ.erase j) p)
    (hz : H j j = 0) (hu : u ≠ j) (hs : (p ᵥ* R) u < 1) : H u j = 0 := by
  have he := deletion_entry_bound h hp hu j
  rw [hz, mul_zero] at he
  have hp' : 0 < 1 - (p ᵥ* R) u := by linarith
  have hn : H u j ≤ 0 := by nlinarith [h.nonneg u j]
  exact le_antisymm hn (h.nonneg u j)

/-- Cast the already proved rational inverse into real certificate space.
The negative inverse of J-R is a nonnegative inverse of R-J. -/
theorem commonInverse_of_strict (R : Matrix V V ℚ)
    (full : WeightedStrictNormal.Full (WeightedStrictNormal.deficit R))
    (w : V → ℚ) (hw : ∀ i, 0 ≤ w i)
    (bad : ∀ i, (WeightedStrictNormal.deficit R *ᵥ w) i < 0) :
    ∃ H : Matrix V V ℝ, CommonInverse (fun i j => (R i j : ℝ)) H := by
  let B := WeightedStrictNormal.deficit R
  have hu := WeightedStrictNormal.matrix_isUnit B full w hw bad
  have hn := WeightedStrictNormal.inverse_nonpos B full w hw bad
  let H : Matrix V V ℝ := fun i j => -(B⁻¹ i j : ℝ)
  refine ⟨H, ?_, ?_⟩
  · intro i j
    dsimp [H]
    have hh : (B⁻¹ i j : ℝ) ≤ 0 := by exact_mod_cast hn i j
    linarith
  · ext i j
    have he := congrArg (fun A : Matrix V V ℚ => A i j)
      (B.mul_nonsing_inv (B.isUnit_iff_isUnit_det.mp hu))
    change (∑ k, (1 - R i k) * B⁻¹ k j) = (if i = j then (1 : ℚ) else 0) at he
    have heR : (∑ k, (1 - (R i k : ℝ)) * (B⁻¹ k j : ℝ)) =
        (if i = j then 1 else 0) := by
      have hh := congrArg (fun x : ℚ => (x : ℝ)) he
      push_cast at hh
      by_cases hij : i = j <;> simpa [hij] using hh
    change (∑ k, ((R i k : ℝ) - 1) * -(B⁻¹ k j : ℝ)) = _
    calc
      _ = ∑ k, (1 - (R i k : ℝ)) * (B⁻¹ k j : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := heR

theorem mulVec_excess (R : Matrix V V ℝ) (w : V → ℝ) (i : V) :
    (excess R *ᵥ w) i = (R *ᵥ w) i - ∑ v, w v := by
  simp [excess, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- The strict inverse cannot be carried over to the equality branch.
An equalizer of mass one lies in the kernel of R-J. -/
theorem no_commonInverse_at_equality {R H : Matrix V V ℝ}
    (w : V → ℝ) (hm : (∑ v, w v) = 1) (hr : ∀ i, (R *ᵥ w) i = 1)
    (h : CommonInverse R H) : False := by
  have hx : excess R *ᵥ w = 0 := by
    funext i
    simp only [mulVec_excess, hr, hm, sub_self, Pi.zero_apply]
  have hl : H * excess R = 1 := mul_eq_one_comm.mp h.right
  have he : w = 0 := by
    calc
      w = (H * excess R) *ᵥ w := by rw [hl, Matrix.one_mulVec]
      _ = H *ᵥ (excess R *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hx, Matrix.mulVec_zero]
  rw [he] at hm
  simp at hm

end LeanCH.BR.FiniteCutInverse
