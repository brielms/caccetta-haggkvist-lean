import LeanCH.BR.BRFiniteCutInverse
import LeanCH.BR.BRWeightedDualCoverage

/-! Derived simultaneous cut constraints in a strict minimal weighted
obstruction. The same inverse is used for every proper induced cut. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix WeightedArithmetic FiniteCutInverse
open scoped Matrix

def realMatrix (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Matrix V V ℝ :=
  fun i j => (rationalMatrix q (adjacencyMatrix D V) i j : ℝ)

def hostCut (V M : Finset ℕ) : Finset V := univ.filter (fun i => i.val ∈ M)

def maskReal (M : Finset ℕ) (p : ℕ → ℝ) : ℕ → ℝ :=
  fun v => if v ∈ M then p v else 0

theorem realMatrix_col (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (p : ℕ → ℝ) (i : V) :
    ((fun j : V => p j) ᵥ* realMatrix q D V) i = realCol q D V p i := by
  have he := realCol_extendWeight q D V (fun j : V => p j) i
  change _ = (∑ j : V, p j * realMatrix q D V j i) at he
  change (∑ j : V, p j * realMatrix q D V j i) = _
  rw [← he]
  unfold realCol realInW
  rw [realExtendWeight_on]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [show realExtendWeight V (fun j : V => p j) j = p j from
    realExtendWeight_on V (fun j : V => p j) ⟨j, hj⟩]

theorem maskReal_mass {V M : Finset ℕ} (hMV : M ⊆ V) (p : ℕ → ℝ) :
    realMass V (maskReal M p) = realMass M p := by
  calc
    _ = ∑ v ∈ M, maskReal M p v :=
      (Finset.sum_subset hMV (fun v hv hn => by simp [maskReal, hn])).symm
    _ = _ := Finset.sum_congr rfl (fun v hv => by simp [maskReal, hv])

theorem maskReal_inW {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (p : ℕ → ℝ) (z : ℕ) :
    realInW D V (maskReal M p) z = realInW D M p z := by
  calc
    _ = ∑ v ∈ M, if D v z = true then maskReal M p v else 0 :=
      (Finset.sum_subset hMV (fun v hv hn => by simp [maskReal, hn])).symm
    _ = _ := Finset.sum_congr rfl (fun v hv => by simp [maskReal, hv])

theorem maskReal_col {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (p : ℕ → ℝ) {z : ℕ} (hz : z ∈ M) :
    realCol q D V (maskReal M p) z = realCol q D M p z := by
  simp only [realCol, maskReal_inW hMV, maskReal, if_pos hz]

theorem cutCertificate_of_realDual {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) {p : ℕ → ℝ} (hp : RealDual q D M 1 p) :
    CutCertificate (realMatrix q D V) (hostCut V M)
      (fun i : V => maskReal M p i) := by
  constructor
  · intro i
    by_cases hi : i.val ∈ M
    · simpa [maskReal, hi] using hp.nonneg i hi
    · simp [maskReal, hi]
  · rw [Finset.sum_coe_sort]
    exact (maskReal_mass hMV p).trans hp.normalized
  · intro i hi
    have hn : i.val ∉ M := by simpa [hostCut] using hi
    simp [maskReal, hn]
  · intro i hi
    have hm : i.val ∈ M := by simpa [hostCut] using hi
    rw [realMatrix_col, maskReal_col hMV p hm]
    exact hp.columns i hm

theorem strict_common_inverse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U) (hs : StrictPositiveRows q D V) :
    ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q D V) H := by
  obtain ⟨w, hw, hm, hr⟩ := hs
  have hb : ∀ i : V, (WeightedStrictNormal.deficit
      (rationalMatrix q (adjacencyMatrix D V)) *ᵥ (fun j : V => w j)) i < 0 := by
    intro i
    rw [WeightedStrictNormal.deficit_mulVec, Finset.sum_coe_sort, matrix_row]
    change mass V w - row q D V w i < 0
    rw [hm]
    linarith [hr i i.property]
  exact commonInverse_of_strict _ (full_deficit_of_proper hproper)
    (fun i : V => w i) (fun i => (hw i i.property).le) hb

/-- Certificate choices are independent existential choices, but every
one obeys the same inverse equations. No stationary marginal is assumed. -/
theorem strict_all_cut_certificates {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U) (hs : StrictPositiveRows q D V) :
    ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q D V) H ∧
      ∀ M ⊆ V, M.Nonempty → M ≠ V →
        ∃ p : V → ℝ, CutCertificate (realMatrix q D V) (hostCut V M) p := by
  obtain ⟨H, hH⟩ := strict_common_inverse hproper hs
  refine ⟨H, hH, ?_⟩
  intro M hMV hM hne
  obtain ⟨p, hp⟩ := realDual_of_selfDual (hproper M hMV hne) hM
  exact ⟨_, cutCertificate_of_realDual hMV hp⟩

/-- The outside supplier in the matrix recovery is an actual exterior
vertex with coverage above 1/q, not an abstract extra capacity. -/
theorem positive_inverse_exterior {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (hMV : M ⊆ V) {p : ℕ → ℝ} (hp : RealDual q D M 1 p)
    {k : V} (hk : 0 < maskReal M p k) :
    ∃ z : V, z.val ∈ exterior D V M ∧
      1 < (q : ℝ) * realInW D M p z ∧ 0 < H z k := by
  obtain ⟨z, hz, hc, hh⟩ := positive_source hH (cutCertificate_of_realDual hMV hp) hk
  have hzn : z.val ∉ M := by simpa [hostCut] using hz
  rw [realMatrix_col, realCol, maskReal_inW hMV, maskReal,
    if_neg hzn, zero_add] at hc
  refine ⟨z, ?_, hc, hh⟩
  by_contra hn
  have hzero := coverage_zero_outside p (Finset.mem_sdiff.mpr ⟨z.property, hzn⟩) hn
  rw [hzero, mul_zero] at hc
  norm_num at hc

theorem no_common_inverse_at_row_one {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (w : ℕ → ℚ) (hm : mass V w = 1) (hr : ∀ v ∈ V, row q D V w v = 1) :
    ¬ ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q D V) H := by
  rintro ⟨H, hH⟩
  apply no_commonInverse_at_equality (fun i : V => (w i : ℝ)) _ _ hH
  · have hh : (∑ i : V, w i) = 1 := by rw [Finset.sum_coe_sort]; exact hm
    exact_mod_cast hh
  · intro i
    have he : (rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun j : V => w j)) i = 1 := by
      rw [matrix_row, hr i i.property]
    change (∑ j : V, rationalMatrix q (adjacencyMatrix D V) i j * w j) = (1 : ℚ) at he
    have hh := congrArg (fun x : ℚ => (x : ℝ)) he
    push_cast at hh
    exact hh

end LeanCH.BR.WeightedSD
