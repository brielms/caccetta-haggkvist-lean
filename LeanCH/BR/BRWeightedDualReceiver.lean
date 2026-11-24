import LeanCH.BR.BRWeightedDualCoverage

/-! An internal universal receiver forces the unit dual to concentrate at
that vertex. If it heads the whole exterior, external coverage loss is zero;
one must retain internal column slack as well. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45

theorem realInW_receiver {D : CH.Digraph} {M : Finset ℕ} {a : ℕ} (ha : a ∈ M)
    (hloop : D a a = false) (hrec : ∀ v ∈ M, v ≠ a → D v a = true) (p : ℕ → ℝ) :
    realInW D M p a = realMass (M.erase a) p := by
  have hs := Finset.sum_erase_add M (fun v => if D v a = true then p v else 0) ha
  have he : (∑ v ∈ M.erase a, if D v a = true then p v else 0) = realMass (M.erase a) p := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [hrec v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1, if_pos rfl]
  rw [he, hloop] at hs
  simpa only [realInW, Bool.false_eq_true, ite_false, add_zero] using hs.symm

theorem receiver_column_floor {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {M : Finset ℕ} {a : ℕ} (ha : a ∈ M) (hloop : D a a = false)
    (hrec : ∀ v ∈ M, v ≠ a → D v a = true) {p : ℕ → ℝ}
    (hp : ∀ v ∈ M, 0 ≤ p v) (hm : realMass M p = 1) : 1 ≤ realCol q D M p a := by
  have hs := Finset.sum_erase_add M p ha
  change realMass (M.erase a) p + p a = realMass M p at hs
  rw [hm] at hs
  have hn : 0 ≤ realMass (M.erase a) p :=
    Finset.sum_nonneg (fun v hv => hp v (Finset.mem_erase.mp hv).2)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [realCol, realInW_receiver ha hloop hrec p]
  nlinarith

theorem receiver_dual_unique {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {M : Finset ℕ} {a : ℕ} (ha : a ∈ M) (hloop : D a a = false)
    (hrec : ∀ v ∈ M, v ≠ a → D v a = true) {p : ℕ → ℝ}
    (hp : RealDual q D M 1 p) : p a = 1 ∧ ∀ v ∈ M, v ≠ a → p v = 0 := by
  have hs := Finset.sum_erase_add M p ha
  change realMass (M.erase a) p + p a = realMass M p at hs
  rw [hp.normalized] at hs
  have hn : 0 ≤ realMass (M.erase a) p :=
    Finset.sum_nonneg (fun v hv => hp.nonneg v (Finset.mem_erase.mp hv).2)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hc := hp.columns a ha
  rw [realCol, realInW_receiver ha hloop hrec p] at hc
  have hz : realMass (M.erase a) p = 0 := by nlinarith
  have heach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v hv => hp.nonneg v (Finset.mem_erase.mp hv).2)).mp hz
  refine ⟨by linarith, ?_⟩
  intro v hv hne
  exact heach v (Finset.mem_erase.mpr ⟨hne, hv⟩)

theorem realInW_of_dirac {D : CH.Digraph} {M : Finset ℕ} {a : ℕ} (ha : a ∈ M)
    {p : ℕ → ℝ} (hpa : p a = 1) (hz : ∀ v ∈ M, v ≠ a → p v = 0) (z : ℕ) :
    realInW D M p z = if D a z = true then 1 else 0 := by
  unfold realInW
  rw [Finset.sum_eq_single a]
  · rw [hpa]
  · intro v hv hne
    simp [hz v hv hne]
  · intro hn
    exact False.elim (hn ha)

theorem receiver_no_exterior_defect {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V M : Finset ℕ} {a : ℕ} (ha : a ∈ M) (hloop : D a a = false)
    (hrec : ∀ v ∈ M, v ≠ a → D v a = true)
    (hcover : ∀ z ∈ exterior D V M, D a z = true) {p : ℕ → ℝ}
    (hp : RealDual q D M 1 p) (w : ℕ → ℝ) : exteriorDefect D V M w p = 0 := by
  obtain ⟨hpa, hz⟩ := receiver_dual_unique hq ha hloop hrec hp
  apply Finset.sum_eq_zero
  intro z he
  rw [realInW_of_dirac ha hpa hz, hcover z he]
  simp

theorem receiver_dual_value_floor {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {M : Finset ℕ} {a : ℕ} (ha : a ∈ M) (hloop : D a a = false)
    (hrec : ∀ v ∈ M, v ≠ a → D v a = true) {alpha : ℝ} {p : ℕ → ℝ}
    (hp : RealDual q D M alpha p) : 1 ≤ alpha :=
  (receiver_column_floor hq ha hloop hrec hp.nonneg hp.normalized).trans (hp.columns a ha)

end LeanCH.BR.WeightedSD
