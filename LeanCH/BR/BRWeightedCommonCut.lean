import LeanCH.BR.BRWeightedTwoSided

/-! Weighted cut and ball inequalities at an arbitrary common row lower
bound c. The existence of a nontrivial tight cut is not asserted. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub

theorem row_cut_split {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (w : ℕ → ℚ) (x : ℕ) :
    row q D V w x = row q D M w x + q * outW D (V \ M) w x := by
  simp only [row, outW_split hMV w x]
  ring

theorem exterior_weight_bound {D : CH.Digraph} {V M : Finset ℕ} {w : ℕ → ℚ}
    (hw : ∀ v ∈ V, 0 ≤ w v) {x : ℕ} (hx : x ∈ M) :
    outW D (V \ M) w x ≤ mass (exterior D V M) w := by
  rw [outW_eq_mass]
  exact mass_mono (exterior_row_subset hx) (fun y hy => hw y (exterior_subset D V M hy))

theorem cut_lower_bound_at_value {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.Nonempty) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v) :
    c ≤ mass M w + q * mass (exterior D V M) w := by
  obtain ⟨x, hx, hs⟩ := exists_small_row hSD hM w (fun v hv => hw v (hMV hv))
  have hg := hr x (hMV hx)
  rw [row_cut_split hMV] at hg
  have he := exterior_weight_bound (D := D) hw hx
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  nlinarith

theorem tight_cut_rows_at_value {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} (hMV : M ⊆ V) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v)
    (hcut : mass M w + q * mass (exterior D V M) w ≤ c) :
    ∀ x ∈ M, outN D (V \ M) x = exterior D V M := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hwM : ∀ x ∈ M, 0 ≤ w x := fun x hx => (hw x (hMV hx)).le
  have hir : ∀ x ∈ M, mass M w ≤ row q D M w x := by
    intro x hx
    have hg := hr x (hMV hx)
    rw [row_cut_split hMV] at hg
    have he := exterior_weight_bound (D := D) (fun v hv => (hw v hv).le) hx
    nlinarith
  intro x hx
  have hint := positive_row_eq hSD hwM hir hx (hw x (hMV hx))
  have hg := hr x (hMV hx)
  rw [row_cut_split hMV, hint] at hg
  have he := exterior_weight_bound (D := D) (fun v hv => (hw v hv).le) hx
  have heq : outW D (V \ M) w x = mass (exterior D V M) w := by nlinarith
  rw [outW_eq_mass] at heq
  exact positive_mass_eq_subset (exterior_row_subset hx)
    (fun y hy => hw y (exterior_subset D V M hy)) heq

theorem outUniform_of_tight_cut_at_value {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} (hMV : M ⊆ V) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v)
    (hcut : mass M w + q * mass (exterior D V M) w ≤ c) : OutUniform D V M := by
  have heq := tight_cut_rows_at_value hq hMV hSD hw hr hcut
  intro x hx y hy z hzV hzM
  apply Bool.eq_iff_iff.mpr
  have hz : z ∈ V \ M := Finset.mem_sdiff.mpr ⟨hzV, hzM⟩
  constructor
  · intro hxz
    have hm : z ∈ outN D (V \ M) x := mem_outN.mpr ⟨hz, hxz⟩
    rw [heq x hx, ← heq y hy] at hm
    exact (mem_outN.mp hm).2
  · intro hyz
    have hm : z ∈ outN D (V \ M) y := mem_outN.mpr ⟨hz, hyz⟩
    rw [heq y hy, ← heq x hx] at hm
    exact (mem_outN.mp hm).2

theorem full_module_of_tight_cut_at_value {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v)
    (hcut : mass M w + q * mass (exterior D V M) w ≤ c) :
    OutUniform D V M ∧ InUniform D V M := by
  have hout := outUniform_of_tight_cut_at_value hq hMV hSD hw hr hcut
  exact ⟨hout, outUniform_inUniform hf hsat hMV hout⟩

theorem strict_cut_at_value {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V : Finset ℕ} {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v)
    (hproper : ∀ M ⊆ V, M ≠ V → SelfDual q D M)
    (hprime : ∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M)
    {M : Finset ℕ} (hMV : M ⊆ V) (hM : 2 ≤ M.card) (hne : M ≠ V) :
    c < mass M w + q * mass (exterior D V M) w := by
  by_contra hn
  exact hprime M hMV hM hne
    (outUniform_of_tight_cut_at_value hq hMV (hproper M hMV hne) hw hr (le_of_not_gt hn))

theorem exterior_ball_eq {D : CH.Digraph} {V : Finset ℕ} {u k : ℕ} (hu : u ∈ V) :
    exterior D V (ball D V u k) = ball D V u (k + 1) \ ball D V u k := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzB, hzN⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨x, hx, hxz⟩ := Finset.mem_biUnion.mp hzB
    exact Finset.mem_sdiff.mpr
      ⟨ball_step hx (mem_outN.mp hxz).1 (mem_outN.mp hxz).2, hzN⟩
  · intro hz
    obtain ⟨hzS, hzN⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨x, hx, hxz⟩ := ball_succ_pred hu hzS hzN
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_biUnion.mpr ⟨x, hx, mem_outN.mpr ⟨ball_subset hzS, hxz⟩⟩, hzN⟩

theorem ball_mass_split {D : CH.Digraph} {V : Finset ℕ} {u k : ℕ}
    (hu : u ∈ V) (w : ℕ → ℚ) :
    mass (exterior D V (ball D V u k)) w + mass (ball D V u k) w =
      mass (ball D V u (k + 1)) w := by
  rw [exterior_ball_eq hu]
  exact Finset.sum_sdiff (ball_mono_radius (by omega))

theorem ball_mass_step {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {u k : ℕ}
    (hu : u ∈ V) (hSD : SelfDual q D (ball D V u k))
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v) :
    c + ((q : ℚ) - 1) * mass (ball D V u k) w ≤
      q * mass (ball D V u (k + 1)) w := by
  have h := cut_lower_bound_at_value ball_subset ⟨u, self_mem_ball hu⟩ hSD hw hr
  have hs := ball_mass_split (D := D) (k := k) hu w
  nlinarith

theorem strict_ball_mass_step {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V : Finset ℕ} {u k : ℕ} (hu : u ∈ V)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v) {c : ℚ}
    (hr : ∀ v ∈ V, c ≤ row q D V w v)
    (hproper : ∀ M ⊆ V, M ≠ V → SelfDual q D M)
    (hprime : ∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M)
    (hcard : 2 ≤ (ball D V u k).card) (hne : ball D V u k ≠ V) :
    c + ((q : ℚ) - 1) * mass (ball D V u k) w <
      q * mass (ball D V u (k + 1)) w := by
  have h := strict_cut_at_value hq hw hr hproper hprime ball_subset hcard hne
  have hs := ball_mass_split (D := D) (k := k) hu w
  nlinarith

end LeanCH.BR.WeightedSD
