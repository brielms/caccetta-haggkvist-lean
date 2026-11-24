import LeanCH.BR.BRWeightedSD
import LeanCH.BR.BROutModule

/-! A tight weighted exterior cut is an out-module under internal self-duality.
The existence of such a nontrivial cut is not asserted. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub

def exterior (D : CH.Digraph) (V M : Finset ℕ) : Finset ℕ :=
  (M.biUnion (fun x => outN D V x)) \ M

theorem exterior_subset (D : CH.Digraph) (V M : Finset ℕ) : exterior D V M ⊆ V := by
  intro y hy
  obtain ⟨hy, _⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hy
  exact (mem_outN.mp hxy).1

theorem exterior_row_subset {D : CH.Digraph} {V M : Finset ℕ} {x : ℕ} (hx : x ∈ M) :
    outN D (V \ M) x ⊆ exterior D V M := by
  intro y hy
  obtain ⟨hyVM, hxy⟩ := mem_outN.mp hy
  obtain ⟨hyV, hyM⟩ := Finset.mem_sdiff.mp hyVM
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_biUnion.mpr ⟨x, hx, mem_outN.mpr ⟨hyV, hxy⟩⟩, hyM⟩

theorem mass_mono {A B : Finset ℕ} {w : ℕ → ℚ} (hAB : A ⊆ B)
    (hw : ∀ x ∈ B, 0 ≤ w x) : mass A w ≤ mass B w :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x hx _ => hw x hx)

theorem outW_eq_mass (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (x : ℕ) :
    outW D V w x = mass (outN D V x) w := by
  simp only [outW, mass, outN, Finset.sum_filter]

theorem outW_split {D : CH.Digraph} {V M : Finset ℕ} (hMV : M ⊆ V)
    (w : ℕ → ℚ) (x : ℕ) : outW D V w x = outW D M w x + outW D (V \ M) w x := by
  exact (Finset.sum_sdiff hMV).symm.trans (add_comm _ _)

theorem positive_mass_eq_subset {A B : Finset ℕ} {w : ℕ → ℚ}
    (hAB : A ⊆ B) (hw : ∀ x ∈ B, 0 < w x) (heq : mass A w = mass B w) : A = B := by
  apply Finset.Subset.antisymm hAB
  intro b hb
  by_contra hbA
  have hins : insert b A ⊆ B := Finset.insert_subset hb hAB
  have hle := mass_mono hins (fun x hx => (hw x hx).le)
  change (∑ x ∈ insert b A, w x) ≤ mass B w at hle
  rw [Finset.sum_insert hbA] at hle
  change w b + mass A w ≤ mass B w at hle
  rw [heq] at hle
  have hp := hw b hb
  linarith

/-- Every vertex of a tight cut has the whole exterior as its external row.
All weights on the host are strictly positive; internal self-duality is an
explicit induction premise. The global rows only need a lower bound. -/
theorem tight_cut_exterior_rows {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} (hMV : M ⊆ V) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    (hcut : mass M w + q * mass (exterior D V M) w ≤ mass V w) :
    ∀ x ∈ M, outN D (V \ M) x = exterior D V M := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hwM : ∀ x ∈ M, 0 ≤ w x := fun x hx => (hw x (hMV hx)).le
  have hsplit : ∀ x, row q D V w x = row q D M w x + q * outW D (V \ M) w x := by
    intro x
    simp only [row, outW_split hMV w x]
    ring
  have hext : ∀ x ∈ M, outW D (V \ M) w x ≤ mass (exterior D V M) w := by
    intro x hx
    rw [outW_eq_mass]
    exact mass_mono (exterior_row_subset hx) (fun y hy => (hw y (exterior_subset D V M hy)).le)
  have hir : ∀ x ∈ M, mass M w ≤ row q D M w x := by
    intro x hx
    have hglobal := hr x (hMV hx)
    rw [hsplit] at hglobal
    have he := hext x hx
    nlinarith
  intro x hx
  have hint := positive_row_eq hSD hwM hir hx (hw x (hMV hx))
  have hglobal := hr x (hMV hx)
  rw [hsplit, hint] at hglobal
  have he := hext x hx
  have heq : outW D (V \ M) w x = mass (exterior D V M) w := by nlinarith
  rw [outW_eq_mass] at heq
  exact positive_mass_eq_subset (exterior_row_subset hx)
    (fun y hy => hw y (exterior_subset D V M hy)) heq

theorem outUniform_of_tight_cut {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} (hMV : M ⊆ V) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    (hcut : mass M w + q * mass (exterior D V M) w ≤ mass V w) : OutUniform D V M := by
  have heq := tight_cut_exterior_rows hq hMV hSD hw hr hcut
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

/-- The resulting cut is a full module when the ambient graph is saturated. -/
theorem full_module_of_tight_cut {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hSD : SelfDual q D M)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    (hcut : mass M w + q * mass (exterior D V M) w ≤ mass V w) :
    OutUniform D V M ∧ InUniform D V M := by
  have hout := outUniform_of_tight_cut hq hMV hSD hw hr hcut
  exact ⟨hout, outUniform_inUniform hf hsat hMV hout⟩

/-- In an out-module-free instance satisfying smaller-instance self-duality,
every nontrivial proper cut has strict surplus. This locates the obstruction
to a tight-cut induction: the required cut cannot simply be assumed. -/
theorem strict_cut_of_no_outModule {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V : Finset ℕ} {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    (hproper : ∀ M ⊆ V, M ≠ V → SelfDual q D M)
    (hprime : ∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M)
    {M : Finset ℕ} (hMV : M ⊆ V) (hM : 2 ≤ M.card) (hne : M ≠ V) :
    mass V w < mass M w + q * mass (exterior D V M) w := by
  by_contra hn
  have hcut := le_of_not_gt hn
  exact hprime M hMV hM hne
    (outUniform_of_tight_cut hq hMV (hproper M hMV hne) hw hr hcut)

end LeanCH.BR.WeightedSD
