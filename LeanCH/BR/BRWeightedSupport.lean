import LeanCH.BR.BRWeightedZeroVertex
import LeanCH.BR.BRWeightedSDBridge

/-! Reduction to strictly positive weights, uniformly in the cutoff.
The positive-weight supplier remains an explicit mathematical premise. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45

def PositiveSelfDual (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ w : ℕ → ℚ, (∀ v ∈ V, 0 < w v) →
    (∀ v ∈ V, mass V w ≤ row q D V w v) →
    ∀ v ∈ V, col q D V w v ≤ mass V w

theorem no_strict_positive_rows {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hP : PositiveSelfDual q D V) (hV : V.Nonempty) (w : ℕ → ℚ)
    (hw : ∀ v ∈ V, 0 < w v) (hr : ∀ v ∈ V, mass V w < row q D V w v) : False := by
  have hc := hP w hw (fun v hv => (hr v hv).le)
  have hlo : (∑ v ∈ V, w v * mass V w) < ∑ v ∈ V, w v * row q D V w v := by
    apply Finset.sum_lt_sum
    · exact fun v hv => (mul_lt_mul_of_pos_left (hr v hv) (hw v hv)).le
    · obtain ⟨v, hv⟩ := hV
      exact ⟨v, hv, mul_lt_mul_of_pos_left (hr v hv) (hw v hv)⟩
  have hhi : (∑ v ∈ V, w v * col q D V w v) ≤ ∑ v ∈ V, w v * mass V w :=
    Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hc v hv) (hw v hv).le)
  rw [row_col_balance] at hlo
  exact (not_lt_of_ge hhi) hlo

theorem mass_subset_zero {U V : Finset ℕ} {w : ℕ → ℚ} (hUV : U ⊆ V)
    (hz : ∀ v ∈ V, v ∉ U → w v = 0) : mass U w = mass V w :=
  Finset.sum_subset hUV hz

theorem outW_subset_zero {D : CH.Digraph} {U V : Finset ℕ} {w : ℕ → ℚ}
    (hUV : U ⊆ V) (hz : ∀ v ∈ V, v ∉ U → w v = 0) (u : ℕ) :
    outW D U w u = outW D V w u := by
  apply Finset.sum_subset hUV
  intro v hv hn
  simp [hz v hv hn]

theorem inW_subset_zero {D : CH.Digraph} {U V : Finset ℕ} {w : ℕ → ℚ}
    (hUV : U ⊆ V) (hz : ∀ v ∈ V, v ∉ U → w v = 0) (u : ℕ) :
    inW D U w u = inW D V w u := by
  apply Finset.sum_subset hUV
  intro v hv hn
  simp [hz v hv hn]

theorem normalized_selfDual_of_positive_and_proper {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hP : PositiveSelfDual q D V)
    (hproper : ∀ M ⊆ V, M ≠ V → SelfDual q D M)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hsum : mass V w = 1)
    (hr : ∀ v ∈ V, 1 ≤ row q D V w v) : ∀ v ∈ V, col q D V w v ≤ 1 := by
  let S := V.filter (fun v => 0 < w v)
  have hSV : S ⊆ V := Finset.filter_subset _ _
  have hzero : ∀ v ∈ V, v ∉ S → w v = 0 := by
    intro v hv hn
    have hnpos : ¬ 0 < w v := fun hp => hn (Finset.mem_filter.mpr ⟨hv, hp⟩)
    exact le_antisymm (le_of_not_gt hnpos) (hw v hv)
  by_cases hSVeq : S = V
  · have hp : ∀ v ∈ V, 0 < w v := by
      intro v hv
      exact (Finset.mem_filter.mp (hSVeq ▸ hv : v ∈ S)).2
    simpa only [hsum] using hP w hp (by simpa only [hsum] using hr)
  intro u hu
  by_contra hn
  have hbad : 1 < col q D V w u := lt_of_not_ge hn
  let U := insert u S
  have hUV : U ⊆ V := Finset.insert_subset hu hSV
  have hzU : ∀ v ∈ V, v ∉ U → w v = 0 := by
    intro v hv hn
    exact hzero v hv (fun h => hn (Finset.mem_insert_of_mem h))
  by_cases hUeq : U = V
  · have huS : u ∉ S := by
      intro h
      have heq : U = S := Finset.insert_eq_of_mem h
      exact hSVeq (heq.symm.trans hUeq)
    have hwu := hzero u hu huS
    have hpos : ∀ v ∈ V.erase u, 0 < w v := by
      intro v hv
      have hvU : v ∈ U := hUeq ▸ (Finset.mem_erase.mp hv).2
      have hvS : v ∈ S := (Finset.mem_insert.mp hvU).resolve_left (Finset.mem_erase.mp hv).1
      exact (Finset.mem_filter.mp hvS).2
    have hproperErase : V.erase u ≠ V := by
      intro heq
      have hh : u ∈ V.erase u := by rw [heq]; exact hu
      exact Finset.notMem_erase u V hh
    have hcore := hproper (V.erase u) (Finset.erase_subset _ _) hproperErase
    have hloop : D u u = false := Bool.eq_false_iff.mpr (loopfree hf (by omega) hu)
    obtain ⟨p, hp, hmass, hrows⟩ :=
      positive_weighting_of_one_zero hq hu hloop hcore w hpos hwu hsum hr hbad
    exact no_strict_positive_rows hP ⟨u, hu⟩ p hp (by simpa only [hmass] using hrows)
  · have hcore := hproper U hUV hUeq
    have hrU : ∀ v ∈ U, mass U w ≤ row q D U w v := by
      intro v hv
      rw [mass_subset_zero hUV hzU, hsum, row, outW_subset_zero hUV hzU]
      exact hr v (hUV hv)
    have hc := hcore w (fun v hv => hw v (hUV hv)) hrU u (Finset.mem_insert_self _ _)
    rw [mass_subset_zero hUV hzU, hsum, col, inW_subset_zero hUV hzU] at hc
    exact (not_lt_of_ge hc) hbad

theorem mass_div (V : Finset ℕ) (w : ℕ → ℚ) (t : ℚ) :
    mass V (fun v => w v / t) = mass V w / t := by
  simp only [mass, div_eq_mul_inv, Finset.sum_mul]

theorem outW_div (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (t : ℚ) (v : ℕ) :
    outW D V (fun u => w u / t) v = outW D V w v / t := by
  simp only [outW, div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]

theorem inW_div (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (t : ℚ) (v : ℕ) :
    inW D V (fun u => w u / t) v = inW D V w v / t := by
  simp only [inW, div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]

theorem row_div (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (t : ℚ) (v : ℕ) :
    row q D V (fun u => w u / t) v = row q D V w v / t := by
  simp only [row, outW_div, add_div, mul_div_assoc]

theorem col_div (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (t : ℚ) (v : ℕ) :
    col q D V (fun u => w u / t) v = col q D V w v / t := by
  simp only [col, inW_div, add_div, mul_div_assoc]

theorem selfDual_of_positive_and_proper {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hP : PositiveSelfDual q D V)
    (hproper : ∀ M ⊆ V, M ≠ V → SelfDual q D M) : SelfDual q D V := by
  intro w hw hr
  by_cases hz : mass V w = 0
  · have hzero := mass_zero_weights hw hz
    intro v hv
    have hi : inW D V w v = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      simp [hzero u hu]
    simp [col, hzero v hv, hi, hz]
  · have hpos : 0 < mass V w := lt_of_le_of_ne (mass_nonneg hw) (Ne.symm hz)
    let z := fun v => w v / mass V w
    have hwz : ∀ v ∈ V, 0 ≤ z v := fun v hv => div_nonneg (hw v hv) hpos.le
    have hsumz : mass V z = 1 := by
      rw [mass_div]
      exact div_self hz
    have hrz : ∀ v ∈ V, 1 ≤ row q D V z v := by
      intro v hv
      rw [row_div]
      exact (le_div_iff₀ hpos).mpr (by simpa using hr v hv)
    have hc := normalized_selfDual_of_positive_and_proper hq hf hP hproper z hwz hsumz hrz
    intro v hv
    have hh := hc v hv
    rw [col_div] at hh
    simpa using (div_le_iff₀ hpos).mp hh

theorem selfDual_one {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 1) :
    SelfDual 1 D V := by
  intro w hw _ v hv
  have hloop : D v v = false := Bool.eq_false_iff.mpr (loopfree hf le_rfl hv)
  have hi : inW D (V.erase v) w v ≤ mass (V.erase v) w := by
    apply Finset.sum_le_sum
    intro u hu
    split_ifs
    · exact le_rfl
    · exact hw u (Finset.mem_erase.mp hu).2
  have hsum := Finset.sum_erase_add V w hv
  change mass (V.erase v) w + w v = mass V w at hsum
  rw [col, inW_erase hv w v, hloop]
  simp only [Bool.false_eq_true, ite_false, add_zero, Nat.cast_one, one_mul]
  linarith

/-- Only the strictly positive weight case is left as a supplier. It must
hold for every cutoff and every finite q-free graph. -/
def AllPositiveSelfDual : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ),
    QFree D V q → PositiveSelfDual q D V

theorem selfDual_of_all_positive_fixed {q : ℕ} (hq : 2 ≤ q)
    (hP : ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → PositiveSelfDual q D V)
    (D : CH.Digraph) (V : Finset ℕ) (hf : QFree D V q) : SelfDual q D V := by
  have main : ∀ n : ℕ, ∀ U : Finset ℕ, U.card = n →
      ∀ E : CH.Digraph, QFree E U q → SelfDual q E U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hcard E hfree
      apply selfDual_of_positive_and_proper hq hfree (hP E U hfree)
      intro M hMU hne
      have hlt : M.card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hMU, hne⟩)
      exact ih M.card hlt M rfl E (hfree.mono_set hMU)
  exact main V.card V rfl D hf

theorem allSelfDual_of_allPositiveSelfDual (h : AllPositiveSelfDual) : AllSelfDual := by
  intro q hq D V hf
  by_cases htwo : 2 ≤ q
  · exact selfDual_of_all_positive_fixed htwo (h q htwo) D V hf
  · have heq : q = 1 := by omega
    subst q
    exact selfDual_one hf

theorem caccettaHaggkvist_of_allPositiveSelfDual (h : AllPositiveSelfDual) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_allSelfDual (allSelfDual_of_allPositiveSelfDual h)

end LeanCH.BR.WeightedSD
