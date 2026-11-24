import LeanCH.BR.BRWeightedCutInverse

/-! The strict induction requires small rows on smaller hosts, not full
self-duality there. Empty hosts are handled without a spurious witness. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix WeightedArithmetic
open scoped Matrix

def SmallRow (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ w : ℕ → ℚ, (∀ v ∈ V, 0 ≤ w v) → V.Nonempty →
    ∃ v ∈ V, row q D V w v ≤ mass V w

theorem smallRow_of_selfDual {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SelfDual q D V) : SmallRow q D V := by
  intro w hw hV
  exact exists_small_row h hV w hw

theorem SmallRow.no_strict {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SmallRow q D V) (hV : V.Nonempty) (w : ℕ → ℚ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hr : ∀ v ∈ V, mass V w < row q D V w v) : False := by
  obtain ⟨v, hv, hs⟩ := h w hw hV
  exact (not_lt_of_ge hs) (hr v hv)

theorem strict_positive_of_proper_smallRow {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v) : ∀ v ∈ V, 0 < w v := by
  intro a ha
  by_contra hna
  let S := V.filter (fun v => 0 < w v)
  have hSV : S ⊆ V := Finset.filter_subset _ _
  have hz : ∀ v ∈ V, v ∉ S → w v = 0 := by
    intro v hv hn
    have hnp : ¬ 0 < w v := fun hp => hn (Finset.mem_filter.mpr ⟨hv, hp⟩)
    exact le_antisymm (le_of_not_gt hnp) (hw v hv)
  have hne : S ≠ V := by
    intro he
    have hh : a ∈ S := he ▸ ha
    exact hna (Finset.mem_filter.mp hh).2
  have hnS : S.Nonempty := by
    by_contra he
    have hzero : ∀ v ∈ V, w v = 0 := fun v hv => hz v hv (fun h => he ⟨v, h⟩)
    have hm : mass V w = 0 := Finset.sum_eq_zero hzero
    have ho : outW D V w a = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp [hzero v hv]
    have hh := hr a ha
    simp [row, hm, hzero a ha, ho] at hh
  obtain ⟨v, hv, hs⟩ := hproper S hSV hne w (fun v hv => hw v (hSV hv)) hnS
  rw [mass_subset_zero hSV hz, row, outW_subset_zero hSV hz] at hs
  exact (not_lt_of_ge hs) (hr v (hSV hv))

theorem full_deficit_of_proper_smallRow {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U) :
    WeightedStrictNormal.Full (WeightedStrictNormal.deficit
      (rationalMatrix q (adjacencyMatrix D V))) := by
  intro w hw hb
  let z := extendWeight V w
  have hz : ∀ v ∈ V, 0 ≤ z v := by
    intro v hv
    simpa only [z, extendWeight_on V w ⟨v, hv⟩] using hw ⟨v, hv⟩
  have hr : ∀ v ∈ V, mass V z < row q D V z v := by
    intro v hv
    have hi := hb ⟨v, hv⟩
    rw [WeightedStrictNormal.deficit_mulVec] at hi
    change mass V (extendWeight V w) < row q D V (extendWeight V w) v
    rw [mass_extendWeight, row_extendWeight q D V w ⟨v, hv⟩]
    linarith
  have hp := strict_positive_of_proper_smallRow hproper z hz hr
  intro i
  simpa only [z, extendWeight_on] using hp i i.property

theorem realDual_of_smallRow {q : ℕ} {D : CH.Digraph} {M : Finset ℕ}
    (h : SmallRow q D M) (hM : M.Nonempty) : ∃ p, RealDual q D M 1 p := by
  letI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  let R := rationalMatrix q (adjacencyMatrix D M)
  have good : ∀ w : M → ℚ, (∀ v, 0 ≤ w v) →
      ∃ v : M, (∑ u : M, R v u * w u) ≤ ∑ u : M, w u := by
    intro w hw
    have hn : ∀ v ∈ M, 0 ≤ extendWeight M w v := by
      intro v hv
      simpa only [extendWeight_on M w ⟨v, hv⟩] using hw ⟨v, hv⟩
    obtain ⟨v, hv, hs⟩ := h (extendWeight M w) hn hM
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [row_extendWeight q D M w ⟨v, hv⟩, mass_extendWeight] at hs
    exact hs
  obtain ⟨p, hp, hm, hc⟩ := FiniteDual.dual_of_rational_small R good
  refine ⟨realExtendWeight M p, ?_, ?_, ?_⟩
  · intro v hv
    simpa only [realExtendWeight_on M p ⟨v, hv⟩] using hp ⟨v, hv⟩
  · rw [realMass_extendWeight]; exact hm
  · intro v hv
    rw [realCol_extendWeight q D M p ⟨v, hv⟩]
    exact hc ⟨v, hv⟩

theorem smallRow_of_realDual {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {p : ℕ → ℝ} (hp : RealDual q D V 1 p) : SmallRow q D V := by
  intro w hw _
  by_contra hn
  have hr : ∀ v ∈ V, (mass V w : ℝ) < realRow q D V (fun u => (w u : ℝ)) v := by
    intro v hv
    rw [realRow_rat]
    have hh : mass V w < row q D V w v := lt_of_not_ge (fun he => hn ⟨v, hv, he⟩)
    exact_mod_cast hh
  have hpos : ∃ v ∈ V, 0 < p v := by
    by_contra hh
    push Not at hh
    have hs := Finset.sum_nonpos hh
    change realMass V p ≤ 0 at hs
    rw [hp.normalized] at hs
    norm_num at hs
  obtain ⟨a, ha, hpa⟩ := hpos
  have hlo := Finset.sum_lt_sum (s := V)
    (fun v hv => mul_le_mul_of_nonneg_left (hr v hv).le (hp.nonneg v hv))
    ⟨a, ha, mul_lt_mul_of_pos_left (hr a ha) hpa⟩
  rw [← Finset.sum_mul] at hlo
  change realMass V p * (mass V w : ℝ) < _ at hlo
  rw [hp.normalized, one_mul, real_cross_rows] at hlo
  have hwR : ∀ v ∈ V, (0 : ℝ) ≤ (w v : ℝ) := by
    intro v hv
    exact_mod_cast hw v hv
  have hhi := Finset.sum_le_sum (s := V) (fun v hv =>
    mul_le_mul_of_nonneg_left (hp.columns v hv) (hwR v hv))
  simp only [mul_one] at hhi
  change _ ≤ realMass V (fun v => (w v : ℝ)) at hhi
  rw [realMass_rat] at hhi
  exact (not_lt_of_ge hhi) hlo

theorem smallRow_iff_realDual {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hV : V.Nonempty) : SmallRow q D V ↔ ∃ p, RealDual q D V 1 p :=
  ⟨fun h => realDual_of_smallRow h hV, fun ⟨_, hp⟩ => smallRow_of_realDual hp⟩

theorem strict_pair_of_proper_smallRow {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U) (hV : V.Nonempty)
    (z : ℕ → ℚ) (hz : ∀ v ∈ V, 0 ≤ z v)
    (hr : ∀ v ∈ V, mass V z < row q D V z v) :
    ∃ w p : ℕ → ℚ, ∃ c : ℚ, 1 < c ∧ (∀ v ∈ V, 0 < w v) ∧
      (∀ v ∈ V, 0 < p v) ∧ mass V w = 1 ∧ mass V p = 1 ∧
      (∀ v ∈ V, row q D V w v = c) ∧ (∀ v ∈ V, col q D V p v = c) := by
  letI : Nonempty V := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  have hb : ∀ i : V, (∑ j : V, z j) <
      (rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun j : V => z j)) i := by
    intro i
    rw [Finset.sum_coe_sort, matrix_row]
    exact hr i i.property
  obtain ⟨w, p, c, hc, hw, hp, hwm, hpm, hwr, hpc⟩ :=
    WeightedStrictNormal.strict_normal_form (rationalMatrix q (adjacencyMatrix D V))
      (full_deficit_of_proper_smallRow hproper) (fun i : V => z i) (fun i => hz i i.property) hb
  refine ⟨extendWeight V w, extendWeight V p, c, hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simpa only [extendWeight_on V w ⟨v, hv⟩] using hw ⟨v, hv⟩
  · intro v hv
    simpa only [extendWeight_on V p ⟨v, hv⟩] using hp ⟨v, hv⟩
  · rw [mass_extendWeight]; exact hwm
  · rw [mass_extendWeight]; exact hpm
  · intro v hv
    rw [row_extendWeight q D V w ⟨v, hv⟩]
    exact hwr ⟨v, hv⟩
  · intro v hv
    rw [col_extendWeight q D V p ⟨v, hv⟩]
    exact hpc ⟨v, hv⟩

theorem strict_inverse_of_proper_smallRow {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v) :
    ∃ H : Matrix V V ℝ, FiniteCutInverse.CommonInverse (realMatrix q D V) H := by
  have hb : ∀ i : V, (WeightedStrictNormal.deficit
      (rationalMatrix q (adjacencyMatrix D V)) *ᵥ (fun j : V => w j)) i < 0 := by
    intro i
    rw [WeightedStrictNormal.deficit_mulVec, Finset.sum_coe_sort, matrix_row]
    exact sub_neg.mpr (hr i i.property)
  exact FiniteCutInverse.commonInverse_of_strict _ (full_deficit_of_proper_smallRow hproper)
    (fun i : V => w i) (fun i => hw i i.property) hb

theorem all_cut_certificates_of_proper_smallRow {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v) :
    ∃ H : Matrix V V ℝ, FiniteCutInverse.CommonInverse (realMatrix q D V) H ∧
      ∀ M ⊆ V, M.Nonempty → M ≠ V →
        ∃ p : V → ℝ, FiniteCutInverse.CutCertificate (realMatrix q D V) (hostCut V M) p := by
  obtain ⟨H, hH⟩ := strict_inverse_of_proper_smallRow hproper w hw hr
  refine ⟨H, hH, ?_⟩
  intro M hMV hM hne
  obtain ⟨p, hp⟩ := realDual_of_smallRow (hproper M hMV hne) hM
  exact ⟨_, cutCertificate_of_realDual hMV hp⟩

end LeanCH.BR.WeightedSD
