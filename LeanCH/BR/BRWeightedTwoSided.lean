import LeanCH.BR.BRWeightedStrictNormal
import LeanCH.BR.BRWeightedCases

/-! Derive the strict two-sided normal form from proper induced self-duality,
and combine it with the threshold normal form. The final prime structure
statement remains explicit and open. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix WeightedArithmetic BRq2 BRq3 BR45 BRsub
open scoped Matrix

/-- A strict nonnegative weighting cannot have a zero coordinate when every
proper induced host is self-dual. No cycle or saturation premise is needed. -/
theorem strict_weights_positive_of_proper {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
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
    intro heq
    have haS : a ∈ S := heq ▸ ha
    exact hna (Finset.mem_filter.mp haS).2
  have hnS : S.Nonempty := by
    by_contra he
    have hzero : ∀ v ∈ V, w v = 0 := by
      intro v hv
      exact hz v hv (fun h => he ⟨v, h⟩)
    have hm : mass V w = 0 := Finset.sum_eq_zero hzero
    have ho : outW D V w a = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp [hzero v hv]
    have hh := hr a ha
    simp [row, hm, hzero a ha, ho] at hh
  obtain ⟨v, hv, hsmall⟩ := exists_small_row (hproper S hSV hne) hnS w
    (fun v hv => hw v (hSV hv))
  rw [mass_subset_zero hSV hz, row, outW_subset_zero hSV hz] at hsmall
  exact (not_lt_of_ge hsmall) (hr v (hSV hv))

theorem full_deficit_of_proper {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U) :
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
  have hp := strict_weights_positive_of_proper hproper z hz hr
  intro i
  simpa only [z, extendWeight_on] using hp i i.property

theorem strict_pair_of_proper {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U) (hs : StrictPositiveRows q D V) :
    ∃ w p : ℕ → ℚ, ∃ c : ℚ, 1 < c ∧ (∀ v ∈ V, 0 < w v) ∧
      (∀ v ∈ V, 0 < p v) ∧ mass V w = 1 ∧ mass V p = 1 ∧
      (∀ v ∈ V, row q D V w v = c) ∧ (∀ v ∈ V, col q D V p v = c) := by
  obtain ⟨z, hz, hm, hr⟩ := hs
  have hn : V.Nonempty := by
    by_contra h
    have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, mass] at hm
  letI : Nonempty V := ⟨⟨hn.choose, hn.choose_spec⟩⟩
  have hmass : (∑ i : V, z i) = 1 := by rw [Finset.sum_coe_sort]; exact hm
  have hb : ∀ i : V, (∑ j : V, z j) <
      (rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun j : V => z j)) i := by
    intro i
    rw [hmass, matrix_row]
    exact hr i i.property
  obtain ⟨w, p, c, hc, hw, hp, hwm, hpm, hwr, hpc⟩ :=
    WeightedStrictNormal.strict_normal_form (rationalMatrix q (adjacencyMatrix D V))
      (full_deficit_of_proper hproper) (fun i : V => z i) (fun i => (hz i i.property).le) hb
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

/-- Under proper induced self-duality every positive feasible host admits a
two-sided positive probability pair at a common value at least one. -/
theorem two_sided_of_positive_feasible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (z : ℕ → ℚ) (hz : ∀ v ∈ V, 0 < z v) (hm : mass V z = 1)
    (hr : ∀ v ∈ V, 1 ≤ row q D V z v) :
    ∃ w p : ℕ → ℚ, ∃ c : ℚ, 1 ≤ c ∧ (∀ v ∈ V, 0 < w v) ∧
      (∀ v ∈ V, 0 < p v) ∧ mass V w = 1 ∧ mass V p = 1 ∧
      (∀ v ∈ V, row q D V w v = c) ∧ (∀ v ∈ V, col q D V p v = c) := by
  by_cases hs : StrictPositiveRows q D V
  · obtain ⟨w, p, c, hc, hw, hp, hwm, hpm, hwr, hpc⟩ := strict_pair_of_proper hproper hs
    exact ⟨w, p, c, hc.le, hw, hp, hwm, hpm, hwr, hpc⟩
  · obtain ⟨hrz, p, hp, hpm, hpc⟩ := normalized_pair_of_no_strict hq z hz hm hr hs
    exact ⟨z, p, 1, le_rfl, hz, hp, hm, hpm, hrz, hpc⟩

/-- Deleting any vertex in a strict equalized host finds an incoming
witness and forces a lower bound on that vertex's weight. -/
theorem strict_atom_witness {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (w : ℕ → ℚ) {c : ℚ} (hc : 1 < c) (hw : ∀ v ∈ V, 0 < w v)
    (hm : mass V w = 1) (hr : ∀ v ∈ V, row q D V w v = c)
    {a : ℕ} (ha : a ∈ V) (hloop : D a a = false) :
    (∃ v ∈ V.erase a, D v a = true) ∧ c - 1 ≤ ((q : ℚ) - 1) * w a := by
  have hwa : w a ≤ 1 := by
    rw [← hm]
    exact Finset.single_le_sum (fun v hv => (hw v hv).le) ha
  have hn : (V.erase a).Nonempty := by
    by_contra he
    have hall : ∀ v ∈ V, v = a := by
      intro v hv
      by_contra hne
      exact he ⟨v, Finset.mem_erase.mpr ⟨hne, hv⟩⟩
    have ho : outW D V w a = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp [hall v hv, hloop]
    have hh := hr a ha
    rw [row, ho, mul_zero, add_zero] at hh
    linarith
  have hne : V.erase a ≠ V := by
    intro he
    have hh : a ∈ V.erase a := by rw [he]; exact ha
    exact Finset.notMem_erase a V hh
  obtain ⟨v, hv, hs⟩ := exists_small_row
    (hproper (V.erase a) (Finset.erase_subset _ _) hne) hn w
    (fun v hv => (hw v (Finset.mem_erase.mp hv).2).le)
  have hmE := Finset.sum_erase_add V w ha
  change mass (V.erase a) w + w a = mass V w at hmE
  rw [hm] at hmE
  have hg := hr v (Finset.mem_erase.mp hv).2
  rw [row, outW_erase ha] at hg
  unfold row at hs
  have hva : D v a = true := by
    by_contra hn
    simp only [hn, ite_false, add_zero] at hg
    have hp := hw a ha
    linarith
  refine ⟨⟨v, hv, hva⟩, ?_⟩
  simp only [hva, ite_true] at hg
  nlinarith

theorem strict_value_order_bound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (hloop : ∀ v ∈ V, D v v = false)
    (w : ℕ → ℚ) {c : ℚ} (hc : 1 < c) (hw : ∀ v ∈ V, 0 < w v)
    (hm : mass V w = 1) (hr : ∀ v ∈ V, row q D V w v = c) :
    (V.card : ℚ) * (c - 1) ≤ (q : ℚ) - 1 := by
  have h := Finset.sum_le_sum (s := V) (fun a ha =>
    (strict_atom_witness hproper w hc hw hm hr ha (hloop a ha)).2)
  have hm' : (∑ i ∈ V, w i) = 1 := hm
  simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hm', mul_one] using h

/-- The remaining structural statement is about already derived, positive
two-sided pairs. Neither the value bound nor the balance is assumed proved. -/
def PrimeTwoSidedRigidity : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → Sat q D V →
    (∀ U ⊆ V, U ≠ V → SelfDual q D U) →
    (∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M) →
    ∀ (w p : ℕ → ℚ) (c : ℚ), 1 ≤ c →
      (∀ v ∈ V, 0 < w v) → (∀ v ∈ V, 0 < p v) → mass V w = 1 → mass V p = 1 →
      (∀ v ∈ V, row q D V w v = c) → (∀ v ∈ V, col q D V p v = c) →
      c = 1 ∧ ∀ v ∈ V, w v = p v

theorem primeNoStrictRows_of_twoSidedRigidity (h : PrimeTwoSidedRigidity) : PrimeNoStrictRows := by
  intro q hq D V hf hsat hproper hprime hs
  obtain ⟨w, p, c, hc, hw, hp, hwm, hpm, hwr, hpc⟩ := strict_pair_of_proper hproper hs
  have he := (h q hq D V hf hsat hproper hprime w p c hc.le hw hp hwm hpm hwr hpc).1
  exact (ne_of_gt hc) he

theorem primeEqualityBalance_of_twoSidedRigidity (h : PrimeTwoSidedRigidity) :
    PrimeEqualityBalance := by
  intro q hq D V hf hsat hproper hprime w p hw hp hwm hpm hwr hpc
  exact (h q hq D V hf hsat hproper hprime w p 1 le_rfl hw hp hwm hpm hwr hpc).2

theorem caccettaHaggkvist_of_primeTwoSidedRigidity (h : PrimeTwoSidedRigidity) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_two_prime_cases (primeNoStrictRows_of_twoSidedRigidity h)
    (primeEqualityBalance_of_twoSidedRigidity h)

end LeanCH.BR.WeightedSD
