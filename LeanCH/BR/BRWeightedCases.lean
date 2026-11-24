import LeanCH.BR.BRWeightedNormal
import LeanCH.BR.BRWeightedPrime

/-! Exact rational split of the full positive prime supplier into the
strict-row case and equality of the row and column equalizers. Both
mathematical suppliers remain explicit and unproved. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub Matrix WeightedArithmetic WeightedNormal
open scoped Matrix

def extendWeight (V : Finset ℕ) (p : V → ℚ) : ℕ → ℚ :=
  fun v => if hv : v ∈ V then p ⟨v, hv⟩ else 0

theorem extendWeight_on (V : Finset ℕ) (p : V → ℚ) (i : V) : extendWeight V p i = p i := by
  simp [extendWeight, i.property]

theorem mass_extendWeight (V : Finset ℕ) (p : V → ℚ) :
    mass V (extendWeight V p) = ∑ i : V, p i := by
  rw [mass, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun i hi => extendWeight_on V p i)

theorem row_extendWeight (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (p : V → ℚ) (i : V) :
    row q D V (extendWeight V p) i = (rationalMatrix q (adjacencyMatrix D V) *ᵥ p) i := by
  have he : (fun j : V => extendWeight V p j) = p := funext (extendWeight_on V p)
  rw [← matrix_row q D V (extendWeight V p) i, he]

theorem col_extendWeight (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (p : V → ℚ) (i : V) :
    col q D V (extendWeight V p) i = (p ᵥ* rationalMatrix q (adjacencyMatrix D V)) i := by
  have he : (fun j : V => extendWeight V p j) = p := funext (extendWeight_on V p)
  rw [← matrix_col q D V (extendWeight V p) i, he]

def StrictPositiveRows (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ w : ℕ → ℚ, (∀ v ∈ V, 0 < w v) ∧ mass V w = 1 ∧ ∀ v ∈ V, 1 < row q D V w v

theorem strict_graph_of_matrix {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : StrictProbability (rationalMatrix q (adjacencyMatrix D V))) : StrictPositiveRows q D V := by
  obtain ⟨p, hp, hm, hr⟩ := h
  refine ⟨extendWeight V p, ?_, ?_, ?_⟩
  · intro v hv
    simpa only [extendWeight_on V p ⟨v, hv⟩] using hp ⟨v, hv⟩
  · rw [mass_extendWeight]; exact hm
  · intro v hv
    rw [row_extendWeight q D V p ⟨v, hv⟩]
    exact hr ⟨v, hv⟩

/-- The two-sided equality structure is derived from absence of strict
counterweights. No q-free or smaller-instance premise is needed for this
algebraic theorem, and no equality between the two weights is asserted. -/
theorem normalized_pair_of_no_strict {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (w : ℕ → ℚ)
    (hw : ∀ v ∈ V, 0 < w v) (hm : mass V w = 1)
    (hr : ∀ v ∈ V, 1 ≤ row q D V w v) (hno : ¬ StrictPositiveRows q D V) :
    (∀ v ∈ V, row q D V w v = 1) ∧
      ∃ p : ℕ → ℚ, (∀ v ∈ V, 0 < p v) ∧ mass V p = 1 ∧
        ∀ v ∈ V, col q D V p v = 1 := by
  have hm' : (∑ i : V, w i) = 1 := by rw [Finset.sum_coe_sort]; exact hm
  have hr' : ∀ i : V, 1 ≤ (rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun j : V => w j)) i := by
    intro i
    rw [matrix_row]
    exact hr i i.property
  have hn' : ¬ StrictProbability (rationalMatrix q (adjacencyMatrix D V)) :=
    fun h => hno (strict_graph_of_matrix h)
  obtain ⟨heq, p, hp, hsum, hc⟩ := equalized_of_no_strict hq (adjacencyMatrix D V)
    (fun i : V => w i) (fun i => hw i i.property) hm' hr' hn'
  refine ⟨?_, extendWeight V p, ?_, ?_, ?_⟩
  · intro v hv
    exact (matrix_row q D V w ⟨v, hv⟩).symm.trans (heq ⟨v, hv⟩)
  · intro v hv
    simpa only [extendWeight_on V p ⟨v, hv⟩] using hp ⟨v, hv⟩
  · rw [mass_extendWeight]; exact hsum
  · intro v hv
    rw [col_extendWeight q D V p ⟨v, hv⟩, hc]

theorem column_equalizer_unique_on {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {p r : ℕ → ℚ}
    (hp : ∀ v ∈ V, col q D V p v = 1) (hr : ∀ v ∈ V, col q D V r v = 1) :
    ∀ v ∈ V, p v = r v := by
  have hpM : (fun i : V => p i) ᵥ* rationalMatrix q (adjacencyMatrix D V) = fun _ => 1 := by
    funext i
    exact (matrix_col q D V p i).trans (hp i i.property)
  have hrM : (fun i : V => r i) ᵥ* rationalMatrix q (adjacencyMatrix D V) = fun _ => 1 := by
    funext i
    exact (matrix_col q D V r i).trans (hr i i.property)
  have heq := column_equalizer_unique hq (adjacencyMatrix D V) hpM hrM
  intro v hv
  exact congrFun heq ⟨v, hv⟩

theorem positive_feasible_cases {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (w : ℕ → ℚ)
    (hw : ∀ v ∈ V, 0 < w v) (hm : mass V w = 1)
    (hr : ∀ v ∈ V, 1 ≤ row q D V w v) :
    StrictPositiveRows q D V ∨
      ((∀ v ∈ V, row q D V w v = 1) ∧
        ∃ p : ℕ → ℚ, (∀ v ∈ V, 0 < p v) ∧ mass V p = 1 ∧
          ∀ v ∈ V, col q D V p v = 1) := by
  by_cases hs : StrictPositiveRows q D V
  · exact Or.inl hs
  · exact Or.inr (normalized_pair_of_no_strict hq w hw hm hr hs)

/-- An actual positive column violation falls into one of the two cases
on the SAME graph. In the equality case its positive column equalizer must
differ from the row weighting somewhere on the host. -/
theorem positive_violation_cases {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (w : ℕ → ℚ)
    (hw : ∀ v ∈ V, 0 < w v) (hm : mass V w = 1)
    (hr : ∀ v ∈ V, 1 ≤ row q D V w v) {u : ℕ} (hu : u ∈ V)
    (hbad : 1 < col q D V w u) :
    StrictPositiveRows q D V ∨
      ((∀ v ∈ V, row q D V w v = 1) ∧
        ∃ p : ℕ → ℚ, (∀ v ∈ V, 0 < p v) ∧ mass V p = 1 ∧
          (∀ v ∈ V, col q D V p v = 1) ∧ ¬ (∀ v ∈ V, w v = p v)) := by
  rcases positive_feasible_cases hq w hw hm hr with hs | ⟨heq, p, hp, hpm, hpc⟩
  · exact Or.inl hs
  · refine Or.inr ⟨heq, p, hp, hpm, hpc, ?_⟩
    intro hsame
    have hc : col q D V w u = col q D V p u := by
      unfold col inW
      rw [hsame u hu]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [hsame v hv]
    rw [hc, hpc u hu] at hbad
    exact (lt_irrefl 1) hbad

theorem positiveSelfDual_of_two_cases {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hno : ¬ StrictPositiveRows q D V)
    (hbalance : ∀ (w p : ℕ → ℚ), (∀ v ∈ V, 0 < w v) → (∀ v ∈ V, 0 < p v) →
      mass V w = 1 → mass V p = 1 → (∀ v ∈ V, row q D V w v = 1) →
      (∀ v ∈ V, col q D V p v = 1) → ∀ v ∈ V, w v = p v) : PositiveSelfDual q D V := by
  intro w hw hr v hv
  have hpos : 0 < mass V w := by
    apply Finset.sum_pos'
    · exact fun u hu => (hw u hu).le
    · exact ⟨v, hv, hw v hv⟩
  let z : ℕ → ℚ := fun u => w u / mass V w
  have hz : ∀ u ∈ V, 0 < z u := fun u hu => div_pos (hw u hu) hpos
  have hzm : mass V z = 1 := by rw [mass_div]; exact div_self (ne_of_gt hpos)
  have hzr : ∀ u ∈ V, 1 ≤ row q D V z u := by
    intro u hu
    rw [row_div]
    exact (le_div_iff₀ hpos).mpr (by simpa using hr u hu)
  obtain ⟨hzeq, p, hp, hpm, hpc⟩ := normalized_pair_of_no_strict hq z hz hzm hzr hno
  have hzp := hbalance z p hz hp hzm hpm hzeq hpc
  have hc : col q D V z v = col q D V p v := by
    unfold col inW
    rw [hzp v hv]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [hzp u hu]
  rw [hpc v hv, col_div] at hc
  have hle : col q D V w v / mass V w ≤ 1 := hc.le
  simpa using (div_le_iff₀ hpos).mp hle

def PrimeNoStrictRows : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → Sat q D V →
    (∀ U ⊆ V, U ≠ V → SelfDual q D U) →
    (∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M) → ¬ StrictPositiveRows q D V

def PrimeEqualityBalance : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → Sat q D V →
    (∀ U ⊆ V, U ≠ V → SelfDual q D U) →
    (∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M) →
    ∀ (w p : ℕ → ℚ), (∀ v ∈ V, 0 < w v) → (∀ v ∈ V, 0 < p v) →
      mass V w = 1 → mass V p = 1 → (∀ v ∈ V, row q D V w v = 1) →
      (∀ v ∈ V, col q D V p v = 1) → ∀ v ∈ V, w v = p v

theorem positivePrimeSupplier_of_two_cases (hA : PrimeNoStrictRows) (hB : PrimeEqualityBalance) :
    PositivePrimeSupplier := by
  intro q hq D V hf hsat hproper hprime
  exact positiveSelfDual_of_two_cases (by omega)
    (hA q hq D V hf hsat hproper hprime) (hB q hq D V hf hsat hproper hprime)

theorem caccettaHaggkvist_of_two_prime_cases (hA : PrimeNoStrictRows) (hB : PrimeEqualityBalance) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_positivePrimeSupplier (positivePrimeSupplier_of_two_cases hA hB)

end LeanCH.BR.WeightedSD
