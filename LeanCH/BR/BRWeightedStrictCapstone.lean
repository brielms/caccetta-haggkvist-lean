import LeanCH.BR.BRWeightedStrictPrime

/-! A strict-only consumer for literal CH, with the additional equality
obligation retained explicitly for boundary regularity. Neither supplier
is asserted to hold. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Compose.Boundary

def AllSmallRow : Prop :=
  ∀ q : ℕ, 0 < q → ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → SmallRow q D V

/-- The unresolved strict structural statement under genuine smaller-order
weighted induction. Equality at value one is not part of this supplier. -/
def StrictPrimeExclusion : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ),
    QFree D V q → Sat q D V → SmallerSmallRow q V.card →
    (∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M) →
    ∀ (w p : ℕ → ℚ) (c : ℚ), 1 < c →
      (∀ v ∈ V, 0 < w v) → (∀ v ∈ V, 0 < p v) → mass V w = 1 → mass V p = 1 →
      (∀ v ∈ V, row q D V w v = c) → (∀ v ∈ V, col q D V p v = c) → False

theorem allSmallRow_of_strictPrimeExclusion (hX : StrictPrimeExclusion) : AllSmallRow := by
  intro q hq
  by_cases hthree : 3 ≤ q
  · have main : ∀ n : ℕ, ∀ V : Finset ℕ, V.card = n →
        ∀ D : CH.Digraph, QFree D V q → SmallRow q D V := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro V hcard D hf
        obtain ⟨E, hDE, hEf, hsat⟩ := exists_satQ hf
        apply smallRow_of_supergraph hDE
        have hsm : SmallerSmallRow q V.card := by
          intro F U hlt hUf
          exact ih U.card (by simpa only [hcard] using hlt) U rfl F hUf
        have hproper := hsm.induced hEf
        by_cases hprime : ∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform E V M
        · intro z hz hV
          by_contra hn
          have hr : ∀ v ∈ V, mass V z < row q E V z v := by
            intro v hv
            exact lt_of_not_ge (fun hs => hn ⟨v, hv, hs⟩)
          obtain ⟨w, p, c, hc, hw, hp, hm, hpm, hwr, hpc⟩ :=
            strict_pair_of_proper_smallRow hproper hV z hz hr
          exact hX q hthree E V hEf hsat hsm hprime w p c hc hw hp hm hpm hwr hpc
        · push Not at hprime
          obtain ⟨M, hMV, hM, hne, hout⟩ := hprime
          exact smallRow_of_proper_module (by omega) hEf hsat hproper hMV hM hne hout
    intro D V hf
    exact main V.card V rfl D hf
  · intro D V hf
    rcases (by omega : q = 1 ∨ q = 2) with rfl | rfl
    · exact smallRow_of_selfDual (selfDual_one hf)
    · exact smallRow_of_selfDual (selfDual_two hf)

/-- Uniform weights turn the all-cutoff small-row bound into the literal
positive-order, positive-degree CH conclusion. No equality supplier occurs. -/
theorem caccettaHaggkvist_of_allSmallRow (h : AllSmallRow) :
    CH.CaccettaHaggkvistConjecture := by
  intro n s G hn hs hloop hdeg
  have hnq : n ≤ CH.ceilDiv n s * s := by
    have hmod := Nat.mod_lt (n + s - 1) hs
    have hdiv := Nat.mod_add_div (n + s - 1) s
    rw [Nat.mul_comm s] at hdiv
    unfold CH.ceilDiv
    omega
  have hq : 0 < CH.ceilDiv n s := by
    by_contra hzero
    have he : CH.ceilDiv n s = 0 := by omega
    rw [he, Nat.zero_mul] at hnq
    omega
  by_contra hno
  have hf := qfree_of_noShort hloop hno
  obtain ⟨v, hv, hrow⟩ := h (CH.ceilDiv n s) hq G (Finset.range n) hf
    (fun _ => 1) (fun _ _ => by norm_num) ⟨0, Finset.mem_range.mpr hn⟩
  have hd : (s : ℚ) ≤ (outN G (Finset.range n) v).card := by
    exact_mod_cast Compose.FloorSix.out_card hdeg (Finset.mem_range.mp hv)
  have hnQ : (n : ℚ) ≤ (CH.ceilDiv n s : ℚ) * s := by exact_mod_cast hnq
  have hm := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (CH.ceilDiv n s) : (0 : ℚ) ≤ _)
  have hrQ : 1 + (CH.ceilDiv n s : ℚ) * (outN G (Finset.range n) v).card ≤ n := by
    simpa only [row, outW_unit, mass, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] using hrow
  linarith

theorem caccettaHaggkvist_of_strictPrimeExclusion (h : StrictPrimeExclusion) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_allSmallRow (allSmallRow_of_strictPrimeExclusion h)

theorem SmallRow.not_strictPositiveRows {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SmallRow q D V) : ¬ StrictPositiveRows q D V := by
  rintro ⟨w, hw, hm, hr⟩
  have hV : V.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, mass] at hm
  exact h.no_strict hV w (fun v hv => (hw v hv).le)
    (fun v hv => by rw [hm]; exact hr v hv)

theorem primeNoStrictRows_of_allSmallRow (h : AllSmallRow) : PrimeNoStrictRows := by
  intro q hq D V hf _ _ _
  exact (h q (by omega) D V hf).not_strictPositiveRows

theorem allSelfDual_of_smallRow_and_balance (h : AllSmallRow) (hB : PrimeEqualityBalance) :
    AllSelfDual :=
  allSelfDual_of_positivePrimeSupplier
    (positivePrimeSupplier_of_two_cases (primeNoStrictRows_of_allSmallRow h) hB)

/-- The full boundary-regularity target retains its separate, unproved
equality-balance obligation even though strict exclusion alone implies CH. -/
theorem boundaryRegular_of_strict_and_balance (hX : StrictPrimeExclusion)
    (hB : PrimeEqualityBalance) {q s : ℕ} (hq : 0 < q) : BoundaryRegular q s :=
  boundaryRegular_of_allSelfDual
    (allSelfDual_of_smallRow_and_balance (allSmallRow_of_strictPrimeExclusion hX) hB) hq

end LeanCH.BR.WeightedSD
