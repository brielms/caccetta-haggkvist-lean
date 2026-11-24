import LeanCH.BR.BRWeightedSD

/-! Self-duality is preserved by arbitrary finite substitutions, including
weightings with zero-mass blocks. This does not assert universal self-duality. -/
namespace LeanCH.BR.WeightedSD
open scoped BigOperators

structure Substitution (D E : CH.Digraph) (V I : Finset ℕ) where
  fiber : ℕ → Finset ℕ
  cover : V = I.biUnion fiber
  nonempty : ∀ i ∈ I, (fiber i).Nonempty
  disjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (fiber i) (fiber j)
  loopless : ∀ i ∈ I, E i i = false
  cross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    ∀ a ∈ fiber i, ∀ b ∈ fiber j, D a b = E i j

namespace Substitution
variable {D E : CH.Digraph} {V I : Finset ℕ} (P : Substitution D E V I)

theorem fiber_subset {i : ℕ} (hi : i ∈ I) : P.fiber i ⊆ V := by
  intro a ha
  rw [P.cover]
  exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩

theorem mass_partition (w : ℕ → ℚ) :
    mass V w = mass I (fun i => mass (P.fiber i) w) := by
  simp only [mass, P.cover]
  exact Finset.sum_biUnion P.disjoint

theorem out_partition (w : ℕ → ℚ) {i a : ℕ} (hi : i ∈ I) (ha : a ∈ P.fiber i) :
    outW D V w a = outW D (P.fiber i) w a + outW E I (fun j => mass (P.fiber j) w) i := by
  conv_lhs => rw [outW, P.cover, Finset.sum_biUnion P.disjoint]
  calc
    _ = ∑ j ∈ I, ((if j = i then outW D (P.fiber i) w a else 0) +
        (if E i j = true then mass (P.fiber j) w else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp only [ite_true, P.loopless i hi, Bool.false_eq_true, ite_false, add_zero]
        rfl
      · have hij : i ≠ j := Ne.symm hji
        simp only [if_neg hji, zero_add]
        have heq : (∑ b ∈ P.fiber j, if D a b = true then w b else 0) =
            ∑ b ∈ P.fiber j, if E i j = true then w b else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [P.cross i hi j hj hij a ha b hb]
        rw [heq]
        by_cases he : E i j = true <;> simp [he, mass]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', hi, ite_true, outW]

def reverse : Substitution (fun a b => D b a) (fun i j => E j i) V I where
  fiber := P.fiber
  cover := P.cover
  nonempty := P.nonempty
  disjoint := P.disjoint
  loopless := P.loopless
  cross := by
    intro i hi j hj hij a ha b hb
    exact P.cross j hj i hi hij.symm b hb a ha

theorem in_partition (w : ℕ → ℚ) {i a : ℕ} (hi : i ∈ I) (ha : a ∈ P.fiber i) :
    inW D V w a = inW D (P.fiber i) w a + inW E I (fun j => mass (P.fiber j) w) i :=
  P.reverse.out_partition w hi ha

theorem row_partition (q : ℕ) (w : ℕ → ℚ) {i a : ℕ} (hi : i ∈ I) (ha : a ∈ P.fiber i) :
    row q D V w a = row q D (P.fiber i) w a +
      q * outW E I (fun j => mass (P.fiber j) w) i := by
  simp only [row, P.out_partition w hi ha]
  ring

theorem col_partition (q : ℕ) (w : ℕ → ℚ) {i a : ℕ} (hi : i ∈ I) (ha : a ∈ P.fiber i) :
    col q D V w a = col q D (P.fiber i) w a +
      q * inW E I (fun j => mass (P.fiber j) w) i := by
  simp only [col, P.in_partition w hi ha]
  ring

/-- The module step in weighted boundary induction, uniform in q and in all
block orders. No premise that the weighting has full support is used. -/
theorem selfDual {q : ℕ} (hquot : SelfDual q E I)
    (hinside : ∀ i ∈ I, SelfDual q D (P.fiber i)) : SelfDual q D V := by
  intro w hw hr
  let t : ℕ → ℚ := fun i => mass (P.fiber i) w
  have hsub : ∀ i ∈ I, ∀ a ∈ P.fiber i, 0 ≤ w a := by
    intro i hi a ha
    exact hw a (P.fiber_subset hi ha)
  have ht : ∀ i ∈ I, 0 ≤ t i := by
    intro i hi
    exact mass_nonneg (hsub i hi)
  have htotal : mass V w = mass I t := P.mass_partition w
  have hrows : ∀ i ∈ I, mass I t ≤ row q E I t i := by
    intro i hi
    obtain ⟨a, ha, hsmall⟩ := exists_small_row (hinside i hi) (P.nonempty i hi) w (hsub i hi)
    have hglobal := hr a (P.fiber_subset hi ha)
    rw [P.row_partition q w hi ha, htotal] at hglobal
    change mass I t ≤ t i + q * outW E I t i
    change row q D (P.fiber i) w a ≤ t i at hsmall
    change mass I t ≤ row q D (P.fiber i) w a + q * outW E I t i at hglobal
    linarith
  have hcols := hquot t ht hrows
  intro a ha
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (P.cover ▸ ha)
  rw [P.col_partition q w hi hai, htotal]
  change col q D (P.fiber i) w a + q * inW E I t i ≤ mass I t
  have hc := hcols i hi
  change t i + q * inW E I t i ≤ mass I t at hc
  by_cases hz : t i = 0
  · have hzero := mass_zero_weights (hsub i hi) hz
    have hin : inW D (P.fiber i) w a = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp [hzero b hb]
    simp only [col, hzero a hai, hin, mul_zero, add_zero, zero_add]
    simpa only [hz, zero_add] using hc
  · have htp : 0 < t i := lt_of_le_of_ne (ht i hi) (Ne.symm hz)
    have heq := positive_row_eq hquot ht hrows hi htp
    change t i + q * outW E I t i = mass I t at heq
    have hir : ∀ b ∈ P.fiber i, mass (P.fiber i) w ≤ row q D (P.fiber i) w b := by
      intro b hb
      have hh := hr b (P.fiber_subset hi hb)
      rw [P.row_partition q w hi hb, htotal] at hh
      change mass I t ≤ row q D (P.fiber i) w b + q * outW E I t i at hh
      change t i ≤ row q D (P.fiber i) w b
      linarith
    have hic := hinside i hi w (hsub i hi) hir a hai
    change col q D (P.fiber i) w a ≤ t i at hic
    linarith

end Substitution
end LeanCH.BR.WeightedSD
