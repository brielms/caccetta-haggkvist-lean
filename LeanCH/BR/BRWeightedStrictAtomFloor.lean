import LeanCH.BR.BRWeightedPositiveParentTransfer

/-! Strict atom floor from the actual deleted positive support. Only local
absence of digons at the deleted vertex is needed geometrically. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem strict_atom_floor_of_support_smallRow {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} (hv : v ∈ V)
    (hno2 : ∀ z ∈ V, D v z = true → ¬ D z v = true)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (hsmall : SmallRow q D ((V.erase v).filter (fun z => 0 < a z)))
    (c : ℚ) (hc : mass V a < c) (hr : ∀ z ∈ V, c ≤ row q D V a z) :
    c - mass V a < ((q : ℚ) - 1) * a v := by
  by_contra hn
  have hfloor : ((q : ℚ) - 1) * a v ≤ c - mass V a := le_of_not_gt hn
  have hmass : mass (V.erase v) a + a v = mass V a := sum_erase_add _ _ hv
  have hrows : ∀ x, row q D V a x = row q D (V.erase v) a x +
      q * (if D x v = true then a v else 0) := by
    intro x
    rw [row, row, outW_erase hv a x]
    ring
  have hfeas : ∀ x ∈ V.erase v, mass (V.erase v) a ≤ row q D (V.erase v) a x := by
    intro x hx
    have hrow := hr x (mem_erase.mp hx).2
    rw [hrows] at hrow
    split_ifs at hrow <;> nlinarith [ha v hv]
  have hav : a v ≤ mass V a := single_le_sum ha hv
  have hout : 0 < outW D V a v := by
    have hrow := hr v hv
    unfold row at hrow
    have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  rw [outW_eq_mass] at hout
  obtain ⟨z, hz, hpos⟩ := (sum_pos_iff_of_nonneg (fun z hz => ha z (outN_subset hz))).mp hout
  obtain ⟨hzV, hvz⟩ := mem_outN.mp hz
  have hnot := hno2 z hzV hvz
  have hzK : z ∈ V.erase v := by
    refine mem_erase.mpr ⟨?_, hzV⟩
    intro he; subst z
    exact hnot hvz
  have he := positive_coordinate_tight_of_support_smallRow hq a
    (fun x hx => ha x (mem_erase.mp hx).2) hsmall hfeas hzK hpos
  have hrow := hr z hzV
  rw [hrows, if_neg hnot, mul_zero, add_zero, he] at hrow
  linarith [ha v hv]

theorem strict_atom_floor_of_proper {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ z ∈ V, c ≤ row q D V a z) :
    ∀ v ∈ V, c - mass V a < ((q : ℚ) - 1) * a v := by
  intro v hv
  apply strict_atom_floor_of_support_smallRow hq hv
    (fun z hz hvz => digonfree hf hq hv hz hvz) a ha
  · apply hproper ((V.erase v).filter (fun z => 0 < a z))
    · exact (filter_subset _ _).trans (erase_subset v V)
    · intro he
      have hvU := he.symm ▸ hv
      exact (mem_erase.mp (mem_filter.mp hvU).1).1 rfl
  · exact hc
  · exact hr

end LeanCH.BR.WeightedSD
