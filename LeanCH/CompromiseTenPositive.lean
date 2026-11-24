module

public import LeanCH.CompromiseTenOneException

set_option linter.style.header false

/-! Positive-omission rows and exceptional access. A good degree-two
column restricts their number under undercharging; at two exceptions
the resulting covering charge is already sufficient. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

@[expose] def positiveRows (f : Frame adj) := f.A \ f.zeroExtra
@[expose] def exceptionalAccess (f : Frame adj) :=
  f.positiveRows.filter (fun a => ∃ z ∈ f.exceptional, adj a z)

variable (H : Ambient adj) (f : Frame adj)
include H

omit H in
theorem positive_extra (a : V) (ha : a ∈ f.positiveRows) : 1 ≤ f.extra a := by
  have notZero : f.extra a ≠ 0 := fun equal =>
    (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1, equal⟩)
  omega

omit H in
theorem zero_sees (a : V) (ha : a ∈ f.zeroExtra) (z : V) (hz : z ∈ f.Z) : adj a z := by
  by_contra misses
  have positive : 1 ≤ f.extra a := card_pos.mpr ⟨z, mem_sdiff.mpr ⟨hz,
    fun edge => misses ((mem_outN adj a z).mp edge)⟩⟩
  have zero := (mem_filter.mp ha).2
  omega

omit H in
theorem omission_positive (z : V) (hz : z ∈ f.Z) : f.A \ inN adj z ⊆ f.positiveRows := by
  intro a ha
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1, ?_⟩
  intro zero
  exact (mem_sdiff.mp ha).2 ((mem_inN adj z a).mpr (f.zero_sees a zero z hz))

omit H in
theorem positive_column_count (z : V) (hz : z ∈ f.Z) :
    f.omission z + (inN adj z ∩ f.positiveRows).card = f.positiveRows.card := by
  have equal : f.positiveRows \ inN adj z = f.A \ inN adj z := by
    apply Subset.antisymm
    · intro a ha
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp ha).1).1, (mem_sdiff.mp ha).2⟩
    · intro a ha
      exact mem_sdiff.mpr ⟨f.omission_positive z hz ha, (mem_sdiff.mp ha).2⟩
  have count := card_sdiff_add_card_inter f.positiveRows (inN adj z)
  rw [equal, inter_comm] at count
  exact count

omit H in
theorem exceptional_access_budget :
    f.exceptionalAccess.card + 4 * f.exceptional.card ≤
      f.exceptional.card * f.positiveRows.card := by
  have positive (a : V) (ha : a ∈ f.exceptionalAccess) :
      1 ≤ (outN adj a ∩ f.exceptional).card := by
    obtain ⟨z, hz, edge⟩ := (mem_filter.mp ha).2
    exact card_pos.mpr ⟨z, mem_inter.mpr ⟨(mem_outN adj a z).mpr edge, hz⟩⟩
  have lower := sum_le_sum positive
  simp only [sum_const, smul_eq_mul, Nat.mul_one] at lower
  have subset : f.exceptionalAccess ⊆ f.positiveRows := filter_subset _ _
  have upper := sum_le_sum_of_subset (f := fun a => (outN adj a ∩ f.exceptional).card) subset
  have count := double_count adj f.positiveRows f.exceptional
  have column (z : V) (hz : z ∈ f.exceptional) :
      (inN adj z ∩ f.positiveRows).card + 4 ≤ f.positiveRows.card := by
    have zZ := (mem_sdiff.mp hz).1
    have omission : 4 ≤ f.omission z := by
      rw [f.exceptional_eq_filter] at hz
      exact (mem_filter.mp hz).2
    have split := f.positive_column_count z zZ
    omega
  have total := sum_le_sum column
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at total
  omega

theorem good_two_positive_bound (g : V) (hg : g ∈ f.good) (two : f.zOut g = 2) :
    10 + f.positiveRows.card ≤
      (∑ a ∈ f.A, (10 - (inN adj a).card)) + 2 * f.omission g := by
  let P := inN adj g ∩ f.A
  let B := inN adj g ∩ f.positiveRows
  have pA : P ⊆ f.A := inter_subset_right
  have bP : B ⊆ P := by
    intro a ha
    exact mem_inter.mpr ⟨(mem_inter.mp ha).1, (mem_sdiff.mp (mem_inter.mp ha).2).1⟩
  have point (a : V) (ha : a ∈ P) :
      1 + (if a ∈ B then 1 else 0) ≤ 10 - (inN adj a).card := by
    have edge := (mem_inN adj g a).mp (mem_inter.mp ha).1
    by_cases positive : a ∈ B
    · have inside := f.inside_extra_positive H a (pA ha)
        (f.positive_extra a (mem_inter.mp positive).2)
      have bound := f.head_deficit H a (pA ha) g edge 1 (by
        rw [f.good_return_zero H g hg, two]
        omega)
      rw [ite_eq_left positive]
      omega
    · have inside := f.inside_at_least_two H a (pA ha)
      have bound := f.head_deficit H a (pA ha) g edge 0 (by
        rw [f.good_return_zero H g hg, two]
        omega)
      rw [ite_eq_right positive]
      omega
  have countB : (∑ a ∈ P, if a ∈ B then 1 else 0 : ℕ) = B.card := by
    simp [sum_ite_mem, inter_eq_right.mpr bP]
  have lower := sum_le_sum point
  simp only [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_one, countB] at lower
  have upper := sum_le_sum_of_subset (f := fun a => 10 - (inN adj a).card) pA
  change (∑ a ∈ P, (10 - (inN adj a).card)) ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) at upper
  have column := card_sdiff_add_card_inter f.A (inN adj g)
  rw [inter_comm, f.cardA] at column
  change f.omission g + P.card = 10 at column
  have positives := f.positive_column_count g (mem_filter.mp hg).1
  change f.omission g + B.card = f.positiveRows.card at positives
  omega

theorem undercharged_good_two_five (g : V) (hg : g ∈ f.good) (two : f.zOut g = 2)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) : f.positiveRows.card ≤ 5 := by
  have bound := f.good_two_positive_bound H g hg two
  have good := (mem_filter.mp hg).2
  omega

theorem outside_access_deficient (g : V) (hg : g ∈ f.good) (two : f.zOut g = 2)
    (a : V) (ha : a ∈ f.A) (outside : a ∉ f.exceptionalAccess) : (inN adj a).card ≤ 9 := by
  by_cases zero : a ∈ f.zeroExtra
  · have edge := f.zero_sees a zero g (mem_filter.mp hg).1
    have inside := f.inside_at_least_two H a ha
    have bound := f.head_deficit H a ha g edge 0 (by
      rw [f.good_return_zero H g hg, two]
      omega)
    omega
  · have positive : a ∈ f.positiveRows := mem_sdiff.mpr ⟨ha, zero⟩
    apply f.zero_return_heads_deficient H a ha
    intro z hz
    apply f.good_return_zero H z
    by_contra notGood
    have exceptional : z ∈ f.exceptional := mem_sdiff.mpr ⟨(mem_inter.mp hz).2, notGood⟩
    exact outside (mem_filter.mpr ⟨positive, z, exceptional,
      (mem_outN adj a z).mp (mem_inter.mp hz).1⟩)

theorem good_two_access_charge (g : V) (hg : g ∈ f.good) (two : f.zOut g = 2) :
    10 + (inN adj g ∩ f.positiveRows).card ≤
      (∑ a ∈ f.A, (10 - (inN adj a).card)) + f.exceptionalAccess.card := by
  let B := inN adj g ∩ f.positiveRows
  let N := f.A \ f.exceptionalAccess
  have bA : B ⊆ f.A := fun a ha => (mem_sdiff.mp (mem_inter.mp ha).2).1
  have nA : N ⊆ f.A := sdiff_subset
  have point (a : V) (ha : a ∈ f.A) :
      (if a ∈ N then 1 else 0) + (if a ∈ B then 1 else 0) ≤ 10 - (inN adj a).card := by
    by_cases inB : a ∈ B
    · have inside := f.inside_extra_positive H a ha
        (f.positive_extra a (mem_inter.mp inB).2)
      have edge := (mem_inN adj g a).mp (mem_inter.mp inB).1
      have bound := f.head_deficit H a ha g edge 1 (by
        rw [f.good_return_zero H g hg, two]
        omega)
      by_cases inN : a ∈ N <;> simp only [inB, inN, ite_true, ite_false] <;> omega
    · by_cases inN : a ∈ N
      · have bound := f.outside_access_deficient H g hg two a ha (mem_sdiff.mp inN).2
        rw [ite_eq_right inB, ite_eq_left inN]
        omega
      · simp only [ite_eq_right inB, ite_eq_right inN, Nat.add_zero, Nat.zero_le]
  have countN : (∑ a ∈ f.A, if a ∈ N then 1 else 0 : ℕ) = N.card := by
    simp [sum_ite_mem, inter_eq_right.mpr nA]
  have countB : (∑ a ∈ f.A, if a ∈ B then 1 else 0 : ℕ) = B.card := by
    simp [sum_ite_mem, inter_eq_right.mpr bA]
  have lower := sum_le_sum point
  rw [sum_add_distrib, countN, countB] at lower
  have subset : f.exceptionalAccess ⊆ f.A := (filter_subset _ _).trans sdiff_subset
  have split := card_sdiff_of_subset subset
  have cap := card_le_card subset
  change N.card = f.A.card - f.exceptionalAccess.card at split
  rw [f.cardA] at split cap
  change 10 + B.card ≤ _
  omega

theorem two_good_two_charge (exceptions : f.exceptional.card = 2)
    (g : V) (hg : g ∈ f.good) (two : f.zOut g = 2) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  by_contra failure
  have under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9 := by omega
  have small := f.undercharged_good_two_five H g hg two under
  have budget := f.exceptional_access_budget
  rw [exceptions] at budget
  have covered := f.positive_column_count g (mem_filter.mp hg).1
  have good := (mem_filter.mp hg).2
  have charge := f.good_two_access_charge H g hg two
  omega

theorem undercharged_two_good_minimum (exceptions : f.exceptional.card = 2)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    ∀ g ∈ f.good, 3 ≤ f.zOut g := by
  intro g hg
  have minimum := f.undercharged_good_minimum H under g hg
  by_contra small
  have charge := f.two_good_two_charge H exceptions g hg (by omega)
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.exceptional_access_budget
#print axioms CH.CompromiseTenFrame.Frame.good_two_positive_bound
#print axioms CH.CompromiseTenFrame.Frame.two_good_two_charge
#print axioms CH.CompromiseTenFrame.Frame.undercharged_two_good_minimum
