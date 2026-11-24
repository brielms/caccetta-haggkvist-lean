module

public import LeanCH.CompromiseTenUndercharged

set_option linter.style.header false

/-! Complementary head selection forces an actual return path at every
undercharged frame. One-exception rows missing that exception are deficient. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem zero_return_heads_deficient (a : V) (ha : a ∈ f.A)
    (noReturn : ∀ z ∈ outN adj a ∩ f.Z, f.aOut z = 0) : (inN adj a).card ≤ 9 := by
  let S := outN adj a ∩ f.Z
  have split : f.extra a + S.card = 8 := by
    have count := card_sdiff_add_card_inter f.Z (outN adj a)
    rw [inter_comm, f.cardZ] at count
    exact count
  have extra := f.extra_le_seven H a ha
  obtain ⟨z, hz, small⟩ := H.small S (card_pos.mp (by omega)) (by omega)
  have subset : outN adj z ∩ f.Z ⊆ S ∪ f.missing a := by
    intro b hb
    by_cases edge : adj a b
    · exact mem_union_left _ (mem_inter.mpr ⟨(mem_outN adj a b).mpr edge, (mem_inter.mp hb).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_inter.mp hb).2,
        fun h => edge ((mem_outN adj a b).mp h)⟩)
  have count := degree_bound (outN adj z ∩ f.Z) S (f.missing a) subset
  have equal : (outN adj z ∩ f.Z) ∩ S = outN adj z ∩ S := by
    ext b
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (mem_inter.mp h.2).2⟩, h.2⟩⟩
  rw [equal] at count
  change f.zOut z ≤ (outN adj z ∩ S).card + f.extra a at count
  have inside := f.full_inside_growth H a ha
  have bound := f.head_deficit H a ha z ((mem_outN adj a z).mp (mem_inter.mp hz).1) 0 (by
    rw [noReturn z hz]
    omega)
  omega

theorem undercharged_return_path
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    ∃ a ∈ f.A, 10 ≤ (inN adj a).card ∧ ∃ z ∈ f.Z,
      adj a z ∧ 4 ≤ f.omission z ∧ ∃ b ∈ f.A, adj z b := by
  have unpaid : ∃ a ∈ f.A, 10 ≤ (inN adj a).card := by
    by_contra none
    have point (a : V) (ha : a ∈ f.A) : 1 ≤ 10 - (inN adj a).card := by
      have h : ¬ 10 ≤ (inN adj a).card := fun h => none ⟨a, ha, h⟩
      omega
    have bound := sum_le_sum point
    simp only [sum_const, smul_eq_mul, Nat.mul_one, f.cardA] at bound
    omega
  obtain ⟨a, ha, high⟩ := unpaid
  have returning : ∃ z ∈ outN adj a ∩ f.Z, 1 ≤ f.aOut z := by
    by_contra none
    have zero (z : V) (hz : z ∈ outN adj a ∩ f.Z) : f.aOut z = 0 := by
      have h : ¬ 1 ≤ f.aOut z := fun h => none ⟨z, hz, h⟩
      omega
    have bound := f.zero_return_heads_deficient H a ha zero
    omega
  obtain ⟨z, hz, positive⟩ := returning
  obtain ⟨b, hb⟩ := card_pos.mp positive
  have edge := (mem_outN adj z b).mp (mem_inter.mp hb).1
  have bA := (mem_inter.mp hb).2
  refine ⟨a, ha, high, z, (mem_inter.mp hz).2,
    (mem_outN adj a z).mp (mem_inter.mp hz).1, ?_, b, bA, edge⟩
  by_contra small
  exact f.good_avoids_A H z (mem_filter.mpr ⟨(mem_inter.mp hz).2, by omega⟩) b bA edge

theorem one_missing_deficient (x : V) (single : f.exceptional = {x})
    (a : V) (ha : a ∈ f.A) (misses : ¬ adj a x) : (inN adj a).card ≤ 9 := by
  apply f.zero_return_heads_deficient H a ha
  intro z hz
  have good : z ∈ f.good := by
    by_contra notGood
    have ex : z ∈ f.exceptional := mem_sdiff.mpr ⟨(mem_inter.mp hz).2, notGood⟩
    rw [single, mem_singleton] at ex
    subst z
    exact misses ((mem_outN adj a x).mp (mem_inter.mp hz).1)
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  exact f.good_avoids_A H z good b (mem_inter.mp hb).2
    ((mem_outN adj z b).mp (mem_inter.mp hb).1)

theorem one_cost_two_charge (x : V) (single : f.exceptional = {x})
    (cost : f.aOut x + f.zOut x ≤ 2) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have point (a : V) (ha : a ∈ f.A) : 1 ≤ 10 - (inN adj a).card := by
    by_cases edge : adj a x
    · have inside := f.inside_at_least_two H a ha
      have bound := f.head_deficit H a ha x edge 0 (by omega)
      omega
    · have bound := f.one_missing_deficient H x single a ha edge
      omega
  have bound := sum_le_sum point
  simpa only [sum_const, smul_eq_mul, Nat.mul_one, f.cardA] using bound

theorem return_cap_four (z : V) (hz : z ∈ f.Z) (small : f.omission z ≤ 4) :
    f.aOut z ≤ 1 := by
  by_cases positive : 1 ≤ f.aOut z
  · have := f.return_bound H z hz positive
    omega
  · omega

theorem return_cap_five (z : V) (hz : z ∈ f.Z) (small : f.omission z ≤ 5) :
    f.aOut z ≤ 2 := by
  by_cases positive : 1 ≤ f.aOut z
  · have := f.return_bound H z hz positive
    omega
  · omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.zero_return_heads_deficient
#print axioms CH.CompromiseTenFrame.Frame.undercharged_return_path
#print axioms CH.CompromiseTenFrame.Frame.one_missing_deficient
