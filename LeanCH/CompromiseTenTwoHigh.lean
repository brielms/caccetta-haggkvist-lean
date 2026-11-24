module

public import LeanCH.CompromiseTenReturnBudget

set_option linter.style.header false

/-! The remaining two-exception case has six good vertices of Z-degree
at least three. Two good vertices point to both exceptions, increasing
the omission needed by every actual return. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

@[expose] def goodOnes (f : Frame adj) :=
  f.good.filter (fun g => (outN adj g ∩ f.good).card = 1)

variable (H : Ambient adj) (f : Frame adj)
include H

omit H in
theorem good_exceptional_partition : f.good ∪ f.exceptional = f.Z :=
  union_sdiff_of_subset (filter_subset _ _)

omit H in
theorem good_exceptional_disjoint : Disjoint f.good f.exceptional :=
  disjoint_left.mpr (fun _ good ex => (mem_sdiff.mp ex).2 good)

omit H in
theorem good_exceptional_card : f.good.card + f.exceptional.card = 8 := by
  rw [← card_union_of_disjoint f.good_exceptional_disjoint,
    f.good_exceptional_partition, f.cardZ]

omit H in
theorem good_exceptional_degrees (z : V) :
    f.zOut z = (outN adj z ∩ f.good).card + (outN adj z ∩ f.exceptional).card := by
  rw [← card_union_of_disjoint (f.good_exceptional_disjoint.mono
    inter_subset_right inter_subset_right), ← inter_union_distrib_left,
    f.good_exceptional_partition]
  rfl

theorem two_high_common_heads (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g) :
    2 ≤ f.goodOnes.card ∧
      ∀ g ∈ f.goodOnes, f.zOut g = 3 ∧ f.exceptional ⊆ outN adj g := by
  have size : f.good.card = 6 := by have := f.good_exceptional_card; omega
  have minGood (g : V) (hg : g ∈ f.good) : 1 ≤ (outN adj g ∩ f.good).card := by
    have split := f.good_exceptional_degrees g
    have upper := card_le_card (inter_subset_right : outN adj g ∩ f.exceptional ⊆ f.exceptional)
    have lower := minimum g hg
    omega
  have smallNine : CH.CompromiseNineLocal.SmallOut adj := fun S hn hs => H.small S hn (by omega)
  have count := CH.CompromiseNineLocal.six_two_degree_one adj H.loopless H.noDigon
    H.noTri smallNine f.good size minGood
  refine ⟨count, ?_⟩
  intro g hg
  have low := (mem_filter.mp hg).2
  have lower := minimum g (mem_filter.mp hg).1
  have split := f.good_exceptional_degrees g
  have upper := card_le_card (inter_subset_right : outN adj g ∩ f.exceptional ⊆ f.exceptional)
  have equal : outN adj g ∩ f.exceptional = f.exceptional :=
    eq_of_subset_of_card_le inter_subset_right (by omega)
  refine ⟨by omega, ?_⟩
  rw [← equal]
  exact inter_subset_left

theorem two_high_return_omission (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g)
    (x : V) (hx : x ∈ f.exceptional) (positive : 1 ≤ f.aOut x) : 6 ≤ f.omission x := by
  have common := f.two_high_common_heads H exceptions minimum
  have subset : f.goodOnes ⊆ inN adj x ∩ f.Z := by
    intro g hg
    exact mem_inter.mpr ⟨(mem_inN adj x g).mpr ((mem_outN adj g x).mp ((common.2 g hg).2 hx)),
      (mem_filter.mp (mem_filter.mp hg).1).1⟩
  have count := card_le_card subset
  have bound := f.return_predecessor_bound H x (mem_sdiff.mp hx).1 positive
  omega

theorem undercharged_two_return (exceptions : f.exceptional.card = 2)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    (∀ g ∈ f.good, 3 ≤ f.zOut g) ∧ 2 ≤ f.goodOnes.card ∧
      (∀ g ∈ f.goodOnes, f.zOut g = 3 ∧ f.exceptional ⊆ outN adj g) ∧
      ∃ a ∈ f.A, 10 ≤ (inN adj a).card ∧ ∃ x ∈ f.exceptional,
        adj a x ∧ 6 ≤ f.omission x ∧ f.omission x ≤ 9 ∧ ∃ b ∈ f.A, adj x b := by
  have minimum := f.undercharged_two_good_minimum H exceptions under
  have common := f.two_high_common_heads H exceptions minimum
  refine ⟨minimum, common.1, common.2, ?_⟩
  obtain ⟨a, ha, high, x, hx, ax, omission, b, hb, xb⟩ := f.undercharged_return_path H under
  have ex : x ∈ f.exceptional := by
    rw [f.exceptional_eq_filter]
    exact mem_filter.mpr ⟨hx, omission⟩
  have positive : 1 ≤ f.aOut x :=
    card_pos.mpr ⟨b, mem_inter.mpr ⟨(mem_outN adj x b).mpr xb, hb⟩⟩
  have lower := f.two_high_return_omission H exceptions minimum x ex positive
  have incoming : 1 ≤ (inN adj x ∩ f.A).card :=
    card_pos.mpr ⟨a, mem_inter.mpr ⟨(mem_inN adj x a).mpr ax, ha⟩⟩
  have column := card_sdiff_add_card_inter f.A (inN adj x)
  rw [inter_comm, f.cardA] at column
  change f.omission x + (inN adj x ∩ f.A).card = 10 at column
  exact ⟨a, ha, high, x, ex, ax, lower, by omega, b, hb, xb⟩

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.two_high_common_heads
#print axioms CH.CompromiseTenFrame.Frame.two_high_return_omission
#print axioms CH.CompromiseTenFrame.Frame.undercharged_two_return
