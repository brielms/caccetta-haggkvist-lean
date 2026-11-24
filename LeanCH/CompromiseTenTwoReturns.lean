module

public import LeanCH.CompromiseTenReturnSets

set_option linter.style.header false

/-! Two exceptional columns cannot both return in an undercharged frame. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem both_returns_target_cap (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g)
    (returns : ∀ x ∈ f.exceptional, 1 ≤ f.aOut x) : f.returnTargets.card ≤ 2 := by
  let U := ∑ x ∈ f.exceptional, f.aOut x
  let F := ∑ x ∈ f.exceptional, (f.aOut x - 1) / 3
  have common := f.two_high_common_heads H exceptions minimum
  have point (x : V) (hx : x ∈ f.exceptional) :
      f.goodOnes.card + 3 + f.aOut x ≤ f.omission x + (f.aOut x - 1) / 3 := by
    have subset : f.goodOnes ⊆ inN adj x ∩ f.Z := by
      intro g hg
      exact mem_inter.mpr ⟨(mem_inN adj x g).mpr ((mem_outN adj g x).mp ((common.2 g hg).2 hx)),
        (mem_filter.mp (mem_filter.mp hg).1).1⟩
    have count := card_le_card subset
    have bound := f.return_predecessor_bound H x (mem_sdiff.mp hx).1 (returns x hx)
    omega
  have first := sum_le_sum point
  simp only [sum_add_distrib, sum_const, smul_eq_mul, exceptions] at first
  change 2 * (f.goodOnes.card + 3) + U ≤ f.exceptionalBudget + F at first
  have floors (x : V) (hx : x ∈ f.exceptional) : 3 * ((f.aOut x - 1) / 3) + 1 ≤ f.aOut x := by
    have positive := returns x hx
    omega
  have second := sum_le_sum floors
  simp only [sum_add_distrib, sum_const, smul_eq_mul, exceptions, Nat.mul_one, ← mul_sum] at second
  change 3 * F + 2 ≤ U at second
  have targets := f.return_targets_count
  change f.returnTargets.card ≤ U at targets
  have good := f.common_good_budget H exceptions minimum
  have product := Nat.mul_le_mul_right f.returnTargets.card common.1
  have partition := f.budget_partition
  have budget := f.total_le_eighteen H
  omega

theorem both_returns_exceptional_budget (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g)
    (returns : ∀ x ∈ f.exceptional, 1 ≤ f.aOut x) :
    2 * f.goodOnes.card + 8 ≤ f.exceptionalBudget := by
  have cap := f.both_returns_target_cap H exceptions minimum returns
  have common := f.two_high_common_heads H exceptions minimum
  have point (x : V) (hx : x ∈ f.exceptional) : f.goodOnes.card + 4 ≤ f.omission x := by
    have subset : f.goodOnes ⊆ inN adj x ∩ f.Z := by
      intro g hg
      exact mem_inter.mpr ⟨(mem_inN adj x g).mpr ((mem_outN adj g x).mp ((common.2 g hg).2 hx)),
        (mem_filter.mp (mem_filter.mp hg).1).1⟩
    have count := card_le_card subset
    have upper := card_le_card (f.return_subset_targets x hx)
    change f.aOut x ≤ f.returnTargets.card at upper
    have positive := returns x hx
    have bound := f.return_predecessor_bound H x (mem_sdiff.mp hx).1 positive
    omega
  have sum := sum_le_sum point
  simp only [sum_const, smul_eq_mul, exceptions] at sum
  change 2 * (f.goodOnes.card + 4) ≤ f.exceptionalBudget at sum
  omega

theorem both_returns_single_budget (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g)
    (returns : ∀ x ∈ f.exceptional, 1 ≤ f.aOut x) (one : f.returnTargets.card = 1) :
    2 * f.goodOnes.card + 10 ≤ f.exceptionalBudget := by
  obtain ⟨b, single⟩ := card_eq_one.mp one
  have bR : b ∈ f.returnTargets := single.symm ▸ mem_singleton_self b
  have bA := (mem_filter.mp bR).1
  have allReturn (x : V) (hx : x ∈ f.exceptional) : adj x b := by
    obtain ⟨a, ha⟩ := card_pos.mp (returns x hx)
    have aR := f.return_subset_targets x hx ha
    rw [single, mem_singleton] at aR
    subst a
    exact (mem_outN adj x b).mp (mem_inter.mp ha).1
  have common := f.two_high_common_heads H exceptions minimum
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < f.exceptional.card by omega)
  have missed : f.goodOnes ∪ f.exceptional ⊆ f.missing b := by
    intro z hz
    rcases mem_union.mp hz with good | ex
    · refine mem_sdiff.mpr ⟨(mem_filter.mp (mem_filter.mp good).1).1, ?_⟩
      intro edge
      exact H.noTri z x b ((mem_outN adj z x).mp ((common.2 z good).2 hx)) (allReturn x hx)
        ((mem_outN adj b z).mp edge)
    · refine mem_sdiff.mpr ⟨(mem_sdiff.mp ex).1, ?_⟩
      intro edge
      exact H.noDigon z b (allReturn z ex) ((mem_outN adj b z).mp edge)
  have disj : Disjoint f.goodOnes f.exceptional :=
    f.good_exceptional_disjoint.mono_left (filter_subset _ _)
  have extra := card_le_card missed
  rw [card_union_of_disjoint disj, exceptions] at extra
  change f.goodOnes.card + 2 ≤ f.extra b at extra
  have row := f.row_counts H b bA
  have point (z : V) (hz : z ∈ f.exceptional) : f.goodOnes.card + 5 ≤ f.omission z := by
    have edge := allReturn z hz
    have subset : insert b (outN adj b ∩ f.A) ⊆ f.A \ inN adj z := by
      intro a ha
      rcases mem_insert.mp ha with equal | ha
      · subst a
        exact mem_sdiff.mpr ⟨bA, fun incoming => H.noDigon z b edge ((mem_inN adj z b).mp incoming)⟩
      · exact mem_sdiff.mpr ⟨(mem_inter.mp ha).2, fun incoming =>
          H.noTri z b a edge ((mem_outN adj b a).mp (mem_inter.mp ha).1)
            ((mem_inN adj z a).mp incoming)⟩
    have count := card_le_card subset
    rw [card_insert_of_notMem (by simp [H.loopless])] at count
    change f.aOut b + 1 ≤ f.omission z at count
    omega
  have sum := sum_le_sum point
  simp only [sum_const, smul_eq_mul, exceptions] at sum
  change 2 * (f.goodOnes.card + 5) ≤ f.exceptionalBudget at sum
  omega

theorem two_high_not_both_return (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g) :
    ¬ (∀ x ∈ f.exceptional, 1 ≤ f.aOut x) := by
  intro returns
  have cap := f.both_returns_target_cap H exceptions minimum returns
  have common := f.two_high_common_heads H exceptions minimum
  have good := f.common_good_budget H exceptions minimum
  have partition := f.budget_partition
  have total := f.total_le_eighteen H
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < f.exceptional.card by omega)
  have upper := card_le_card (f.return_subset_targets x hx)
  have positive := returns x hx
  change f.aOut x ≤ f.returnTargets.card at upper
  by_cases one : f.returnTargets.card = 1
  · have exceptional := f.both_returns_single_budget H exceptions minimum returns one
    rw [one, Nat.mul_one] at good
    have ones : f.goodOnes.card = 2 := by omega
    have stronger := f.both_returns_good_budget H exceptions minimum ones returns
    rw [one] at stronger
    omega
  · have two : f.returnTargets.card = 2 := by omega
    have exceptional := f.both_returns_exceptional_budget H exceptions minimum returns
    rw [two] at good
    have ones : f.goodOnes.card = 2 := by omega
    have stronger := f.both_returns_good_budget H exceptions minimum ones returns
    rw [two] at stronger
    omega

theorem two_returning_charge (exceptions : f.exceptional.card = 2)
    (returns : ∀ x ∈ f.exceptional, 1 ≤ f.aOut x) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  by_contra failure
  have under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9 := by omega
  exact f.two_high_not_both_return H exceptions
    (f.undercharged_two_good_minimum H exceptions under) returns

theorem undercharged_two_nonreturn (exceptions : f.exceptional.card = 2)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    ∃ y ∈ f.exceptional, f.aOut y = 0 := by
  by_contra none
  have returns (y : V) (hy : y ∈ f.exceptional) : 1 ≤ f.aOut y := by
    have nonzero : f.aOut y ≠ 0 := fun zero => none ⟨y, hy, zero⟩
    omega
  have charge := f.two_returning_charge H exceptions returns
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.two_high_not_both_return
#print axioms CH.CompromiseTenFrame.Frame.two_returning_charge
#print axioms CH.CompromiseTenFrame.Frame.undercharged_two_nonreturn
