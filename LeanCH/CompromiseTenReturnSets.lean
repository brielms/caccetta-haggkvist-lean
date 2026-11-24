module

public import LeanCH.CompromiseTenTwoHigh
public import LeanCH.CompromiseSixBudget

set_option linter.style.header false

/-! Count distinct return targets and their compulsory omissions. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

@[expose] def goodBudget (f : Frame adj) := ∑ g ∈ f.good, f.omission g
@[expose] def exceptionalBudget (f : Frame adj) := ∑ x ∈ f.exceptional, f.omission x
@[expose] def returnTargets (f : Frame adj) :=
  f.A.filter (fun b => ∃ x ∈ f.exceptional, adj x b)
@[expose] def goodInternalTwos (f : Frame adj) :=
  f.good.filter (fun g => (outN adj g ∩ f.good).card = 2)

variable (H : Ambient adj) (f : Frame adj)
include H

omit H in
theorem budget_partition : f.goodBudget + f.exceptionalBudget = f.total := by
  dsimp [goodBudget, exceptionalBudget, total]
  rw [← sum_union f.good_exceptional_disjoint, f.good_exceptional_partition]

omit H in
theorem return_subset_targets (x : V) (hx : x ∈ f.exceptional) :
    outN adj x ∩ f.A ⊆ f.returnTargets := by
  intro b hb
  exact mem_filter.mpr ⟨(mem_inter.mp hb).2, x, hx, (mem_outN adj x b).mp (mem_inter.mp hb).1⟩

omit H in
theorem return_targets_count : f.returnTargets.card ≤ ∑ x ∈ f.exceptional, f.aOut x := by
  have point (b : V) (hb : b ∈ f.returnTargets) : 1 ≤ (inN adj b ∩ f.exceptional).card := by
    obtain ⟨x, hx, edge⟩ := (mem_filter.mp hb).2
    exact card_pos.mpr ⟨x, mem_inter.mpr ⟨(mem_inN adj b x).mpr edge, hx⟩⟩
  have lower := sum_le_sum point
  simp only [sum_const, smul_eq_mul, Nat.mul_one] at lower
  have upper := sum_le_sum_of_subset (f := fun b => (inN adj b ∩ f.exceptional).card)
    (filter_subset _ _ : f.returnTargets ⊆ f.A)
  change (∑ b ∈ f.returnTargets, (inN adj b ∩ f.exceptional).card) ≤
    ∑ b ∈ f.A, (inN adj b ∩ f.exceptional).card at upper
  have count := double_count adj f.exceptional f.A
  change (∑ x ∈ f.exceptional, f.aOut x) = ∑ b ∈ f.A, (inN adj b ∩ f.exceptional).card at count
  omega

theorem common_target_omission (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g)
    (g : V) (hg : g ∈ f.goodOnes) : f.returnTargets.card ≤ f.omission g := by
  have common := f.two_high_common_heads H exceptions minimum
  apply card_le_card
  intro b hb
  obtain ⟨x, hx, edge⟩ := (mem_filter.mp hb).2
  refine mem_sdiff.mpr ⟨(mem_filter.mp hb).1, ?_⟩
  intro incoming
  exact H.noTri g x b ((mem_outN adj g x).mp ((common.2 g hg).2 hx)) edge
    ((mem_inN adj g b).mp incoming)

theorem common_good_budget (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g) :
    f.goodOnes.card * f.returnTargets.card ≤ f.goodBudget := by
  have lower := sum_le_sum (fun g hg => f.common_target_omission H exceptions minimum g hg)
  simp only [sum_const, smul_eq_mul] at lower
  have upper : (∑ g ∈ f.goodOnes, f.omission g) ≤ f.goodBudget :=
    sum_le_sum_of_subset (filter_subset _ _)
  omega

theorem two_high_three_internal_twos (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g) (ones : f.goodOnes.card = 2) :
    3 ≤ f.goodInternalTwos.card := by
  have size : f.good.card = 6 := by have := f.good_exceptional_card; omega
  have minGood (g : V) (hg : g ∈ f.good) : 1 ≤ (outN adj g ∩ f.good).card := by
    have split := f.good_exceptional_degrees g
    have upper := card_le_card (inter_subset_right : outN adj g ∩ f.exceptional ⊆ f.exceptional)
    have lower := minimum g hg
    omega
  have budget := CH.CompromiseSixBudget.eleven adj H.loopless H.noDigon H.noTri
    H.small H.smallRev f.good size minGood ones
  have point (g : V) (hg : g ∈ f.good) :
      3 ≤ (outN adj g ∩ f.good).card + (if g ∈ f.goodOnes then 2 else 0) +
        (if g ∈ f.goodInternalTwos then 1 else 0) := by
    have min := minGood g hg
    by_cases one : g ∈ f.goodOnes
    · have degree := (mem_filter.mp one).2
      have notTwo : g ∉ f.goodInternalTwos := by intro h; have := (mem_filter.mp h).2; omega
      rw [ite_eq_left one, ite_eq_right notTwo, degree]
    · by_cases two : g ∈ f.goodInternalTwos
      · have degree := (mem_filter.mp two).2
        rw [ite_eq_right one, ite_eq_left two, degree]
      · have notOne : (outN adj g ∩ f.good).card ≠ 1 :=
          fun equal => one (mem_filter.mpr ⟨hg, equal⟩)
        have notTwo : (outN adj g ∩ f.good).card ≠ 2 :=
          fun equal => two (mem_filter.mpr ⟨hg, equal⟩)
        rw [ite_eq_right one, ite_eq_right two]
        omega
  have oneCount : (∑ g ∈ f.good, if g ∈ f.goodOnes then 2 else 0 : ℕ) = f.goodOnes.card * 2 := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul]
    exact congrArg (fun S : Finset V => S.card * 2)
      (show f.good ∩ f.goodOnes = f.goodOnes from
        inter_eq_right.mpr (filter_subset _ _))
  have twoCount : (∑ g ∈ f.good, if g ∈ f.goodInternalTwos then 1 else 0 : ℕ) =
      f.goodInternalTwos.card := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul, Nat.mul_one]
    exact congrArg Finset.card
      (show f.good ∩ f.goodInternalTwos = f.goodInternalTwos from
        inter_eq_right.mpr (filter_subset _ _))
  have lower := sum_le_sum point
  simp only [sum_add_distrib, sum_const, smul_eq_mul, oneCount, twoCount, size, ones] at lower
  omega

theorem both_returns_good_budget (exceptions : f.exceptional.card = 2)
    (minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g) (ones : f.goodOnes.card = 2)
    (returns : ∀ x ∈ f.exceptional, 1 ≤ f.aOut x) :
    2 * f.returnTargets.card + 3 ≤ f.goodBudget := by
  have many := f.two_high_three_internal_twos H exceptions minimum ones
  have positive (g : V) (hg : g ∈ f.goodInternalTwos) : 1 ≤ f.omission g := by
    have degree := (mem_filter.mp hg).2
    have min := minimum g (mem_filter.mp hg).1
    have split := f.good_exceptional_degrees g
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (outN adj g ∩ f.exceptional).card by omega)
    have xX := (mem_inter.mp hx).2
    have gx := (mem_outN adj g x).mp (mem_inter.mp hx).1
    obtain ⟨b, hb⟩ := card_pos.mp (returns x xX)
    have xb := (mem_outN adj x b).mp (mem_inter.mp hb).1
    exact card_pos.mpr ⟨b, mem_sdiff.mpr ⟨(mem_inter.mp hb).2, fun incoming =>
      H.noTri g x b gx xb ((mem_inN adj g b).mp incoming)⟩⟩
  have point (g : V) (_hg : g ∈ f.good) :
      (if g ∈ f.goodOnes then f.returnTargets.card else 0) +
        (if g ∈ f.goodInternalTwos then 1 else 0) ≤ f.omission g := by
    by_cases one : g ∈ f.goodOnes
    · have degree := (mem_filter.mp one).2
      have notTwo : g ∉ f.goodInternalTwos := by intro h; have := (mem_filter.mp h).2; omega
      rw [ite_eq_left one, ite_eq_right notTwo, Nat.add_zero]
      exact f.common_target_omission H exceptions minimum g one
    · by_cases two : g ∈ f.goodInternalTwos
      · rw [ite_eq_right one, ite_eq_left two, Nat.zero_add]
        exact positive g two
      · simp only [ite_eq_right one, ite_eq_right two, Nat.add_zero, Nat.zero_le]
  have oneCount : (∑ g ∈ f.good, if g ∈ f.goodOnes then f.returnTargets.card else 0 : ℕ) =
      f.goodOnes.card * f.returnTargets.card := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul]
    exact congrArg (fun S : Finset V => S.card * f.returnTargets.card)
      (show f.good ∩ f.goodOnes = f.goodOnes from
        inter_eq_right.mpr (filter_subset _ _))
  have twoCount : (∑ g ∈ f.good, if g ∈ f.goodInternalTwos then 1 else 0 : ℕ) =
      f.goodInternalTwos.card := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul, Nat.mul_one]
    exact congrArg Finset.card
      (show f.good ∩ f.goodInternalTwos = f.goodInternalTwos from
        inter_eq_right.mpr (filter_subset _ _))
  have lower := sum_le_sum point
  rw [sum_add_distrib, oneCount, twoCount, ones] at lower
  change 2 * f.returnTargets.card + f.goodInternalTwos.card ≤ f.goodBudget at lower
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.return_targets_count
#print axioms CH.CompromiseTenFrame.Frame.two_high_three_internal_twos
#print axioms CH.CompromiseTenFrame.Frame.both_returns_good_budget
