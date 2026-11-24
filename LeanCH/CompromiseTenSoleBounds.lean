module

public import LeanCH.CompromiseTenSoleReturn

set_option linter.style.header false

/-! The sole returning exception has one return target; its omission
is six or seven, and that target misses only three or four columns. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame.SoleReturn

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable {f : Frame adj} (s : SoleReturn f) (H : Ambient adj)
include s H

theorem budget : f.goodBudget + f.omission s.x + f.omission s.y ≤ 18 := by
  have equal : f.exceptionalBudget = f.omission s.x + f.omission s.y := by
    simp [exceptionalBudget, s.exceptions, s.different]
  have partition := f.budget_partition
  have total := f.total_le_eighteen H
  omega

theorem common_x_bound : f.goodOnes.card + 3 + f.aOut s.x ≤
    f.omission s.x + (f.aOut s.x - 1) / 3 := by
  have common := s.common H
  have subset : f.goodOnes ⊆ inN adj s.x ∩ f.Z := by
    intro g hg
    exact mem_inter.mpr ⟨(mem_inN adj s.x g).mpr
      ((mem_outN adj g s.x).mp ((common.2 g hg).2 s.x_mem)),
      (mem_filter.mp (mem_filter.mp hg).1).1⟩
  have count := card_le_card subset
  have bound := f.return_predecessor_bound H s.x s.x_Z s.xPositive
  omega

theorem common_target_budget : f.goodOnes.card * f.aOut s.x ≤ f.goodBudget := by
  have bound := f.common_good_budget H s.two (s.good_minimum H)
  have count := card_le_card (f.return_subset_targets s.x s.x_mem)
  change f.aOut s.x ≤ f.returnTargets.card at count
  exact (Nat.mul_le_mul_left f.goodOnes.card count).trans bound

theorem x_one : f.aOut s.x = 1 := by
  have budget := s.budget H
  have order := s.omission_order H
  have bound := s.common_x_bound H
  have good := s.common_target_budget H
  have common := (s.common H).1
  have product := Nat.mul_le_mul_right (f.aOut s.x) common
  have positive := s.xPositive
  omega

theorem small_shape : 2 ≤ f.goodOnes.card ∧ f.goodOnes.card ≤ 3 ∧
    6 ≤ f.omission s.x ∧ f.omission s.x ≤ 7 := by
  have one := s.x_one H
  have budget := s.budget H
  have order := s.omission_order H
  have bound := s.common_x_bound H
  have good := s.common_target_budget H
  have common := (s.common H).1
  rw [one, Nat.mul_one] at good
  rw [one] at bound
  omega

theorem target_missing_common (b : V) (_hb : b ∈ f.A) (edge : adj s.x b) :
    f.goodOnes ⊆ f.missing b := by
  intro g hg
  have common := s.common H
  exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_filter.mp hg).1).1, fun outgoing =>
    H.noTri g s.x b ((mem_outN adj g s.x).mp ((common.2 g hg).2 s.x_mem)) edge
      ((mem_outN adj b g).mp outgoing)⟩

theorem target_extra_lower (b : V) (hb : b ∈ f.A) (edge : adj s.x b) :
    f.goodOnes.card + 1 ≤ f.extra b := by
  have subset : insert s.x f.goodOnes ⊆ f.missing b := by
    apply insert_subset
    · exact mem_sdiff.mpr ⟨s.x_Z, fun outgoing =>
        H.noDigon s.x b edge ((mem_outN adj b s.x).mp outgoing)⟩
    · exact s.target_missing_common H b hb edge
  have notMember : s.x ∉ f.goodOnes := fun h =>
    (mem_sdiff.mp s.x_mem).2 (mem_filter.mp h).1
  have count := card_le_card subset
  rw [card_insert_of_notMem notMember] at count
  exact count

theorem target_head_count (b : V) (hb : b ∈ f.A) (edge : adj s.x b) :
    f.extra b + 3 ≤ f.omission s.x := by
  have subset : insert b (outN adj b ∩ f.A) ⊆ f.A \ inN adj s.x := by
    intro a ha
    rcases mem_insert.mp ha with equal | ha
    · subst a
      exact mem_sdiff.mpr ⟨hb, fun incoming =>
        H.noDigon s.x b edge ((mem_inN adj s.x b).mp incoming)⟩
    · exact mem_sdiff.mpr ⟨(mem_inter.mp ha).2, fun incoming =>
        H.noTri s.x b a edge ((mem_outN adj b a).mp (mem_inter.mp ha).1)
          ((mem_inN adj s.x a).mp incoming)⟩
  have count := card_le_card subset
  rw [card_insert_of_notMem (by simp [H.loopless])] at count
  change f.aOut b + 1 ≤ f.omission s.x at count
  have row := f.row_counts H b hb
  omega

theorem target_extra_upper (b : V) (hb : b ∈ f.A) (edge : adj s.x b) : f.extra b ≤ 4 := by
  have bound := s.target_head_count H b hb edge
  have shape := s.small_shape H
  omega

theorem target_good_missing (b : V) (hb : b ∈ f.A) (edge : adj s.x b) :
    (f.missing b ∩ f.good).card ≤ 3 := by
  have subset : insert s.x (f.missing b ∩ f.good) ⊆ f.missing b :=
    insert_subset (mem_sdiff.mpr ⟨s.x_Z, fun outgoing =>
      H.noDigon s.x b edge ((mem_outN adj b s.x).mp outgoing)⟩) inter_subset_left
  have notMember : s.x ∉ f.missing b ∩ f.good :=
    fun h => (mem_sdiff.mp s.x_mem).2 (mem_inter.mp h).2
  have count := card_le_card subset
  rw [card_insert_of_notMem notMember] at count
  change (f.missing b ∩ f.good).card + 1 ≤ f.extra b at count
  have upper := s.target_extra_upper H b hb edge
  omega

end CH.CompromiseTenFrame.Frame.SoleReturn

#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.x_one
#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.small_shape
#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.target_extra_upper
