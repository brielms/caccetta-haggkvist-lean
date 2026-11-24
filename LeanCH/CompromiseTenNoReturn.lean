module

public import LeanCH.CompromiseFrameGrowth

set_option linter.style.header false

/-! Degree-ten charge when all eight second-neighbour vertices have
minimum internal out-degree two and no heads back in the first set.
This closes, in particular, frames with no exceptional columns. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem good_low_fourteen (g : V) (hg : g ∈ f.good) (low : f.zOut g ≤ 1) :
    14 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  let P := inN adj g ∩ f.A
  have density : 7 ≤ P.card := by
    have count := card_sdiff_add_card_inter f.A (inN adj g)
    rw [inter_comm, f.cardA] at count
    change f.omission g + P.card = 10 at count
    have good := (mem_filter.mp hg).2
    omega
  have noReturn : f.aOut g = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact f.good_avoids_A H g hg a (mem_inter.mp ha).2
      ((mem_outN adj g a).mp (mem_inter.mp ha).1)
  have point (a : V) (ha : a ∈ P) : 2 ≤ 10 - (inN adj a).card := by
    have aA := (mem_inter.mp ha).2
    have edge := (mem_inN adj g a).mp (mem_inter.mp ha).1
    have inside := f.inside_at_least_two H a aA
    have bound := f.head_deficit H a aA g edge 1 (by rw [noReturn]; omega)
    omega
  have bound := sum_le_sum point
  simp only [sum_const, smul_eq_mul] at bound
  have upper := sum_le_sum_of_subset (f := fun a => 10 - (inN adj a).card)
    (inter_subset_right : P ⊆ f.A)
  change (∑ a ∈ P, (10 - (inN adj a).card)) ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) at upper
  omega

theorem z_edge_budget (minimum : ∀ z ∈ f.Z, 2 ≤ f.zOut z) :
    (∑ z ∈ f.Z, f.zOut z) ≤ 21 := by
  let K := ∑ z ∈ f.Z, f.zOut z
  let F := ∑ z ∈ f.Z, (f.zOut z - 1) / 3
  have pointBound (z : V) (hz : z ∈ f.Z) :
      (inN adj z ∩ f.Z).card + f.zOut z + 3 ≤ 8 + (f.zOut z - 1) / 3 := by
    have bound := CH.CompromiseTenLocal.local_degree_bound adj H.loopless H.noDigon
      H.noTri H.small f.Z 2 (by omega) minimum z hz
      ((card_le_card inter_subset_right).trans (by rw [f.cardZ]; omega))
    rw [f.cardZ] at bound
    exact bound
  have floorBound (z : V) (hz : z ∈ f.Z) :
      2 * ((f.zOut z - 1) / 3) + 2 ≤ f.zOut z := by
    have := minimum z hz
    omega
  have first := sum_le_sum pointBound
  have second := sum_le_sum floorBound
  have count := double_count adj f.Z f.Z
  simp only [sum_add_distrib, sum_const, smul_eq_mul, f.cardZ, ← mul_sum] at first second
  change K = ∑ z ∈ f.Z, (inN adj z ∩ f.Z).card at count
  change (∑ z ∈ f.Z, (inN adj z ∩ f.Z).card) + K + 8 * 3 ≤ 8 * 8 + F at first
  change 2 * F + 8 * 2 ≤ K at second
  change K ≤ 21
  omega

theorem four_twos (minimum : ∀ z ∈ f.Z, 2 ≤ f.zOut z) :
    4 ≤ (f.Z.filter (fun z => f.zOut z = 2)).card := by
  have smallSeven : LocalSmall adj := fun S hn hs => H.small S hn (by omega)
  exact (CH.CompromiseEight.eight_structure adj H.loopless H.noDigon H.noTri
    smallSeven f.Z f.cardZ minimum).1

theorem no_return_all_deficient (minimum : ∀ z ∈ f.Z, 2 ≤ f.zOut z)
    (noReturn : ∀ z ∈ f.Z, ∀ a ∈ f.A, ¬ adj z a) :
    ∀ a ∈ f.A, (inN adj a).card ≤ 9 := by
  let L := f.Z.filter (fun z => f.zOut z = 2)
  have lowCount : 4 ≤ L.card := f.four_twos H minimum
  have budget := f.z_edge_budget H minimum
  have zeroReturn (z : V) (hz : z ∈ f.Z) : f.aOut z = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact noReturn z hz a (mem_inter.mp ha).2 ((mem_outN adj z a).mp (mem_inter.mp ha).1)
  intro a ha
  have insideTwo := f.inside_at_least_two H a ha
  have capture (z : V) (hz : z ∈ f.Z) (edge : adj a z)
      (small : f.zOut z ≤ (f.inside a).card) : (inN adj a).card ≤ 9 := by
    have bound := f.head_deficit H a ha z edge 0 (by rw [zeroReturn z hz]; omega)
    omega
  by_cases seesLow : ∃ z ∈ L, adj a z
  · obtain ⟨z, hz, edge⟩ := seesLow
    exact capture z (mem_filter.mp hz).1 edge (by rw [(mem_filter.mp hz).2]; omega)
  have lowMissing : L ⊆ f.missing a := by
    intro z hz
    exact mem_sdiff.mpr ⟨(mem_filter.mp hz).1,
      fun h => seesLow ⟨z, hz, (mem_outN adj a z).mp h⟩⟩
  have extraLow : 4 ≤ f.extra a := lowCount.trans (card_le_card lowMissing)
  have extraHigh := f.extra_le_seven H a ha
  have insideExtra := f.inside_at_least_extra H a ha
  let P := outN adj a ∩ f.Z
  have splitCard : f.extra a + P.card = 8 := by
    have count := card_sdiff_add_card_inter f.Z (outN adj a)
    rw [inter_comm, f.cardZ] at count
    exact count
  have choice : ∃ z ∈ P, f.zOut z ≤ (f.inside a).card := by
    by_contra none
    have missingLower (z : V) (hz : z ∈ f.missing a) : 2 ≤ f.zOut z :=
      minimum z (mem_sdiff.mp hz).1
    have seenLower (z : V) (hz : z ∈ P) : (f.inside a).card + 1 ≤ f.zOut z := by
      have h : ¬ f.zOut z ≤ (f.inside a).card := fun h => none ⟨z, hz, h⟩
      omega
    have missed := sum_le_sum missingLower
    have seen := sum_le_sum seenLower
    simp only [sum_const, smul_eq_mul] at missed seen
    change f.extra a * 2 ≤ ∑ z ∈ f.missing a, f.zOut z at missed
    have disj : Disjoint (f.missing a) P := disjoint_left.mpr
      (fun _ hz hp => (mem_sdiff.mp hz).2 (mem_inter.mp hp).1)
    have union : f.missing a ∪ P = f.Z := by
      ext z
      simp only [missing, P, mem_union, mem_sdiff, mem_inter]
      tauto
    have split := sum_union (f := f.zOut) disj
    rw [union] at split
    have cases : P.card = 1 ∨ P.card = 2 ∨ P.card = 3 ∨ P.card = 4 := by omega
    rcases cases with one | two | three | four
    · rw [one] at seen splitCard
      omega
    · rw [two] at seen splitCard
      omega
    · rw [three] at seen splitCard
      omega
    · rw [four] at seen splitCard
      omega
  obtain ⟨z, hz, small⟩ := choice
  exact capture z (mem_inter.mp hz).2 ((mem_outN adj a z).mp (mem_inter.mp hz).1) small

theorem no_return_charge (minimum : ∀ z ∈ f.Z, 2 ≤ f.zOut z)
    (noReturn : ∀ z ∈ f.Z, ∀ a ∈ f.A, ¬ adj z a) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have point (a : V) (ha : a ∈ f.A) : 1 ≤ 10 - (inN adj a).card := by
    have := f.no_return_all_deficient H minimum noReturn a ha
    omega
  have bound := sum_le_sum point
  simpa only [sum_const, smul_eq_mul, Nat.mul_one, f.cardA] using bound

theorem all_good_charge (allGood : ∀ z ∈ f.Z, f.omission z ≤ 3) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  by_cases low : ∃ z ∈ f.Z, f.zOut z ≤ 1
  · obtain ⟨z, hz, small⟩ := low
    have bound := f.good_low_fourteen H z (mem_filter.mpr ⟨hz, allGood z hz⟩) small
    omega
  · apply f.no_return_charge H
    · intro z hz
      have hn : ¬ f.zOut z ≤ 1 := fun h => low ⟨z, hz, h⟩
      omega
    · intro z hz a ha
      exact f.good_avoids_A H z (mem_filter.mpr ⟨hz, allGood z hz⟩) a ha

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.good_low_fourteen
#print axioms CH.CompromiseTenFrame.Frame.z_edge_budget
#print axioms CH.CompromiseTenFrame.Frame.no_return_all_deficient
#print axioms CH.CompromiseTenFrame.Frame.all_good_charge
