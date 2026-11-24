module

public import LeanCH.CompromiseTenFrame

set_option linter.style.header false

/-! The deficit charge for a ten/eight frame containing a good second
neighbour of internal out-degree at most one. The other frames are
not claimed to satisfy the charge in this module. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)

include H

theorem unreached_budget (a : V) (ha : a ∈ f.A) :
    (f.unreached a).card * (f.extra a + 3) ≤ f.total := by
  have lower (z : V) (hz : z ∈ f.unreached a) : f.extra a + 3 ≤ f.omission z := by
    by_contra small
    exact (mem_sdiff.mp hz).2 (f.missing_reached H a ha z (mem_sdiff.mp hz).1 (by omega))
  have bound := sum_le_sum lower
  simp only [sum_const, smul_eq_mul] at bound
  have subset : f.unreached a ⊆ f.Z := sdiff_subset.trans sdiff_subset
  exact bound.trans (sum_le_sum_of_subset subset)

omit H in
theorem unreached_account (a : V) :
    f.extra a + (second adj a ∩ f.A).card ≤
      (f.unreached a).card + (f.inside a).card := by
  have split := card_sdiff_add_card_inter (f.missing a) (second adj a)
  have disj : Disjoint (second adj a ∩ f.A) (f.missing a ∩ second adj a) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact disjoint_left.mp f.disj (mem_inter.mp hx).2
      (mem_sdiff.mp (mem_inter.mp hx').1).1
  have subset : (second adj a ∩ f.A) ∪ (f.missing a ∩ second adj a) ⊆ f.inside a := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact mem_inter.mpr ⟨(mem_inter.mp h).1, mem_union_left _ (mem_inter.mp h).2⟩
    · exact mem_inter.mpr ⟨(mem_inter.mp h).2,
        mem_union_right _ (mem_sdiff.mp (mem_inter.mp h).1).1⟩
  have bound := card_le_card subset
  rw [card_union_of_disjoint disj] at bound
  change (f.unreached a).card + (f.missing a ∩ second adj a).card = f.extra a at split
  omega

omit H in
theorem internal_le_inside (a : V) : (second adj a ∩ f.A).card ≤ (f.inside a).card :=
  card_le_card (fun _ h => mem_inter.mpr ⟨(mem_inter.mp h).1,
    mem_union_left _ (mem_inter.mp h).2⟩)

theorem thin_inside_structure (a : V) (ha : a ∈ f.A) (thin : (f.inside a).card ≤ 1) :
    (f.inside a).card = 1 ∧ (second adj a ∩ f.A).card = 1 ∧
      2 ≤ f.extra a ∧ f.extra a ≤ 3 := by
  have insideBound := f.internal_le_inside a
  have lower := f.internal_second_lower H a ha
  have account := f.unreached_account a
  have budget := f.unreached_budget H a ha
  have total := f.total_le_eighteen H
  have positive : 1 ≤ (second adj a ∩ f.A).card := by
    by_contra small
    have zero : (second adj a ∩ f.A).card = 0 := by omega
    have extraLarge : 5 ≤ f.extra a := by omega
    have unreachedLarge : 4 ≤ (f.unreached a).card := by omega
    have product := Nat.mul_le_mul unreachedLarge (show 8 ≤ f.extra a + 3 by omega)
    omega
  have internalOne : (second adj a ∩ f.A).card = 1 := by omega
  have insideOne : (f.inside a).card = 1 := by omega
  have extraSmall : f.extra a ≤ 3 := by
    by_contra large
    have extraLarge : 4 ≤ f.extra a := by omega
    have unreachedLarge : 4 ≤ (f.unreached a).card := by omega
    have product := Nat.mul_le_mul unreachedLarge (show 7 ≤ f.extra a + 3 by omega)
    omega
  exact ⟨insideOne, internalOne, by omega, extraSmall⟩

theorem inside_positive (a : V) (ha : a ∈ f.A) : 1 ≤ (f.inside a).card := by
  by_cases large : 2 ≤ (f.inside a).card
  · omega
  · have h := f.thin_inside_structure H a ha (by omega)
    omega

theorem internal_head_bound (a : V) (b : V) (hb : b ∈ outN adj a ∩ f.A) :
    (outN adj b ∩ f.A).card ≤
      (outN adj b ∩ (outN adj a ∩ f.A)).card + (second adj a ∩ f.A).card := by
  let W := outN adj a ∩ f.A
  have subset : outN adj b ∩ f.A ⊆ W ∪ (second adj a ∩ f.A) := by
    intro x hx
    by_cases edge : adj a x
    · exact mem_union_left _ (mem_inter.mpr ⟨(mem_outN adj a x).mpr edge, (mem_inter.mp hx).2⟩)
    · apply mem_union_right
      refine mem_inter.mpr ⟨(mem_second adj a x).mpr ⟨?_, edge, b,
        (mem_outN adj a b).mp (mem_inter.mp hb).1,
        (mem_outN adj b x).mp (mem_inter.mp hx).1⟩, (mem_inter.mp hx).2⟩
      intro equal
      subst x
      exact H.noDigon a b ((mem_outN adj a b).mp (mem_inter.mp hb).1)
        ((mem_outN adj b a).mp (mem_inter.mp hx).1)
  have bound := degree_bound (outN adj b ∩ f.A) W (second adj a ∩ f.A) subset
  have equal : (outN adj b ∩ f.A) ∩ W = outN adj b ∩ W := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (mem_inter.mp h.2).2⟩, h.2⟩⟩
  rw [equal] at bound
  exact bound

theorem thin_inside_three_zero (a : V) (ha : a ∈ f.A) (thin : (f.inside a).card ≤ 1) :
    3 ≤ f.zeroExtra.card := by
  obtain ⟨_, internalOne, extraLow, extraHigh⟩ := f.thin_inside_structure H a ha thin
  let W := outN adj a ∩ f.A
  have row := f.row_counts H a ha
  change W.card = 2 + f.extra a at row
  have minimum (b : V) (hb : b ∈ W) : 1 ≤ (outN adj b ∩ W).card := by
    have bound := f.internal_head_bound H a b hb
    have lower := f.minA H b (mem_inter.mp hb).2
    rw [internalOne] at bound
    change (outN adj b ∩ f.A).card ≤ (outN adj b ∩ W).card + 1 at bound
    omega
  have zeroOfOne (b : V) (hb : b ∈ W) (one : (outN adj b ∩ W).card = 1) :
      b ∈ f.zeroExtra := by
    have bound := f.internal_head_bound H a b hb
    rw [internalOne] at bound
    change (outN adj b ∩ f.A).card ≤ (outN adj b ∩ W).card + 1 at bound
    rw [one] at bound
    have count := f.row_counts H b (mem_inter.mp hb).2
    change (outN adj b ∩ f.A).card = 2 + f.extra b at count
    exact mem_filter.mpr ⟨(mem_inter.mp hb).2, by omega⟩
  by_cases four : W.card = 4
  · have rigid := rigid_small adj H.loopless H.noDigon H.noTri H.small W 1
      (by omega) (by omega) four minimum
    have subset : W ⊆ f.zeroExtra := fun b hb => zeroOfOne b hb (rigid b hb).1
    have count := card_le_card subset
    omega
  · have five : W.card = 5 := by omega
    have smallNine : CH.CompromiseNineLocal.SmallOut adj := fun S hn hs => H.small S hn (by omega)
    have fiveFact := CH.CompromiseNineLocal.five_structure adj H.loopless H.noDigon
      H.noTri smallNine W five minimum
    have subset : W.filter (fun b => (outN adj b ∩ W).card = 1) ⊆ f.zeroExtra :=
      fun b hb => zeroOfOne b (mem_filter.mp hb).1 (mem_filter.mp hb).2
    exact fiveFact.1.trans (card_le_card subset)

theorem zero_inside_two (a : V) (ha : a ∈ f.zeroExtra) : 2 ≤ (f.inside a).card := by
  have lower := f.internal_second_lower H a (mem_filter.mp ha).1
  rw [(mem_filter.mp ha).2] at lower
  have := f.internal_le_inside a
  omega

omit H in
theorem zero_complete (a : V) (ha : a ∈ f.zeroExtra) (z : V) (hz : z ∈ f.Z) : adj a z := by
  have zero := (mem_filter.mp ha).2
  have subset : f.Z ⊆ outN adj a := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp zero)
  exact (mem_outN adj a z).mp (subset hz)

/-- One good second neighbour of internal out-degree at most one pays
the full ten units of deficit required at an in-degree-eleven root. -/
theorem good_low_charge (g : V) (hg : g ∈ f.good) (low : f.zOut g ≤ 1) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  let P := inN adj g ∩ f.A
  let B := P.filter (fun a => 2 ≤ (f.inside a).card)
  have pA : P ⊆ f.A := inter_subset_right
  have bP : B ⊆ P := filter_subset _ _
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
  have bonus : 3 ≤ B.card := by
    by_cases all : ∀ a ∈ f.A, 2 ≤ (f.inside a).card
    · have equal : B = P := filter_eq_self.mpr (fun a ha => all a (pA ha))
      rw [equal]
      omega
    · push Not at all
      obtain ⟨a, ha, thin⟩ := all
      have three := f.thin_inside_three_zero H a ha (by omega)
      have subset : f.zeroExtra ⊆ B := by
        intro b hb
        refine mem_filter.mpr ⟨mem_inter.mpr ⟨?_, (mem_filter.mp hb).1⟩, f.zero_inside_two H b hb⟩
        exact (mem_inN adj g b).mpr (f.zero_complete b hb g (mem_filter.mp hg).1)
      exact three.trans (card_le_card subset)
  have point (a : V) (ha : a ∈ P) :
      1 + (if a ∈ B then 1 else 0) ≤ 10 - (inN adj a).card := by
    have edge := (mem_inN adj g a).mp (mem_inter.mp ha).1
    by_cases inB : a ∈ B
    · have inside := (mem_filter.mp inB).2
      have bound := f.head_deficit H a (pA ha) g edge 1 (by rw [noReturn]; omega)
      rw [ite_eq_left inB]
      omega
    · have inside := f.inside_positive H a (pA ha)
      have bound := f.head_deficit H a (pA ha) g edge 0 (by rw [noReturn]; omega)
      rw [ite_eq_right inB]
      omega
  have bound := sum_le_sum point
  have indicator : (∑ a ∈ P, if a ∈ B then 1 else 0 : ℕ) = B.card := by
    simp [sum_ite_mem, inter_eq_right.mpr bP]
  simp only [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_one, indicator] at bound
  have upper := sum_le_sum_of_subset (f := fun a => 10 - (inN adj a).card) pA
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.unreached_budget
#print axioms CH.CompromiseTenFrame.Frame.thin_inside_structure
#print axioms CH.CompromiseTenFrame.Frame.thin_inside_three_zero
#print axioms CH.CompromiseTenFrame.Frame.good_low_charge
