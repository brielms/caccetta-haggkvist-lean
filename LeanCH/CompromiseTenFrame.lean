module

public import LeanCH.CompromiseTenBudget
public import LeanCH.CompromiseTenTop

set_option linter.style.header false

/-! Exact accounting in a ten/eight neighbourhood frame. This module
does not assume the local deficit charge that remains to be established. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal CH.CompromiseTenBudget
public section

namespace CH.CompromiseTenFrame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

structure Ambient extends CH.CompromiseTenTop.Ambient adj where
  smallRev : SmallOut (fun u v => adj v u)

structure Frame where
  A : Finset V
  Z : Finset V
  cardA : A.card = 10
  cardZ : Z.card = 8
  disj : Disjoint A Z
  headsA : ∀ a ∈ A, outN adj a ⊆ A ∪ Z

namespace Frame

variable {adj}

@[expose] def missing (f : Frame adj) (a : V) := f.Z \ outN adj a
@[expose] def extra (f : Frame adj) (a : V) := (f.missing a).card
@[expose] def omission (f : Frame adj) (z : V) := (f.A \ inN adj z).card
@[expose] def total (f : Frame adj) := ∑ z ∈ f.Z, f.omission z
@[expose] def good (f : Frame adj) := f.Z.filter (fun z => f.omission z ≤ 3)
@[expose] def exceptional (f : Frame adj) := f.Z \ f.good
@[expose] def aOut (f : Frame adj) (v : V) := (outN adj v ∩ f.A).card
@[expose] def zOut (f : Frame adj) (v : V) := (outN adj v ∩ f.Z).card
@[expose] def outside (f : Frame adj) (z : V) := outN adj z \ (f.A ∪ f.Z)
@[expose] def inside (f : Frame adj) (a : V) := second adj a ∩ (f.A ∪ f.Z)
@[expose] def unreached (f : Frame adj) (a : V) := f.missing a \ second adj a
@[expose] def zeroExtra (f : Frame adj) := f.A.filter (fun a => f.extra a = 0)

variable (H : Ambient adj) (f : Frame adj)

include H

theorem row_counts (a : V) (ha : a ∈ f.A) : f.aOut a = 2 + f.extra a := by
  have union : (outN adj a ∩ f.A) ∪ (outN adj a ∩ f.Z) = outN adj a := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr (f.headsA a ha)]
  have count := card_union_of_disjoint (f.disj.mono
    (inter_subset_right : outN adj a ∩ f.A ⊆ f.A)
    (inter_subset_right : outN adj a ∩ f.Z ⊆ f.Z))
  rw [union, H.regular] at count
  have missing := card_sdiff_add_card_inter f.Z (outN adj a)
  rw [inter_comm, f.cardZ] at missing
  change f.extra a + (outN adj a ∩ f.Z).card = 8 at missing
  dsimp [aOut]
  omega

theorem minA (a : V) (ha : a ∈ f.A) : 2 ≤ (outN adj a ∩ f.A).card := by
  have := f.row_counts H a ha
  change (outN adj a ∩ f.A).card = 2 + f.extra a at this
  omega

omit H in
theorem total_eq_extra : f.total = ∑ a ∈ f.A, f.extra a := by
  have row (a : V) : f.extra a + (outN adj a ∩ f.Z).card = 8 := by
    have h := card_sdiff_add_card_inter f.Z (outN adj a)
    rw [inter_comm, f.cardZ] at h
    exact h
  have column (z : V) : f.omission z + (inN adj z ∩ f.A).card = 10 := by
    have h := card_sdiff_add_card_inter f.A (inN adj z)
    rw [inter_comm, f.cardA] at h
    exact h
  have rows := sum_congr rfl (fun a (_ : a ∈ f.A) => row a)
  have columns := sum_congr rfl (fun z (_ : z ∈ f.Z) => column z)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, f.cardA, f.cardZ] at rows columns
  have := double_count adj f.A f.Z
  dsimp [total]
  omega

theorem total_le_eighteen : f.total ≤ 18 := by
  have budget := ten_edge_budget adj H.loopless H.noDigon H.noTri H.small H.smallRev
    f.A f.cardA (f.minA H)
  have rows := sum_congr rfl (fun a ha => f.row_counts H a ha)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, f.cardA] at rows
  change (∑ a ∈ f.A, (outN adj a ∩ f.A).card) = 20 + ∑ a ∈ f.A, f.extra a at rows
  rw [f.total_eq_extra]
  omega

theorem exceptional_le_four : f.exceptional.card ≤ 4 := by
  have lower (z : V) (hz : z ∈ f.exceptional) : 4 ≤ f.omission z := by
    have hzZ := (mem_sdiff.mp hz).1
    have notGood := (mem_sdiff.mp hz).2
    simp only [good, mem_filter, hzZ, true_and] at notGood
    omega
  have bound := sum_le_sum lower
  simp only [sum_const, smul_eq_mul] at bound
  have upper : (∑ z ∈ f.exceptional, f.omission z) ≤ f.total :=
    sum_le_sum_of_subset sdiff_subset
  have := f.total_le_eighteen H
  omega

theorem return_bound (z : V) (hz : z ∈ f.Z) (positive : 1 ≤ f.aOut z) :
    3 + f.aOut z ≤ f.omission z + (f.aOut z - 1) / 3 := by
  let Q := outN adj z ∩ f.A
  let S := f.A \ inN adj z
  have qA : Q ⊆ f.A := inter_subset_right
  have qS : Q ⊆ S := by
    intro a ha
    refine mem_sdiff.mpr ⟨qA ha, ?_⟩
    intro incoming
    exact H.noDigon z a ((mem_outN adj z a).mp (mem_inter.mp ha).1)
      ((mem_inN adj z a).mp incoming)
  obtain ⟨a, ha, low⟩ := H.small Q (card_pos.mp positive)
    ((card_le_card qA).trans (by rw [f.cardA]))
  have edge := (mem_outN adj z a).mp (mem_inter.mp ha).1
  have missed : z ∈ f.missing a := mem_sdiff.mpr ⟨hz, fun h =>
    H.noDigon z a edge ((mem_outN adj a z).mp h)⟩
  have extraPos : 1 ≤ f.extra a := card_pos.mpr ⟨z, missed⟩
  have row := f.row_counts H a (qA ha)
  have subset : outN adj a ∩ f.A ⊆ Q ∪ (S \ Q) := by
    intro x hx
    have inS : x ∈ S := mem_sdiff.mpr ⟨(mem_inter.mp hx).2, fun h =>
      H.noTri z a x edge ((mem_outN adj a x).mp (mem_inter.mp hx).1)
        ((mem_inN adj z x).mp h)⟩
    by_cases inQ : x ∈ Q
    · exact mem_union_left _ inQ
    · exact mem_union_right _ (mem_sdiff.mpr ⟨inS, inQ⟩)
  have bound := degree_bound (outN adj a ∩ f.A) Q (S \ Q) subset
  have equal : (outN adj a ∩ f.A) ∩ Q = outN adj a ∩ Q := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, qA h.2⟩, h.2⟩⟩
  rw [equal, card_sdiff_of_subset qS] at bound
  have cardinal := card_le_card qS
  change Q.card ≤ f.omission z at cardinal
  change (outN adj a ∩ f.A).card ≤ (outN adj a ∩ Q).card + (f.omission z - Q.card) at bound
  change (outN adj a ∩ f.A).card = 2 + f.extra a at row
  change 3 + Q.card ≤ f.omission z + (Q.card - 1) / 3
  omega

theorem good_avoids_A (g : V) (hg : g ∈ f.good) (a : V) (ha : a ∈ f.A) : ¬ adj g a := by
  intro edge
  have positive : 1 ≤ f.aOut g :=
    card_pos.mpr ⟨a, mem_inter.mpr ⟨(mem_outN adj g a).mpr edge, ha⟩⟩
  have bound := f.return_bound H g (mem_filter.mp hg).1 positive
  have small := (mem_filter.mp hg).2
  omega

theorem missing_reached (a : V) (ha : a ∈ f.A) (z : V) (hz : z ∈ f.missing a)
    (small : f.omission z < f.extra a + 3) : z ∈ second adj a := by
  have zZ := (mem_sdiff.mp hz).1
  have notEdge : ¬ adj a z := fun h => (mem_sdiff.mp hz).2 ((mem_outN adj a z).mpr h)
  have different : z ≠ a := by intro equal; subst z; exact disjoint_left.mp f.disj ha zZ
  by_contra missing
  have subset : insert a (outN adj a ∩ f.A) ⊆ f.A \ inN adj z := by
    intro b hb
    rcases mem_insert.mp hb with equal | hb
    · subst b
      exact mem_sdiff.mpr ⟨ha, fun h => notEdge ((mem_inN adj z a).mp h)⟩
    · refine mem_sdiff.mpr ⟨(mem_inter.mp hb).2, ?_⟩
      intro incoming
      exact missing ((mem_second adj a z).mpr ⟨different, notEdge, b,
        (mem_outN adj a b).mp (mem_inter.mp hb).1, (mem_inN adj z b).mp incoming⟩)
  have count := card_le_card subset
  rw [card_insert_of_notMem (by simp [H.loopless])] at count
  have row := f.row_counts H a ha
  change (outN adj a ∩ f.A).card = 2 + f.extra a at row
  change (outN adj a ∩ f.A).card + 1 ≤ f.omission z at count
  omega

theorem internal_second_lower (a : V) (ha : a ∈ f.A) :
    2 ≤ (second adj a ∩ f.A).card + (f.extra a + 1) / 3 := by
  let W := outN adj a ∩ f.A
  have row := f.row_counts H a ha
  have positive : 0 < W.card := by change 0 < f.aOut a; omega
  obtain ⟨b, hb, small⟩ := H.small W (card_pos.mp positive)
    ((card_le_card inter_subset_right).trans (by rw [f.cardA]))
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
  have minimum := f.minA H b (mem_inter.mp hb).2
  change W.card = 2 + f.extra a at row
  omega

theorem outside_partition (z : V) : f.aOut z + f.zOut z + (f.outside z).card = 10 := by
  have count := card_union_of_disjoint (f.disj.mono
    (inter_subset_right : outN adj z ∩ f.A ⊆ f.A)
    (inter_subset_right : outN adj z ∩ f.Z ⊆ f.Z))
  rw [← inter_union_distrib_left] at count
  have split := card_sdiff_add_card_inter (outN adj z) (f.A ∪ f.Z)
  rw [H.regular] at split
  dsimp [aOut, zOut, outside]
  omega

omit H in
theorem head_capture (a : V) (ha : a ∈ f.A) (z : V) (edge : adj a z) :
    (f.inside a).card + (f.outside z).card ≤ (second adj a).card := by
  have subset : f.outside z ⊆ second adj a := by
    intro x hx
    have notIn := (mem_sdiff.mp hx).2
    refine (mem_second adj a x).mpr ⟨?_, ?_, z, edge,
      (mem_outN adj z x).mp (mem_sdiff.mp hx).1⟩
    · intro equal
      subst x
      exact notIn (mem_union_left _ ha)
    · intro incoming
      exact notIn (f.headsA a ha ((mem_outN adj a x).mpr incoming))
  have disj : Disjoint (f.inside a) (f.outside z) :=
    disjoint_left.mpr (fun _ hx hx' => (mem_sdiff.mp hx').2 (mem_inter.mp hx).2)
  have bound := card_le_card (union_subset
    (inter_subset_left : f.inside a ⊆ second adj a) subset)
  change (f.inside a ∪ f.outside z).card ≤ (second adj a).card at bound
  rw [card_union_of_disjoint disj] at bound
  exact bound

theorem head_deficit (a : V) (ha : a ∈ f.A) (z : V) (edge : adj a z) (t : ℕ)
    (bound : f.aOut z + f.zOut z + t ≤ (f.inside a).card) : (inN adj a).card + t ≤ 9 := by
  have captured := f.head_capture a ha z edge
  have outside := f.outside_partition H z
  have bad := H.bad a
  omega

end Frame
end CH.CompromiseTenFrame

#print axioms CH.CompromiseTenFrame.Frame.total_le_eighteen
#print axioms CH.CompromiseTenFrame.Frame.exceptional_le_four
#print axioms CH.CompromiseTenFrame.Frame.head_deficit
