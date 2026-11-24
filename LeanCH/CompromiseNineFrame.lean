module

public import LeanCH.CompromiseNineLocal
public import LeanCH.CompromiseTransport

set_option linter.style.header false

/-! Graph accounting for the degree-nine candidate. The exceptional-case
dichotomy is not asserted by this module. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

structure Ambient : Prop where
  loopless : ∀ v, ¬ adj v v
  noDigon : ∀ u v, adj u v → ¬ adj v u
  noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u
  small : SmallOut adj
  smallRev : SmallIn adj
  regular : ∀ v, (outN adj v).card = 9
  cap : ∀ v, (inN adj v).card ≤ 10
  bad : ∀ v, (second adj v).card + (inN adj v).card ≤ 17

structure Frame where
  A : Finset V
  Z : Finset V
  cardA : A.card = 9
  cardZ : Z.card = 7
  disj : Disjoint A Z
  headsA : ∀ a ∈ A, outN adj a ⊆ A ∪ Z
  reachedZ : ∀ z ∈ Z, ∃ a ∈ A, adj a z

namespace Frame

variable {adj}

@[expose] def missing (f : Frame adj) (a : V) : Finset V := f.Z \ outN adj a
@[expose] def extra (f : Frame adj) (a : V) : ℕ := (f.missing a).card
@[expose] def omission (f : Frame adj) (z : V) : ℕ := (f.A \ inN adj z).card
@[expose] def total (f : Frame adj) : ℕ := ∑ z ∈ f.Z, f.omission z
@[expose] def good (f : Frame adj) : Finset V := f.Z.filter (fun z => f.omission z ≤ 3)
@[expose] def exceptional (f : Frame adj) : Finset V := f.Z \ f.good
@[expose] def goodBudget (f : Frame adj) : ℕ := ∑ z ∈ f.good, f.omission z
@[expose] def zOut (f : Frame adj) (z : V) : ℕ := (outN adj z ∩ f.Z).card
@[expose] def aOut (f : Frame adj) (z : V) : ℕ := (outN adj z ∩ f.A).card
@[expose] def outside (f : Frame adj) (z : V) : Finset V := outN adj z \ (f.A ∪ f.Z)
@[expose] def inside (f : Frame adj) (a : V) : Finset V := second adj a ∩ (f.A ∪ f.Z)

variable (H : Ambient adj) (f : Frame adj)

include H

theorem row_counts (a : V) (ha : a ∈ f.A) :
    f.aOut a = 2 + f.extra a := by
  have he : (outN adj a ∩ f.A) ∪ (outN adj a ∩ f.Z) = outN adj a := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr (f.headsA a ha)]
  have hd : Disjoint (outN adj a ∩ f.A) (outN adj a ∩ f.Z) :=
    f.disj.mono inter_subset_right inter_subset_right
  have hc := card_union_of_disjoint hd
  rw [he, H.regular] at hc
  have hm := card_sdiff_add_card_inter f.Z (outN adj a)
  rw [inter_comm, f.cardZ] at hm
  change f.extra a + (outN adj a ∩ f.Z).card = 7 at hm
  dsimp [aOut]
  omega

theorem minA (a : V) (ha : a ∈ f.A) : 2 ≤ (outN adj a ∩ f.A).card := by
  have := f.row_counts H a ha
  change (outN adj a ∩ f.A).card = 2 + f.extra a at this
  omega

theorem extra_le_six (a : V) (ha : a ∈ f.A) : f.extra a ≤ 6 := by
  have hs : insert a (outN adj a ∩ f.A) ⊆ f.A := insert_subset ha inter_subset_right
  have hn : a ∉ outN adj a ∩ f.A := by simp [H.loopless]
  have hc := card_le_card hs
  rw [card_insert_of_notMem hn, f.cardA] at hc
  have := f.row_counts H a ha
  change (outN adj a ∩ f.A).card = 2 + f.extra a at this
  omega

omit H in
theorem omission_le_eight (z : V) (hz : z ∈ f.Z) : f.omission z ≤ 8 := by
  obtain ⟨a, ha, haz⟩ := f.reachedZ z hz
  have hp : 1 ≤ (inN adj z ∩ f.A).card :=
    card_pos.mpr ⟨a, mem_inter.mpr ⟨by simpa using haz, ha⟩⟩
  have hc := card_sdiff_add_card_inter f.A (inN adj z)
  rw [inter_comm, f.cardA] at hc
  change f.omission z + (inN adj z ∩ f.A).card = 9 at hc
  omega

omit H in
theorem total_eq_extra : f.total = ∑ a ∈ f.A, f.extra a := by
  have hp (a : V) : f.extra a + (outN adj a ∩ f.Z).card = 7 := by
    have hc := card_sdiff_add_card_inter f.Z (outN adj a)
    rw [inter_comm, f.cardZ] at hc
    exact hc
  have hq (z : V) : f.omission z + (inN adj z ∩ f.A).card = 9 := by
    have hc := card_sdiff_add_card_inter f.A (inN adj z)
    rw [inter_comm, f.cardA] at hc
    exact hc
  have hs := sum_congr rfl (fun a (_ : a ∈ f.A) => hp a)
  have ht := sum_congr rfl (fun z (_ : z ∈ f.Z) => hq z)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, f.cardA, f.cardZ] at hs ht
  have := double_count adj f.A f.Z
  dsimp [total]
  omega

theorem total_le_eleven : f.total ≤ 11 := by
  have hb := nine_edge_budget adj H.loopless H.noDigon H.noTri H.small H.smallRev
    f.A f.cardA (f.minA H)
  have hs := sum_congr rfl (fun a ha => f.row_counts H a ha)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, f.cardA] at hs
  change (∑ a ∈ f.A, (outN adj a ∩ f.A).card) = 18 + ∑ a ∈ f.A, f.extra a at hs
  rw [f.total_eq_extra]
  omega

theorem exceptional_le_two : f.exceptional.card ≤ 2 := by
  have hm (z : V) (hz : z ∈ f.exceptional) : 4 ≤ f.omission z := by
    have hzZ := (mem_sdiff.mp hz).1
    have hn := (mem_sdiff.mp hz).2
    simp only [good, mem_filter, hzZ, true_and] at hn
    omega
  have hs : f.exceptional.card * 4 ≤ ∑ z ∈ f.exceptional, f.omission z := by
    calc
      _ = ∑ _z ∈ f.exceptional, 4 := by simp
      _ ≤ _ := sum_le_sum hm
  have ht : ∑ z ∈ f.exceptional, f.omission z ≤ f.total :=
    sum_le_sum_of_subset (sdiff_subset : f.exceptional ⊆ f.Z)
  have := f.total_le_eleven H
  omega

theorem return_bound (z : V) (hz : z ∈ f.Z) (hpos : 1 ≤ f.aOut z) :
    3 + f.aOut z ≤ f.omission z + (f.aOut z - 1) / 3 := by
  let Q := outN adj z ∩ f.A
  let S := f.A \ inN adj z
  have hQA : Q ⊆ f.A := inter_subset_right
  have hQS : Q ⊆ S := by
    intro a ha
    refine mem_sdiff.mpr ⟨hQA ha, ?_⟩
    intro haz
    exact H.noDigon z a (by simpa using (mem_inter.mp ha).1) (by simpa using haz)
  obtain ⟨a, ha, hsmall⟩ := H.small Q (card_pos.mp hpos)
    ((card_le_card hQA).trans (by rw [f.cardA]))
  have hza : adj z a := (mem_outN adj z a).mp (mem_inter.mp ha).1
  have hzMiss : z ∈ f.missing a := mem_sdiff.mpr ⟨hz, by
    intro haz
    exact H.noDigon z a hza (by simpa using haz)⟩
  have hepos : 1 ≤ f.extra a := card_pos.mpr ⟨z, hzMiss⟩
  have hk := f.row_counts H a (hQA ha)
  have hheads : outN adj a ∩ f.A ⊆ Q ∪ (S \ Q) := by
    intro x hx
    have hxS : x ∈ S := by
      refine mem_sdiff.mpr ⟨(mem_inter.mp hx).2, ?_⟩
      intro hxz
      exact H.noTri z a x hza (by simpa using (mem_inter.mp hx).1) (by simpa using hxz)
    by_cases hxQ : x ∈ Q
    · exact mem_union_left _ hxQ
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hxS, hxQ⟩)
  have hb := degree_bound (outN adj a ∩ f.A) Q (S \ Q) hheads
  have heq : (outN adj a ∩ f.A) ∩ Q = outN adj a ∩ Q := by
    ext x; simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hQA h.2⟩, h.2⟩⟩
  rw [heq, card_sdiff_of_subset hQS] at hb
  have hcard := card_le_card hQS
  change Q.card ≤ f.omission z at hcard
  change (outN adj a ∩ f.A).card ≤ (outN adj a ∩ Q).card + (f.omission z - Q.card) at hb
  change (outN adj a ∩ f.A).card = 2 + f.extra a at hk
  change 3 + Q.card ≤ f.omission z + (Q.card - 1) / 3
  omega

theorem good_avoids_A (g : V) (hg : g ∈ f.good) (a : V) (ha : a ∈ f.A) : ¬ adj g a := by
  intro hga
  have hp : 1 ≤ f.aOut g := card_pos.mpr ⟨a, mem_inter.mpr ⟨by simpa using hga, ha⟩⟩
  have hr := f.return_bound H g (mem_filter.mp hg).1 hp
  have hd := (mem_filter.mp hg).2
  omega

theorem missing_reached (a : V) (ha : a ∈ f.A) (z : V) (hz : z ∈ f.missing a)
    (hdelta : f.omission z < f.extra a + 3) : z ∈ second adj a := by
  have hzZ := (mem_sdiff.mp hz).1
  have haz : ¬ adj a z := by simpa using (mem_sdiff.mp hz).2
  have hza : z ≠ a := by
    intro he
    subst z
    exact disjoint_left.mp f.disj ha hzZ
  by_contra hn
  have hs : insert a (outN adj a ∩ f.A) ⊆ f.A \ inN adj z := by
    intro b hb
    rcases mem_insert.mp hb with hba | hb
    · subst b
      exact mem_sdiff.mpr ⟨ha, by simpa using haz⟩
    · refine mem_sdiff.mpr ⟨(mem_inter.mp hb).2, ?_⟩
      intro hbz
      exact hn ((mem_second adj a z).mpr ⟨hza, haz, b,
        by simpa using (mem_inter.mp hb).1, by simpa using hbz⟩)
  have hc := card_le_card hs
  rw [card_insert_of_notMem (by simp [H.loopless])] at hc
  have hr := f.row_counts H a ha
  change (outN adj a ∩ f.A).card = 2 + f.extra a at hr
  change (outN adj a ∩ f.A).card + 1 ≤ f.omission z at hc
  omega

theorem good_missing_reached (a : V) (ha : a ∈ f.A) (g : V)
    (hg : g ∈ f.missing a ∩ f.good) : g ∈ second adj a := by
  have he : 1 ≤ f.extra a := card_pos.mpr ⟨g, (mem_inter.mp hg).1⟩
  have hd := (mem_filter.mp (mem_inter.mp hg).2).2
  exact f.missing_reached H a ha g (mem_inter.mp hg).1 (by omega)

theorem internal_second_lower (a : V) (ha : a ∈ f.A) :
    2 ≤ (second adj a ∩ f.A).card + (f.extra a + 1) / 3 := by
  let W := outN adj a ∩ f.A
  have hWA : W ⊆ f.A := inter_subset_right
  have hr := f.row_counts H a ha
  have hp : 0 < W.card := by change 0 < f.aOut a; omega
  obtain ⟨b, hb, hsmall⟩ := H.small W (card_pos.mp hp)
    ((card_le_card hWA).trans (by rw [f.cardA]))
  have hheads : outN adj b ∩ f.A ⊆ W ∪ (second adj a ∩ f.A) := by
    intro x hx
    by_cases hax : adj a x
    · exact mem_union_left _ (mem_inter.mpr ⟨by simpa using hax, (mem_inter.mp hx).2⟩)
    · apply mem_union_right
      refine mem_inter.mpr ⟨(mem_second adj a x).mpr ⟨?_, hax, b,
        by simpa using (mem_inter.mp hb).1, by simpa using (mem_inter.mp hx).1⟩,
        (mem_inter.mp hx).2⟩
      intro he
      subst x
      exact H.noDigon a b (by simpa using (mem_inter.mp hb).1)
        (by simpa using (mem_inter.mp hx).1)
  have hc := degree_bound (outN adj b ∩ f.A) W (second adj a ∩ f.A) hheads
  have heq : (outN adj b ∩ f.A) ∩ W = outN adj b ∩ W := by
    ext x; simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hWA h.2⟩, h.2⟩⟩
  rw [heq] at hc
  have hm := f.minA H b (hWA hb)
  change W.card = 2 + f.extra a at hr
  omega

theorem outside_partition (z : V) :
    f.aOut z + f.zOut z + (f.outside z).card = 9 := by
  have hd : Disjoint (outN adj z ∩ f.A) (outN adj z ∩ f.Z) :=
    f.disj.mono inter_subset_right inter_subset_right
  have hc := card_union_of_disjoint hd
  rw [← inter_union_distrib_left] at hc
  have hp := card_sdiff_add_card_inter (outN adj z) (f.A ∪ f.Z)
  rw [H.regular] at hp
  dsimp [aOut, zOut, outside]
  omega

omit H in
theorem head_capture (a : V) (ha : a ∈ f.A) (z : V) (haz : adj a z) :
    (f.inside a).card + (f.outside z).card ≤ (second adj a).card := by
  have ho : f.outside z ⊆ second adj a := by
    intro x hx
    have hxnot := (mem_sdiff.mp hx).2
    have hxA : x ∉ f.A := fun h => hxnot (mem_union_left _ h)
    have hax : ¬ adj a x := by
      intro h
      exact hxnot (f.headsA a ha (by simpa using h))
    refine (mem_second adj a x).mpr ⟨?_, hax, z, haz, ?_⟩
    · intro he
      subst x
      exact hxA ha
    · exact (mem_outN adj z x).mp (mem_sdiff.mp hx).1
  have hd : Disjoint (f.inside a) (f.outside z) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact (mem_sdiff.mp hx').2 (mem_inter.mp hx).2
  have hs : f.inside a ∪ f.outside z ⊆ second adj a :=
    union_subset inter_subset_left ho
  have hc := card_le_card hs
  rw [card_union_of_disjoint hd] at hc
  exact hc

theorem head_deficit (a : V) (ha : a ∈ f.A) (z : V) (haz : adj a z) (t : ℕ)
    (hp : f.aOut z + f.zOut z + t ≤ (f.inside a).card) :
    (inN adj a).card + t ≤ 8 := by
  have hc := f.head_capture a ha z haz
  have ho := f.outside_partition H z
  have hb := H.bad a
  omega

end Frame
end CH.CompromiseNineFrame

#print axioms CH.CompromiseNineFrame.Frame.total_le_eleven
#print axioms CH.CompromiseNineFrame.Frame.return_bound
#print axioms CH.CompromiseNineFrame.Frame.head_deficit
