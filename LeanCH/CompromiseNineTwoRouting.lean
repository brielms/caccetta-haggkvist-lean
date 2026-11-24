module

public import LeanCH.CompromiseNineTwoHigh

set_option linter.style.header false

/-! Routing lemmas for the remaining degree-nine two-exception cases. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem inside_one_more (a : V) (ha : a ∈ f.A) (x : V)
    (hx : x ∈ f.missing a) (hxg : x ∉ f.good) (hxs : x ∈ second adj a) :
    3 + (f.missing a ∩ f.good).card ≤ (f.inside a).card + (f.extra a + 1) / 3 := by
  have hs : insert x (f.missing a ∩ f.good) ⊆ f.seenMissing a := by
    intro z hz
    rcases mem_insert.mp hz with hzx | hz
    · subst z
      exact mem_inter.mpr ⟨hx, hxs⟩
    · exact mem_inter.mpr ⟨(mem_inter.mp hz).1, f.good_missing_reached H a ha z hz⟩
  have hc := card_le_card hs
  rw [card_insert_of_notMem (by simp [hxg])] at hc
  have hp := f.inside_partition a
  have hi := f.internal_second_lower H a ha
  omega

theorem two_some_omission_le_five (hX : f.exceptional.card = 2) :
    ∃ x ∈ f.exceptional, f.omission x ≤ 5 := by
  by_contra hn
  have hm (x : V) (hx : x ∈ f.exceptional) : 6 ≤ f.omission x := by
    have hh : ¬ f.omission x ≤ 5 := fun h => hn ⟨x, hx, h⟩
    omega
  have hs := sum_le_sum hm
  simp only [sum_const, smul_eq_mul, hX] at hs
  have hp := f.budget_partition
  have hb := f.total_le_eleven H
  omega

theorem two_full_missing_of_bound (hX : f.exceptional.card = 2)
    (a : V) (ha : a ∈ f.A) (hb : 7 < f.goodBudget + f.extra a + 3) :
    2 + f.extra a ≤ (f.inside a).card + (f.extra a + 1) / 3 := by
  apply f.inside_full_missing H a ha
  intro z hz
  by_cases hzg : z ∈ f.good
  · exact f.good_missing_reached H a ha z (mem_inter.mpr ⟨hz, hzg⟩)
  · have hzX : z ∈ f.exceptional := mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, hzg⟩
    have hd := f.two_exception_omission H hX z hzX
    exact f.missing_reached H a ha z hz (by omega)

theorem two_four_head_routing (hX : f.exceptional.card = 2)
    (a : V) (ha : a ∈ f.A) (hb : (f.missing a ∩ f.good).card = 1)
    (hB : f.goodBudget ≤ 2)
    (hret : ∀ g ∈ f.good \ f.missing a, 3 ≤ f.zOut g) :
    ∀ x ∈ f.missing a ∩ f.exceptional, x ∈ second adj a := by
  have hG : f.good.card = 5 := by have := f.good_exceptional_card; omega
  have hT : (f.good \ f.missing a).card = 4 := by
    have := f.good_head_card a
    omega
  intro x hx
  have hxM := (mem_inter.mp hx).1
  have hxX := (mem_inter.mp hx).2
  by_contra hxs
  have avoids (g : V) (hg : g ∈ f.good \ f.missing a) : ¬ adj g x := by
    intro hgx
    have hag := ((f.mem_good_head a g).mp hg).2
    have hxa : x ≠ a := by
      intro heq
      subst x
      exact disjoint_left.mp f.disj ha (f.exceptional_sub hxX)
    exact hxs ((mem_second adj a x).mpr ⟨hxa, by simpa using (mem_sdiff.mp hxM).2,
      g, hag, hgx⟩)
  have hmin (g : V) (hg : g ∈ f.good \ f.missing a) :
      2 ≤ (outN adj g ∩ f.good).card := by
    have hs : outN adj g ∩ f.exceptional ⊆ f.exceptional.erase x := by
      intro z hz
      refine mem_erase.mpr ⟨?_, (mem_inter.mp hz).2⟩
      intro heq
      subst z
      exact avoids g hg (by simpa using (mem_inter.mp hz).1)
    have hc := card_le_card hs
    rw [card_erase_of_mem hxX, hX] at hc
    have split : f.zOut g = (outN adj g ∩ f.good).card +
        (outN adj g ∩ f.exceptional).card := by
      rw [← card_union_of_disjoint (f.good_exceptional_disjoint.mono
        inter_subset_right inter_subset_right), ← inter_union_distrib_left,
        f.good_exceptional_union]
      rfl
    have := hret g hg
    omega
  have hs := sum_le_sum hmin
  simp only [sum_const, smul_eq_mul, hT] at hs
  have ht : (∑ g ∈ f.good \ f.missing a, (outN adj g ∩ f.good).card) ≤
      ∑ g ∈ f.good, (outN adj g ∩ f.good).card := sum_le_sum_of_subset sdiff_subset
  have hi := f.good_incoming_capacity H
  omega

theorem two_good_heads_small (a : V) (hheads : 2 ≤ (f.good \ f.missing a).card) :
    ∃ g ∈ f.good, adj a g ∧ f.zOut g ≤ 5 := by
  by_contra hn
  have complete (g : V) (hg : g ∈ f.good \ f.missing a) :
      outN adj g ∩ f.Z = f.Z.erase g := by
    have hgZ := f.good_sub (mem_sdiff.mp hg).1
    have hq := f.zOut_le_six H g hgZ
    have hbig : ¬ f.zOut g ≤ 5 := fun h => hn ⟨g, (mem_sdiff.mp hg).1,
      ((f.mem_good_head a g).mp hg).2, h⟩
    have hs : outN adj g ∩ f.Z ⊆ f.Z.erase g := by
      intro z hz
      refine mem_erase.mpr ⟨?_, (mem_inter.mp hz).2⟩
      intro heq
      subst z
      exact H.loopless g (by simpa using (mem_inter.mp hz).1)
    apply eq_of_subset_of_card_le hs
    rw [card_erase_of_mem hgZ, f.cardZ]
    change 7 - 1 ≤ f.zOut g
    omega
  obtain ⟨g, hg, l, hl, hgl⟩ := one_lt_card.mp (show 1 < (f.good \ f.missing a).card by omega)
  have hag : adj g l := by
    have hm : l ∈ f.Z.erase g := mem_erase.mpr ⟨Ne.symm hgl, f.good_sub (mem_sdiff.mp hl).1⟩
    rw [← complete g hg] at hm
    simpa using (mem_inter.mp hm).1
  have hga : adj l g := by
    have hm : g ∈ f.Z.erase l := mem_erase.mpr ⟨hgl, f.good_sub (mem_sdiff.mp hg).1⟩
    rw [← complete l hl] at hm
    simpa using (mem_inter.mp hm).1
  exact H.noDigon g l hag hga

theorem two_four_heads_force_low_exceptions (hX : f.exceptional.card = 2)
    (hgood : ∀ g ∈ f.good, 2 ≤ f.zOut g)
    (a : V) (hb : (f.missing a ∩ f.good).card = 1)
    (hret : ∀ g ∈ f.good \ f.missing a, 4 ≤ f.zOut g) :
    ∀ x ∈ f.exceptional, f.zOut x ≤ 1 := by
  have hG : f.good.card = 5 := by have := f.good_exceptional_card; omega
  have hB : f.goodBudget ≤ 3 := by have := f.budget_bound H; omega
  have hT : (f.good \ f.missing a).card = 4 := by
    have := f.good_head_card a
    omega
  have hs := sum_le_sum hret
  simp only [sum_const, smul_eq_mul, hT] at hs
  have hm := sum_le_sum (fun g (hg : g ∈ f.good ∩ f.missing a) => hgood g (mem_inter.mp hg).1)
  rw [inter_comm f.good (f.missing a)] at hm
  simp only [sum_const, smul_eq_mul, hb] at hm
  have hp : (∑ g ∈ f.good \ f.missing a, f.zOut g) +
      (∑ g ∈ f.missing a ∩ f.good, f.zOut g) = ∑ g ∈ f.good, f.zOut g := by
    rw [← sum_union (disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h).2 (mem_inter.mp h').1))]
    congr 1
    ext g
    simp only [mem_union, mem_sdiff, mem_inter]
    tauto
  have hc := f.good_outgoing_capacity H
  rw [hG, hX] at hc
  have hzero : (∑ x ∈ f.exceptional, (outN adj x ∩ f.good).card) = 0 := by omega
  intro x hx
  have hxzero : (outN adj x ∩ f.good).card = 0 := by
    have hi := single_le_sum (f := fun x => (outN adj x ∩ f.good).card)
      (fun _ _ => Nat.zero_le _) hx
    omega
  have houtzero : outN adj x ∩ f.good = ∅ := card_eq_zero.mp hxzero
  have hsub : outN adj x ∩ f.Z ⊆ f.exceptional.erase x := by
    intro z hz
    refine mem_erase.mpr ⟨?_, mem_sdiff.mpr ⟨(mem_inter.mp hz).2, ?_⟩⟩
    · intro heq
      subst z
      exact H.loopless x (by simpa using (mem_inter.mp hz).1)
    · intro hzg
      have hm : z ∈ outN adj x ∩ f.good := mem_inter.mpr ⟨(mem_inter.mp hz).1, hzg⟩
      rw [houtzero] at hm
      exact notMem_empty z hm
  have hh := card_le_card hsub
  rw [card_erase_of_mem hx, hX] at hh
  exact hh

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.two_four_head_routing
#print axioms CH.CompromiseNineFrame.Frame.two_four_heads_force_low_exceptions
