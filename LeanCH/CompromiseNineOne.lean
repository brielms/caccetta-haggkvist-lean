module

public import LeanCH.CompromiseNineSaturated

set_option linter.style.header false

/-! Degree-nine local case with exactly one exceptional vertex. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem one_exception_two_good_twos (x : V) (hX : f.exceptional = {x})
    (hgood : ∀ g ∈ f.good, 2 ≤ f.zOut g) :
    2 ≤ (f.good.filter (fun g => f.zOut g = 2)).card := by
  have hXcard : f.exceptional.card = 1 := by rw [hX]; simp
  have hG : f.good.card = 6 := by have := f.good_exceptional_card; omega
  have minG (g : V) (hg : g ∈ f.good) : 1 ≤ (outN adj g ∩ f.good).card := by
    have hb := degree_bound (outN adj g ∩ f.Z) f.good f.exceptional (by
      intro z hz
      rw [f.good_exceptional_union]
      exact (mem_inter.mp hz).2)
    have he : (outN adj g ∩ f.Z) ∩ f.good = outN adj g ∩ f.good := by
      ext z
      simp only [mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, f.good_sub h.2⟩, h.2⟩⟩
    rw [he] at hb
    have := hgood g hg
    change 2 ≤ (outN adj g ∩ f.Z).card at this
    omega
  have hl := six_two_degree_one adj H.loopless H.noDigon H.noTri H.small f.good hG minG
  have hs : f.good.filter (fun g => (outN adj g ∩ f.good).card = 1) ⊆
      f.good.filter (fun g => f.zOut g = 2) := by
    intro g hg
    obtain ⟨hgg, hone⟩ := mem_filter.mp hg
    have hsplit : f.zOut g = (outN adj g ∩ f.good).card +
        (outN adj g ∩ f.exceptional).card := by
      rw [← card_union_of_disjoint (f.good_exceptional_disjoint.mono
        inter_subset_right inter_subset_right), ← inter_union_distrib_left,
        f.good_exceptional_union]
      rfl
    have hb := card_le_card (inter_subset_right : outN adj g ∩ f.exceptional ⊆ f.exceptional)
    have hm := hgood g hgg
    exact mem_filter.mpr ⟨hgg, by omega⟩
  exact hl.trans (card_le_card hs)

theorem one_exception_all_deficient (x : V) (hX : f.exceptional = {x})
    (hgood : ∀ g ∈ f.good, 2 ≤ f.zOut g) (hqx : f.zOut x ≤ 1) :
    ∀ a ∈ f.A, (inN adj a).card ≤ 8 := by
  have hxX : x ∈ f.exceptional := by rw [hX]; simp
  have hxZ := f.exceptional_sub hxX
  have hXcard : f.exceptional.card = 1 := by rw [hX]; simp
  have hG : f.good.card = 6 := by have := f.good_exceptional_card; omega
  have hB : f.goodBudget ≤ 7 := by have := f.budget_bound H; omega
  have hbudget : f.goodBudget + f.omission x ≤ 11 := by
    have hp := f.budget_partition
    rw [hX, sum_singleton] at hp
    have := f.total_le_eleven H
    omega
  have htwos := f.one_exception_two_good_twos H x hX hgood
  intro a ha
  let b := (f.missing a ∩ f.good).card
  let t := (f.missing a ∩ f.exceptional).card
  have he := f.extra_le_six H a ha
  have hpart : b + t = f.extra a := f.missing_partition a
  have ht : t ≤ 1 := by
    have := card_le_card (inter_subset_right : f.missing a ∩ f.exceptional ⊆ f.exceptional)
    omega
  have hbB : b ≤ f.goodBudget := f.budget_missed_good a ha
  have hb6 : b ≤ 6 := by omega
  have hheads : (f.good \ f.missing a).card + b = 6 := by
    have := f.good_head_card a
    omega
  have hp := f.inside_ge_two H hgood a ha
  have hl : 2 + b ≤ (f.inside a).card + (f.extra a + 1) / 3 := f.inside_lower H a ha
  have captureG (g : V) (hg : g ∈ f.good) (hag : adj a g)
      (hq : f.zOut g ≤ (f.inside a).card) : (inN adj a).card ≤ 8 := by
    have hc := f.head_deficit H a ha g hag 0 (by rw [f.good_aOut_zero H g hg]; omega)
    omega
  have seesX (ht0 : t = 0) : adj a x := by
    by_contra hn
    have hxM : x ∈ f.missing a := mem_sdiff.mpr ⟨hxZ, by simpa using hn⟩
    have hxT : x ∈ f.missing a ∩ f.exceptional := mem_inter.mpr ⟨hxM, hxX⟩
    have hh : (f.missing a ∩ f.exceptional).card = 0 := ht0
    rw [card_eq_zero.mp hh] at hxT
    exact notMem_empty x hxT
  have full (hb4 : 4 ≤ b) (ht1 : t = 1) :
      2 + f.extra a ≤ (f.inside a).card + (f.extra a + 1) / 3 := by
    apply f.inside_full_missing H a ha
    intro z hz
    by_cases hzg : z ∈ f.good
    · exact f.good_missing_reached H a ha z (mem_inter.mpr ⟨hz, hzg⟩)
    · have hzX : z ∈ f.exceptional := mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, hzg⟩
      rw [hX, mem_singleton] at hzX
      subst z
      exact f.missing_reached H a ha x hz (by omega)
  by_cases hb1 : b ≤ 1
  · let L := f.good.filter (fun g => f.zOut g = 2)
    have hsub : L ∩ f.missing a ⊆ f.missing a ∩ f.good := by
      intro g hg
      exact mem_inter.mpr ⟨(mem_inter.mp hg).2, (mem_filter.mp (mem_inter.mp hg).1).1⟩
    have hc := card_le_card hsub
    have hsplit := card_sdiff_add_card_inter L (f.missing a)
    obtain ⟨g, hg⟩ := card_pos.mp (show 0 < (L \ f.missing a).card by
      change 2 ≤ L.card at htwos
      change (L ∩ f.missing a).card ≤ b at hc
      omega)
    obtain ⟨hgg, hq⟩ := mem_filter.mp (mem_sdiff.mp hg).1
    have hag := ((f.mem_good_head a g).mp
      (mem_sdiff.mpr ⟨hgg, (mem_sdiff.mp hg).2⟩)).2
    exact captureG g hgg hag (by omega)
  · by_cases hb2 : b = 2
    · obtain ⟨g, hg, hag, hq⟩ := f.good_small_head H hgood a 3 (by
        rw [hG, hXcard]
        change 6 * (1 + 1) + f.goodBudget < 2 * b + 4 * (f.good \ f.missing a).card
        omega)
      exact captureG g hg hag (by omega)
    · by_cases hb3 : b = 3
      · obtain ⟨g, hg, hag, hq⟩ := f.good_small_head H hgood a 4 (by
          rw [hG, hXcard]
          change 6 * (1 + 1) + f.goodBudget < 2 * b + 5 * (f.good \ f.missing a).card
          omega)
        exact captureG g hg hag (by omega)
      · by_cases hb4 : b = 4
        · obtain ⟨g, hg, hag, hq⟩ := f.good_small_head H hgood a 5 (by
            rw [hG, hXcard]
            change 6 * (1 + 1) + f.goodBudget < 2 * b + 6 * (f.good \ f.missing a).card
            omega)
          by_cases ht0 : t = 0
          · exact captureG g hg hag (by omega)
          · have hh := full (by omega) (by omega)
            exact captureG g hg hag (by omega)
        · by_cases ht0 : t = 0
          · have hadj := seesX ht0
            by_cases hb5 : b = 5
            · have hr := f.return_cap_six H x hxZ (by omega)
              have hc := f.head_deficit H a ha x hadj 0 (by omega)
              omega
            · have hr := f.return_cap_five H x hxZ (by omega)
              have hc := f.head_deficit H a ha x hadj 0 (by omega)
              omega
          · have hh := full (by omega) (by omega)
            have hhcard : 0 < (f.good \ f.missing a).card := by omega
            obtain ⟨g, hg⟩ := card_pos.mp hhcard
            obtain ⟨hgg, hag⟩ := (f.mem_good_head a g).mp hg
            have hq := f.zOut_le_six H g (f.good_sub hgg)
            exact captureG g hgg hag (by omega)

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.one_exception_all_deficient
