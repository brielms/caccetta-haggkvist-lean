module

public import LeanCH.CompromiseNineTwoRouting

set_option linter.style.header false

/-! Degree-nine local case: two exceptions and a good vertex of Z-degree two. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem two_low_all_deficient (hX : f.exceptional.card = 2)
    (hgood : ∀ g ∈ f.good, 2 ≤ f.zOut g)
    (hexTwo : ∃ g ∈ f.good, f.zOut g = 2)
    (hexLow : ∃ x ∈ f.exceptional, f.zOut x ≤ 1) :
    ∀ a ∈ f.A, (inN adj a).card ≤ 8 := by
  have hG : f.good.card = 5 := by have := f.good_exceptional_card; omega
  have hB : f.goodBudget ≤ 3 := by have := f.budget_bound H; omega
  intro a ha
  have hp := f.inside_ge_two H hgood a ha
  have captureG (g : V) (hg : g ∈ f.good) (hag : adj a g)
      (hq : f.zOut g ≤ (f.inside a).card) : (inN adj a).card ≤ 8 := by
    have hc := f.head_deficit H a ha g hag 0 (by rw [f.good_aOut_zero H g hg]; omega)
    omega
  by_cases hsees : ∃ g ∈ f.good, adj a g ∧ f.zOut g = 2
  · obtain ⟨g, hg, hag, hq⟩ := hsees
    exact captureG g hg hag (by omega)
  have hret (g : V) (hg : g ∈ f.good \ f.missing a) : 3 ≤ f.zOut g := by
    obtain ⟨hgg, hag⟩ := (f.mem_good_head a g).mp hg
    have hm := hgood g hgg
    have hn : f.zOut g ≠ 2 := fun hh => hsees ⟨g, hgg, hag, hh⟩
    omega
  let b := (f.missing a ∩ f.good).card
  let t := (f.missing a ∩ f.exceptional).card
  have hb1 : 1 ≤ b := by
    obtain ⟨g, hg, hq⟩ := hexTwo
    have hnag : ¬ adj a g := fun hh => hsees ⟨g, hg, hh, hq⟩
    exact card_pos.mpr ⟨g, mem_inter.mpr ⟨
      mem_sdiff.mpr ⟨f.good_sub hg, by simpa using hnag⟩, hg⟩⟩
  have ht : t ≤ 2 := by
    have hc := card_le_card (inter_subset_right : f.missing a ∩ f.exceptional ⊆ f.exceptional)
    omega
  have hbB : b ≤ f.goodBudget := f.budget_missed_good a ha
  have hpart : b + t = f.extra a := f.missing_partition a
  have hheads : (f.good \ f.missing a).card + b = 5 := by
    have := f.good_head_card a
    omega
  have hl : 2 + b ≤ (f.inside a).card + (f.extra a + 1) / 3 := f.inside_lower H a ha
  have seesX (ht0 : t = 0) (x : V) (hx : x ∈ f.exceptional) : adj a x := by
    by_contra hn
    have hxM : x ∈ f.missing a := mem_sdiff.mpr ⟨f.exceptional_sub hx, by simpa using hn⟩
    have hxT : x ∈ f.missing a ∩ f.exceptional := mem_inter.mpr ⟨hxM, hx⟩
    have hh : (f.missing a ∩ f.exceptional).card = 0 := ht0
    rw [card_eq_zero.mp hh] at hxT
    exact notMem_empty x hxT
  have full (hnum : 7 < f.goodBudget + f.extra a + 3) :=
    f.two_full_missing_of_bound H hX a ha hnum
  by_cases hsmall : b = 1 ∧ f.goodBudget ≤ 2
  · obtain ⟨hb, hbb⟩ := hsmall
    obtain ⟨g, hg, hag, hq⟩ := f.good_small_head H hgood a 3 (by
      rw [hG, hX]
      change 5 * (1 + 2) + f.goodBudget < 2 * b + 4 * (f.good \ f.missing a).card
      omega)
    by_cases ht0 : t = 0
    · exact captureG g hg hag (by omega)
    · by_cases ht1 : t = 1
      · have hfull := f.inside_full_missing H a ha (by
          intro z hz
          by_cases hzg : z ∈ f.good
          · exact f.good_missing_reached H a ha z (mem_inter.mpr ⟨hz, hzg⟩)
          · exact f.two_four_head_routing H hX a ha hb hbb hret z
              (mem_inter.mpr ⟨hz, mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, hzg⟩⟩))
        exact captureG g hg hag (by omega)
      · obtain ⟨x, hx, hdx⟩ := f.two_some_omission_le_five H hX
        have heq : f.missing a ∩ f.exceptional = f.exceptional :=
          eq_of_subset_of_card_le inter_subset_right (by change f.exceptional.card ≤ t; omega)
        have hxM := (mem_inter.mp (show x ∈ f.missing a ∩ f.exceptional by rw [heq]; exact hx)).1
        have hxs := f.missing_reached H a ha x hxM (by omega)
        have hmore := f.inside_one_more H a ha x hxM (mem_sdiff.mp hx).2 hxs
        change 3 + b ≤ (f.inside a).card + (f.extra a + 1) / 3 at hmore
        exact captureG g hg hag (by omega)
  · have hB2 : 2 ≤ f.goodBudget := by omega
    by_cases ht0 : t = 0
    · obtain ⟨x, hx, hqx⟩ := hexLow
      have hd := f.two_exception_omission H hX x hx
      have hr := f.return_cap_five H x (f.exceptional_sub hx) (by omega)
      have hh := f.head_deficit H a ha x (seesX ht0 x hx) 0 (by omega)
      omega
    · have hfull := full (by omega)
      by_cases hb2 : b = 2
      · obtain ⟨g, hg, hag, hq⟩ := f.good_small_head H hgood a 4 (by
          rw [hG, hX]
          change 5 * (1 + 2) + f.goodBudget < 2 * b + 5 * (f.good \ f.missing a).card
          omega)
        exact captureG g hg hag (by omega)
      · by_cases hb3 : b = 3
        · obtain ⟨g, hg, hag, hq⟩ := f.two_good_heads_small H a (by omega)
          exact captureG g hg hag (by omega)
        · have hb : b = 1 := by omega
          have hBeq : f.goodBudget = 3 := by omega
          by_cases ht2 : t = 2
          · obtain ⟨g, hg, hag, hq⟩ := f.good_small_head H hgood a 4 (by
              rw [hG, hX]
              change 5 * (1 + 2) + f.goodBudget < 2 * b + 5 * (f.good \ f.missing a).card
              omega)
            exact captureG g hg hag (by omega)
          · have ht1 : t = 1 := by omega
            by_cases hsmallhead : ∃ g ∈ f.good, adj a g ∧ f.zOut g ≤ 3
            · obtain ⟨g, hg, hag, hq⟩ := hsmallhead
              exact captureG g hg hag (by omega)
            · have hret4 (g : V) (hg : g ∈ f.good \ f.missing a) : 4 ≤ f.zOut g := by
                obtain ⟨hgg, hag⟩ := (f.mem_good_head a g).mp hg
                have hn : ¬ f.zOut g ≤ 3 := fun hh => hsmallhead ⟨g, hgg, hag, hh⟩
                omega
              have hlow := f.two_four_heads_force_low_exceptions H hX hgood a hb hret4
              have hcut := card_sdiff_add_card_inter f.exceptional (f.missing a)
              rw [inter_comm f.exceptional (f.missing a)] at hcut
              obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (f.exceptional \ f.missing a).card by
                change (f.exceptional \ f.missing a).card + t = f.exceptional.card at hcut
                omega)
              have hxX := (mem_sdiff.mp hx).1
              have hag : adj a x := by
                by_contra hn
                exact (mem_sdiff.mp hx).2 (mem_sdiff.mpr ⟨f.exceptional_sub hxX, by simpa using hn⟩)
              have hd := f.two_exception_omission H hX x hxX
              have hr := f.return_cap_four H x (f.exceptional_sub hxX) (by omega)
              have hq := hlow x hxX
              have hh := f.head_deficit H a ha x hag 0 (by omega)
              omega

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.two_low_all_deficient
