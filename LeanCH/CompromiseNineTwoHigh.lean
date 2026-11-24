module

public import LeanCH.CompromiseNineOne

set_option linter.style.header false

/-! Degree-nine local case: two exceptions and all good Z-degrees at least three. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem two_exception_omission (hX : f.exceptional.card = 2)
    (x : V) (hx : x ∈ f.exceptional) : f.goodBudget + f.omission x + 4 ≤ 11 := by
  have he : (f.exceptional.erase x).card = 1 := by rw [card_erase_of_mem hx, hX]
  have hs := sum_le_sum (fun y (hy : y ∈ f.exceptional.erase x) =>
    f.omission_exceptional y (mem_erase.mp hy).2)
  simp only [sum_const, smul_eq_mul, he, one_mul] at hs
  have hsum : (∑ y ∈ f.exceptional.erase x, f.omission y) + f.omission x =
      ∑ y ∈ f.exceptional, f.omission y := sum_erase_add _ _ hx
  have hp := f.budget_partition
  have hb := f.total_le_eleven H
  omega

theorem two_high_all_deficient (hX : f.exceptional.card = 2)
    (hgood : ∀ g ∈ f.good, 3 ≤ f.zOut g) :
    ∀ a ∈ f.A, (inN adj a).card ≤ 8 := by
  have hG : f.good.card = 5 := by have := f.good_exceptional_card; omega
  have hB : f.goodBudget ≤ 3 := by have := f.budget_bound H; omega
  have hg2 : ∀ g ∈ f.good, 2 ≤ f.zOut g := fun g hg => by have := hgood g hg; omega
  have split (g : V) : f.zOut g = (outN adj g ∩ f.good).card +
      (outN adj g ∩ f.exceptional).card := by
    rw [← card_union_of_disjoint (f.good_exceptional_disjoint.mono
      inter_subset_right inter_subset_right), ← inter_union_distrib_left,
      f.good_exceptional_union]
    rfl
  have minG (g : V) (hg : g ∈ f.good) : 1 ≤ (outN adj g ∩ f.good).card := by
    have hs := split g
    have hc := card_le_card (inter_subset_right : outN adj g ∩ f.exceptional ⊆ f.exceptional)
    have hm := hgood g hg
    omega
  let L := f.good.filter (fun g => (outN adj g ∩ f.good).card = 1)
  have five := five_structure adj H.loopless H.noDigon H.noTri H.small f.good hG minG
  change 3 ≤ L.card ∧ ∀ g ∈ f.good \ L, ∃ l ∈ L, adj g l at five
  have complete (l : V) (hl : l ∈ L) : f.zOut l = 3 ∧ f.exceptional ⊆ outN adj l := by
    have hs := split l
    have hlg := (mem_filter.mp hl).1
    have hone := (mem_filter.mp hl).2
    have hm := hgood l hlg
    have hc := card_le_card (inter_subset_right : outN adj l ∩ f.exceptional ⊆ f.exceptional)
    have heq : outN adj l ∩ f.exceptional = f.exceptional :=
      eq_of_subset_of_card_le inter_subset_right (by omega)
    refine ⟨by omega, ?_⟩
    rw [← heq]
    exact inter_subset_left
  have avoids (x : V) (hx : x ∈ f.exceptional) (g : V) (hg : g ∈ f.good) : ¬ adj x g := by
    by_cases hgl : g ∈ L
    · exact H.noDigon g x (by simpa using (complete g hgl).2 hx)
    · obtain ⟨l, hl, hgl'⟩ := five.2 g (mem_sdiff.mpr ⟨hg, hgl⟩)
      exact H.noTri g l x hgl' (by simpa using (complete l hl).2 hx)
  have qlow (x : V) (hx : x ∈ f.exceptional) : f.zOut x ≤ 1 := by
    have hs : outN adj x ∩ f.Z ⊆ f.exceptional.erase x := by
      intro z hz
      refine mem_erase.mpr ⟨?_, mem_sdiff.mpr ⟨(mem_inter.mp hz).2, ?_⟩⟩
      · intro he
        subst z
        exact H.loopless x (by simpa using (mem_inter.mp hz).1)
      · intro hzg
        exact avoids x hx z hzg (by simpa using (mem_inter.mp hz).1)
    have hc := card_le_card hs
    rw [card_erase_of_mem hx, hX] at hc
    exact hc
  have rlow (x : V) (hx : x ∈ f.exceptional) : f.aOut x ≤ 1 := by
    by_cases hr : 1 ≤ f.aOut x
    · obtain ⟨a, ha⟩ := card_pos.mp hr
      have hxa : adj x a := by simpa using (mem_inter.mp ha).1
      have haA := (mem_inter.mp ha).2
      have hsub : L ⊆ f.missing a ∩ f.good := by
        intro l hl
        refine mem_inter.mpr ⟨mem_sdiff.mpr ⟨f.good_sub (mem_filter.mp hl).1, ?_⟩,
          (mem_filter.mp hl).1⟩
        intro hal
        exact H.noTri a l x (by simpa using hal)
          (by simpa using (complete l hl).2 hx) hxa
      have hc := card_le_card hsub
      have hb := f.budget_missed_good a haA
      have hd := f.two_exception_omission H hX x hx
      exact f.return_cap_four H x (f.exceptional_sub hx) (by omega)
    · omega
  intro a ha
  let b := (f.missing a ∩ f.good).card
  have hb := f.budget_missed_good a ha
  change b ≤ f.goodBudget at hb
  have he := f.extra_le_six H a ha
  have hp := f.inside_ge_two H hg2 a ha
  have hpart := f.missing_partition a
  have hheads := f.good_head_card a
  change (f.good \ f.missing a).card + b = f.good.card at hheads
  have captureG (g : V) (hg : g ∈ f.good) (hag : adj a g)
      (hq : f.zOut g ≤ (f.inside a).card) : (inN adj a).card ≤ 8 := by
    have hc := f.head_deficit H a ha g hag 0 (by rw [f.good_aOut_zero H g hg]; omega)
    omega
  by_cases he0 : f.extra a = 0
  · obtain ⟨x, hx⟩ := card_pos.mp (show 0 < f.exceptional.card by omega)
    have hag : adj a x := by
      by_contra hn
      have hxm : x ∈ f.missing a := mem_sdiff.mpr ⟨f.exceptional_sub hx, by simpa using hn⟩
      have hm : f.missing a = ∅ := card_eq_zero.mp he0
      rw [hm] at hxm
      exact notMem_empty x hxm
    have hq := qlow x hx
    have hr := rlow x hx
    have hh := f.head_deficit H a ha x hag 0 (by omega)
    omega
  · by_cases hb2 : b ≤ 2
    · have hs : L ∩ f.missing a ⊆ f.missing a ∩ f.good := by
        intro l hl
        exact mem_inter.mpr ⟨(mem_inter.mp hl).2, (mem_filter.mp (mem_inter.mp hl).1).1⟩
      have hc := card_le_card hs
      have hlp := card_sdiff_add_card_inter L (f.missing a)
      obtain ⟨l, hl⟩ := card_pos.mp (show 0 < (L \ f.missing a).card by
        change (L ∩ f.missing a).card ≤ b at hc
        have := five.1
        omega)
      have hlL := (mem_sdiff.mp hl).1
      have hlg := (mem_filter.mp hlL).1
      have hal := ((f.mem_good_head a l).mp
        (mem_sdiff.mpr ⟨hlg, (mem_sdiff.mp hl).2⟩)).2
      have hfull := f.inside_full_missing H a ha (by
        intro z hz
        by_cases hzg : z ∈ f.good
        · exact f.good_missing_reached H a ha z (mem_inter.mpr ⟨hz, hzg⟩)
        · have hzX := mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, hzg⟩
          have hza : z ≠ a := by
            intro heq
            subst z
            exact disjoint_left.mp f.disj ha (mem_sdiff.mp hz).1
          refine (mem_second adj a z).mpr ⟨hza, ?_, l, hal, ?_⟩
          · simpa using (mem_sdiff.mp hz).2
          · simpa using (complete l hlL).2 hzX)
      have hq := (complete l hlL).1
      exact captureG l hlg hal (by omega)
    · have hb3 : b = 3 := by omega
      have hfull := f.inside_full_missing H a ha (by
        intro z hz
        by_cases hzg : z ∈ f.good
        · exact f.good_missing_reached H a ha z (mem_inter.mpr ⟨hz, hzg⟩)
        · have hzX : z ∈ f.exceptional := mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, hzg⟩
          have hd := f.two_exception_omission H hX z hzX
          have hep : 3 ≤ f.extra a := by
            have := card_le_card (inter_subset_left : f.missing a ∩ f.good ⊆ f.missing a)
            change b ≤ f.extra a at this
            omega
          exact f.missing_reached H a ha z hz (by omega))
      obtain ⟨g, hg, hag, hq⟩ := f.good_small_head_bound H a 4 3
        (fun g hg => hgood g (mem_inter.mp hg).1) (by
          rw [hG, hX]
          change 5 * (1 + 2) + f.goodBudget < 3 * b + 5 * (f.good \ f.missing a).card
          omega)
      have hep : 3 ≤ f.extra a := by
        have := card_le_card (inter_subset_left : f.missing a ∩ f.good ⊆ f.missing a)
        change b ≤ f.extra a at this
        omega
      exact captureG g hg hag (by omega)

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.two_high_all_deficient
