module

public import LeanCH.CompromiseNineFrame

set_option linter.style.header false

/-! The degree-nine candidate: internal second neighbours and the low-good
case. These lemmas do not assert the full candidate dichotomy. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

@[expose] def seenMissing (f : Frame adj) (a : V) : Finset V :=
  f.missing a ∩ second adj a
@[expose] def thin (f : Frame adj) : Finset V :=
  f.A.filter (fun a => (f.inside a).card < 2)
@[expose] def commonMissing (f : Frame adj) : Finset V :=
  f.A.filter (fun a => ∀ z ∈ f.exceptional, ¬ adj a z)

variable (H : Ambient adj) (f : Frame adj)

theorem good_sub : f.good ⊆ f.Z := filter_subset _ _
theorem exceptional_sub : f.exceptional ⊆ f.Z := sdiff_subset

theorem good_exceptional_disjoint : Disjoint f.good f.exceptional :=
  disjoint_left.mpr (fun _ hg hx => (mem_sdiff.mp hx).2 hg)

theorem good_exceptional_union : f.good ∪ f.exceptional = f.Z := by
  exact union_sdiff_of_subset f.good_sub

theorem good_exceptional_card : f.good.card + f.exceptional.card = 7 := by
  rw [← card_union_of_disjoint f.good_exceptional_disjoint,
    f.good_exceptional_union, f.cardZ]

theorem missing_partition (a : V) :
    (f.missing a ∩ f.good).card + (f.missing a ∩ f.exceptional).card = f.extra a := by
  rw [← card_union_of_disjoint (f.good_exceptional_disjoint.mono
    inter_subset_right inter_subset_right), ← inter_union_distrib_left,
    f.good_exceptional_union]
  change ((f.Z \ outN adj a) ∩ f.Z).card = (f.Z \ outN adj a).card
  rw [inter_eq_left.mpr sdiff_subset]

theorem inside_partition (a : V) :
    (f.inside a).card = (second adj a ∩ f.A).card + (f.seenMissing a).card := by
  have hz : second adj a ∩ f.Z = f.seenMissing a := by
    ext x
    simp only [seenMissing, missing, mem_inter, mem_sdiff]
    constructor
    · intro h
      exact ⟨⟨h.2, by simpa using (mem_second adj a x).mp h.1 |>.2.1⟩, h.1⟩
    · exact fun h => ⟨h.2, h.1.1⟩
  have hd : Disjoint (second adj a ∩ f.A) (second adj a ∩ f.Z) :=
    f.disj.mono inter_subset_right inter_subset_right
  dsimp [inside]
  rw [inter_union_distrib_left, card_union_of_disjoint hd, hz]

include H

theorem inside_lower (a : V) (ha : a ∈ f.A) :
    2 + (f.missing a ∩ f.good).card ≤ (f.inside a).card + (f.extra a + 1) / 3 := by
  have hs : f.missing a ∩ f.good ⊆ f.seenMissing a := by
    intro g hg
    exact mem_inter.mpr ⟨(mem_inter.mp hg).1, f.good_missing_reached H a ha g hg⟩
  have hc := card_le_card hs
  have hi := f.internal_second_lower H a ha
  have hp := f.inside_partition a
  omega

theorem thin_shape (a : V) (ha : a ∈ f.thin) :
    f.extra a = 2 ∧ f.missing a = f.exceptional ∧ f.exceptional.card = 2 ∧
      f.seenMissing a = ∅ := by
  have haA := (mem_filter.mp ha).1
  have hp := (mem_filter.mp ha).2
  have he := f.extra_le_six H a haA
  have hX := f.exceptional_le_two H
  have hx := card_le_card (inter_subset_right : f.missing a ∩ f.exceptional ⊆ f.exceptional)
  have hpart := f.missing_partition a
  have hl := f.inside_lower H a haA
  have hi := f.internal_second_lower H a haA
  have hip := f.inside_partition a
  have he2 : f.extra a = 2 := by omega
  have hg0 : (f.missing a ∩ f.good).card = 0 := by omega
  have hseen0 : (f.seenMissing a).card = 0 := by omega
  have hX2 : f.exceptional.card = 2 := by omega
  have hsub : f.missing a ⊆ f.exceptional := by
    intro z hz
    refine mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, ?_⟩
    intro hzg
    have hz0 : z ∈ f.missing a ∩ f.good := mem_inter.mpr ⟨hz, hzg⟩
    rw [card_eq_zero.mp hg0] at hz0
    exact notMem_empty z hz0
  have heq : f.missing a = f.exceptional := eq_of_subset_of_card_le hsub (by
    change f.exceptional.card ≤ f.extra a
    omega)
  exact ⟨he2, heq, hX2, card_eq_zero.mp hseen0⟩

theorem common_missing_le_five (hX : f.exceptional.card = 2) :
    f.commonMissing.card ≤ 5 := by
  have hm (z : V) (hz : z ∈ f.exceptional) : f.commonMissing.card ≤ f.omission z := by
    apply card_le_card
    intro a ha
    obtain ⟨haA, haX⟩ := mem_filter.mp ha
    exact mem_sdiff.mpr ⟨haA, by simpa using haX z hz⟩
  have hs := sum_le_sum hm
  simp only [sum_const, smul_eq_mul, hX] at hs
  have ht : ∑ z ∈ f.exceptional, f.omission z ≤ f.total :=
    sum_le_sum_of_subset f.exceptional_sub
  have := f.total_le_eleven H
  omega

theorem thin_heads (a : V) (ha : a ∈ f.thin) :
    insert a (outN adj a ∩ f.A) = f.commonMissing := by
  obtain ⟨he, hM, hX, hseen⟩ := f.thin_shape H a ha
  have haA := (mem_filter.mp ha).1
  have hn (z : V) (hz : z ∈ f.exceptional) : ¬ adj a z := by
    have hm : z ∈ f.missing a := hM ▸ hz
    simpa using (mem_sdiff.mp hm).2
  have hsub : insert a (outN adj a ∩ f.A) ⊆ f.commonMissing := by
    intro b hb
    rcases mem_insert.mp hb with hba | hb
    · subst b
      exact mem_filter.mpr ⟨haA, hn⟩
    · refine mem_filter.mpr ⟨(mem_inter.mp hb).2, ?_⟩
      intro z hz hbz
      have hzM : z ∈ f.missing a := hM ▸ hz
      have hza : z ≠ a := by
        intro heq
        subst z
        exact disjoint_left.mp f.disj haA (f.exceptional_sub hz)
      have hzs : z ∈ f.seenMissing a := mem_inter.mpr ⟨hzM,
        (mem_second adj a z).mpr ⟨hza, hn z hz, b,
          by simpa using (mem_inter.mp hb).1, hbz⟩⟩
      rw [hseen] at hzs
      exact notMem_empty z hzs
  have hc : (insert a (outN adj a ∩ f.A)).card = 5 := by
    rw [card_insert_of_notMem (by simp [H.loopless])]
    have hr := f.row_counts H a haA
    change (outN adj a ∩ f.A).card = 2 + f.extra a at hr
    omega
  exact eq_of_subset_of_card_le hsub (by rw [hc]; exact f.common_missing_le_five H hX)

theorem thin_le_one : f.thin.card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  by_contra hne
  have habC : b ∈ insert a (outN adj a ∩ f.A) := by
    rw [f.thin_heads H a ha, ← f.thin_heads H b hb]
    exact mem_insert_self _ _
  have hbaC : a ∈ insert b (outN adj b ∩ f.A) := by
    rw [f.thin_heads H b hb, ← f.thin_heads H a ha]
    exact mem_insert_self _ _
  have hab : adj a b := by
    rcases mem_insert.mp habC with h | h
    · exact False.elim (hne h.symm)
    · simpa using (mem_inter.mp h).1
  have hba : adj b a := by
    rcases mem_insert.mp hbaC with h | h
    · exact False.elim (hne h)
    · simpa using (mem_inter.mp h).1
  exact H.noDigon a b hab hba

theorem good_aOut_zero (g : V) (hg : g ∈ f.good) : f.aOut g = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact f.good_avoids_A H g hg a (mem_inter.mp ha).2 (by simpa using (mem_inter.mp ha).1)

theorem low_good_five_deficient (g : V) (hg : g ∈ f.good) (hq : f.zOut g ≤ 1) :
    5 ≤ (f.A.filter (fun a => (inN adj a).card ≤ 7)).card := by
  let P := f.A ∩ inN adj g
  have hp : 6 ≤ P.card := by
    have hc := card_sdiff_add_card_inter f.A (inN adj g)
    change f.omission g + P.card = f.A.card at hc
    have hd := (mem_filter.mp hg).2
    rw [f.cardA] at hc
    omega
  have hthin := f.thin_le_one H
  have hcut := card_sdiff_add_card_inter P f.thin
  have hc := card_le_card (inter_subset_right : P ∩ f.thin ⊆ f.thin)
  have hmany : 5 ≤ (P \ f.thin).card := by omega
  have hs : P \ f.thin ⊆ f.A.filter (fun a => (inN adj a).card ≤ 7) := by
    intro a ha
    have haA := (mem_inter.mp (mem_sdiff.mp ha).1).1
    have hag : adj a g := by simpa using (mem_inter.mp (mem_sdiff.mp ha).1).2
    have hin : 2 ≤ (f.inside a).card := by
      by_contra hn
      exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨haA, by omega⟩)
    have hd := f.head_deficit H a haA g hag 1 (by
      rw [f.good_aOut_zero H g hg]
      omega)
    exact mem_filter.mpr ⟨haA, by omega⟩
  exact hmany.trans (card_le_card hs)

theorem inside_ge_two (hgood : ∀ g ∈ f.good, 2 ≤ f.zOut g)
    (a : V) (ha : a ∈ f.A) : 2 ≤ (f.inside a).card := by
  by_contra hn
  have hathin : a ∈ f.thin := mem_filter.mpr ⟨ha, by omega⟩
  obtain ⟨he, hM, hX, hseen⟩ := f.thin_shape H a hathin
  have hG : f.good.card = 5 := by have := f.good_exceptional_card; omega
  have seesG (g : V) (hg : g ∈ f.good) : adj a g := by
    by_contra hnag
    have hgM : g ∈ f.missing a := mem_sdiff.mpr ⟨f.good_sub hg, by simpa using hnag⟩
    rw [hM] at hgM
    exact (mem_sdiff.mp hgM).2 hg
  have avoidsX (g : V) (hg : g ∈ f.good) (z : V) (hz : z ∈ f.exceptional) : ¬ adj g z := by
    intro hgz
    have hzM : z ∈ f.missing a := hM ▸ hz
    have hza : z ≠ a := by
      intro heq
      subst z
      exact disjoint_left.mp f.disj ha (f.exceptional_sub hz)
    have haz : ¬ adj a z := by simpa using (mem_sdiff.mp hzM).2
    have hzs : z ∈ f.seenMissing a := mem_inter.mpr ⟨hzM,
      (mem_second adj a z).mpr ⟨hza, haz, g, seesG g hg, hgz⟩⟩
    rw [hseen] at hzs
    exact notMem_empty z hzs
  have minG (g : V) (hg : g ∈ f.good) : 2 ≤ (outN adj g ∩ f.good).card := by
    have hs : outN adj g ∩ f.Z ⊆ outN adj g ∩ f.good := by
      intro z hz
      refine mem_inter.mpr ⟨(mem_inter.mp hz).1, ?_⟩
      by_contra hnz
      exact avoidsX g hg z (mem_sdiff.mpr ⟨(mem_inter.mp hz).2, hnz⟩)
        (by simpa using (mem_inter.mp hz).1)
    exact (hgood g hg).trans (card_le_card hs)
  obtain ⟨g, hg, hsmall⟩ := H.small f.good (card_pos.mp (by omega)) (by omega)
  have := minG g hg
  rw [hG] at hsmall
  omega

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.thin_le_one
#print axioms CH.CompromiseNineFrame.Frame.low_good_five_deficient
#print axioms CH.CompromiseNineFrame.Frame.inside_ge_two
