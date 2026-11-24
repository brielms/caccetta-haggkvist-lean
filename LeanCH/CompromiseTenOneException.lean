module

public import LeanCH.CompromiseTenOneCover

set_option linter.style.header false

/-! Closure of the single-exception ten/eight frame. Undercharging
would force the seven good columns into a rigid internal graph,
incompatible with the return path that undercharging also requires. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

omit H in
theorem one_good_seven (x : V) (single : f.exceptional = {x}) : f.good.card = 7 := by
  have subset : f.good ⊆ f.Z := filter_subset _ _
  have split := card_sdiff_of_subset subset
  have cap := card_le_card subset
  change f.exceptional.card = f.Z.card - f.good.card at split
  rw [single, card_singleton, f.cardZ] at split
  rw [f.cardZ] at cap
  omega

omit H in
theorem one_good_or_exception (x : V) (single : f.exceptional = {x})
    (z : V) (hz : z ∈ f.Z) : z ∈ f.good ∨ z = x := by
  by_cases good : z ∈ f.good
  · exact Or.inl good
  · have ex : z ∈ f.exceptional := mem_sdiff.mpr ⟨hz, good⟩
    rw [single, mem_singleton] at ex
    exact Or.inr ex

omit H in
theorem one_good_degree_bound (x : V) (single : f.exceptional = {x}) (z : V) :
    f.zOut z ≤ (outN adj z ∩ f.good).card + 1 := by
  have subset : outN adj z ∩ f.Z ⊆ f.good ∪ {x} := by
    intro b hb
    rcases f.one_good_or_exception x single b (mem_inter.mp hb).2 with good | equal
    · exact mem_union_left _ good
    · exact mem_union_right _ (mem_singleton.mpr equal)
  have bound := degree_bound (outN adj z ∩ f.Z) f.good {x} subset
  have equal : (outN adj z ∩ f.Z) ∩ f.good = outN adj z ∩ f.good := by
    ext b
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, (mem_filter.mp h.2).1⟩, h.2⟩⟩
  rw [equal, card_singleton] at bound
  exact bound

omit H in
theorem one_good_degree_eq (x : V) (single : f.exceptional = {x})
    (z : V) (misses : ¬ adj z x) : f.zOut z = (outN adj z ∩ f.good).card := by
  change (outN adj z ∩ f.Z).card = (outN adj z ∩ f.good).card
  apply congrArg Finset.card
  apply Subset.antisymm
  · intro b hb
    refine mem_inter.mpr ⟨(mem_inter.mp hb).1, ?_⟩
    rcases f.one_good_or_exception x single b (mem_inter.mp hb).2 with good | equal
    · exact good
    · subst b
      exact False.elim (misses ((mem_outN adj z x).mp (mem_inter.mp hb).1))
  · intro b hb
    exact mem_inter.mpr ⟨(mem_inter.mp hb).1, (mem_filter.mp (mem_inter.mp hb).2).1⟩

theorem undercharged_one_good_two (x : V) (single : f.exceptional = {x})
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) : f.goodTwos.Nonempty := by
  by_contra empty
  have minimum (z : V) (hz : z ∈ f.good) : 2 ≤ (outN adj z ∩ f.good).card := by
    have bound := f.one_good_degree_bound x single z
    have min := f.undercharged_good_minimum H under z hz
    have unequal : f.zOut z ≠ 2 := fun equal => empty ⟨z, mem_filter.mpr ⟨hz, equal⟩⟩
    omega
  have rigid := rigid_small adj H.loopless H.noDigon H.noTri H.small
    f.good 2 (by omega) (by omega) (by simpa using f.one_good_seven x single) minimum
  have parent (z : V) (hz : z ∈ f.good) : adj z x := by
    by_contra misses
    have equal := f.one_good_degree_eq x single z misses
    have two := (rigid z hz).1
    have inTwos : z ∈ f.goodTwos := mem_filter.mpr ⟨hz, by omega⟩
    exact empty ⟨z, inTwos⟩
  obtain ⟨a, _, _, z, hz, _, omitted, b, hb, zb⟩ := f.undercharged_return_path H under
  have notGood : z ∉ f.good := by intro good; have := (mem_filter.mp good).2; omega
  have ex : z ∈ f.exceptional := mem_sdiff.mpr ⟨hz, notGood⟩
  rw [single, mem_singleton] at ex
  subst z
  have subset : f.Z ⊆ f.missing b := by
    intro z hz
    refine mem_sdiff.mpr ⟨hz, ?_⟩
    intro outgoing
    have bz := (mem_outN adj b z).mp outgoing
    rcases f.one_good_or_exception x single z hz with good | equal
    · exact H.noTri x b z zb bz (parent z good)
    · subst z
      exact H.noDigon x b zb bz
  have lower := card_le_card subset
  rw [f.cardZ] at lower
  change 8 ≤ f.extra b at lower
  have upper := f.extra_le_seven H b hb
  omega

theorem one_exception_charge (x : V) (single : f.exceptional = {x}) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  by_contra failure
  have under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9 := by omega
  have two := f.undercharged_one_good_two H x single under
  have charge := f.one_good_two_charge H x single two
  omega

theorem undercharged_two_exceptions
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    2 ≤ f.exceptional.card ∧ f.exceptional.card ≤ 4 := by
  have lower := (f.undercharged_exceptional_card H under).1
  refine ⟨?_, f.exceptional_le_four H⟩
  by_contra small
  have one : f.exceptional.card = 1 := by omega
  obtain ⟨x, single⟩ := card_eq_one.mp one
  have charge := f.one_exception_charge H x single
  omega

omit H in
theorem exceptional_eq_filter : f.exceptional = f.Z.filter (fun z => 4 ≤ f.omission z) := by
  ext z
  constructor
  · intro hz
    have zZ := (mem_sdiff.mp hz).1
    refine mem_filter.mpr ⟨zZ, ?_⟩
    by_contra small
    exact (mem_sdiff.mp hz).2 (mem_filter.mpr ⟨zZ, by omega⟩)
  · intro hz
    refine mem_sdiff.mpr ⟨(mem_filter.mp hz).1, ?_⟩
    intro good
    have upper := (mem_filter.mp good).2
    have lower := (mem_filter.mp hz).2
    omega

end CH.CompromiseTenFrame.Frame

namespace CH.CompromiseTenOneException

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem residual_root (H : CH.CompromiseTenFrame.Ambient adj)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ y, (inN adj y).card = 11 ∧ (second adj y).card = 8 ∧
      (∑ a ∈ outN adj y, (10 - (inN adj a).card)) ≤ 9 ∧
      2 ≤ ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ∧
      ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ≤ 4 ∧
      ∃ a ∈ outN adj y, 10 ≤ (inN adj a).card ∧ ∃ z ∈ second adj y,
        adj a z ∧ 4 ≤ (outN adj y \ inN adj z).card ∧ ∃ b ∈ outN adj y, adj z b := by
  obtain ⟨y, eleven, eight, under⟩ := CH.CompromiseTenUndercharged.root adj H seymour
  let f := CH.CompromiseTenResidual.eightFrame adj H y eight
  have counts := f.undercharged_two_exceptions H under
  rw [f.exceptional_eq_filter] at counts
  refine ⟨y, eleven, eight, under, counts.1, counts.2, ?_⟩
  exact f.undercharged_return_path H under

theorem residual_root_from_induction
    (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 10 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card)
    (ihRev : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 10 →
      (∀ a ∈ S, r ≤ (inN adj a ∩ S).card) → 3 * r < S.card)
    (regular : ∀ v, (outN adj v).card = 10)
    (bad : ∀ v, (second adj v).card + (inN adj v).card ≤ 19)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ y, (inN adj y).card = 11 ∧ (second adj y).card = 8 ∧
      (∑ a ∈ outN adj y, (10 - (inN adj a).card)) ≤ 9 ∧
      2 ≤ ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ∧
      ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ≤ 4 ∧
      ∃ a ∈ outN adj y, 10 ≤ (inN adj a).card ∧ ∃ z ∈ second adj y,
        adj a z ∧ 4 ≤ (outN adj y \ inN adj z).card ∧ ∃ b ∈ outN adj y, adj z b := by
  have outFlip (v : V) : outN (fun u w => adj w u) v = inN adj v := by ext x; simp
  have reverse : SmallOut (fun u v => adj v u) := by
    apply CH.CompromiseTenLocal.small_of_induction
    intro S r hn hr hrTen minimum
    apply ihRev S r hn hr hrTen
    intro a ha
    simpa only [outFlip] using minimum a ha
  let H : CH.CompromiseTenFrame.Ambient adj := {
    loopless := loopless
    noDigon := noDigon
    noTri := noTri
    small := CH.CompromiseTenLocal.small_of_induction adj ih
    smallRev := reverse
    regular := regular
    bad := bad }
  exact residual_root adj H seymour

end CH.CompromiseTenOneException

#print axioms CH.CompromiseTenFrame.Frame.one_exception_charge
#print axioms CH.CompromiseTenFrame.Frame.undercharged_two_exceptions
#print axioms CH.CompromiseTenOneException.residual_root_from_induction
