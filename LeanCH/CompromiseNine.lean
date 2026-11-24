module

public import LeanCH.CompromiseNineTwoLow

set_option linter.style.header false

/-!
Unit-weight compromise at exact out-degree nine, conditional on the prompt's
small-set CH bounds (in both directions) and existence of a Seymour vertex.
No bound on the order or minimality assumption is used. This does not establish
the general CH conjecture or weighted compromise.
-/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal CH.CompromiseNineFrame
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

theorem local_dichotomy (H : Ambient adj) (f : Frame adj) :
    (∀ a ∈ f.A, (inN adj a).card ≤ 8) ∨
      5 ≤ (f.A.filter (fun a => (inN adj a).card ≤ 7)).card := by
  by_cases hl : ∃ g ∈ f.good, f.zOut g ≤ 1
  · obtain ⟨g, hg, hq⟩ := hl
    exact Or.inr (f.low_good_five_deficient H g hg hq)
  have hg2 (g : V) (hg : g ∈ f.good) : 2 ≤ f.zOut g := by
    have hn : ¬ f.zOut g ≤ 1 := fun hh => hl ⟨g, hg, hh⟩
    omega
  apply Or.inl
  by_cases hsat : ∀ z ∈ f.Z, 2 ≤ f.zOut z
  · exact f.saturated_all_deficient H hsat
  have hlow : ∃ x ∈ f.exceptional, f.zOut x ≤ 1 := by
    push Not at hsat
    obtain ⟨x, hx, hq⟩ := hsat
    have hxG : x ∉ f.good := fun hh => by have := hg2 x hh; omega
    exact ⟨x, mem_sdiff.mpr ⟨hx, hxG⟩, by omega⟩
  have hXpos : 1 ≤ f.exceptional.card := by
    obtain ⟨x, hx, _⟩ := hlow
    exact card_pos.mpr ⟨x, hx⟩
  have hXcap := f.exceptional_le_two H
  by_cases hXone : f.exceptional.card = 1
  · obtain ⟨x, hX⟩ := card_eq_one.mp hXone
    have hq : f.zOut x ≤ 1 := by
      obtain ⟨y, hy, hqy⟩ := hlow
      rw [hX, mem_singleton] at hy
      simpa [hy] using hqy
    exact f.one_exception_all_deficient H x hX hg2 hq
  have hXtwo : f.exceptional.card = 2 := by omega
  by_cases hg3 : ∀ g ∈ f.good, 3 ≤ f.zOut g
  · exact f.two_high_all_deficient H hXtwo hg3
  · have htwo : ∃ g ∈ f.good, f.zOut g = 2 := by
      push Not at hg3
      obtain ⟨g, hg, hq⟩ := hg3
      have := hg2 g hg
      exact ⟨g, hg, by omega⟩
    exact f.two_low_all_deficient H hXtwo hg2 htwo hlow

end CH.CompromiseNineFrame.Frame

namespace CH.CompromiseNine

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem small_out_of_induction
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 9 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card) : SmallOut adj := by
  intro S hn hs
  have hp := card_pos.mpr hn
  by_contra h
  have hm : ∀ a ∈ S, (S.card - 1) / 3 + 1 ≤ (outN adj a ∩ S).card := by
    intro a ha
    have hh : ¬ (outN adj a ∩ S).card ≤ (S.card - 1) / 3 := fun hc => h ⟨a, ha, hc⟩
    omega
  have := ih S ((S.card - 1) / 3 + 1) hn (by omega) (by omega) hm
  omega

theorem small_in_of_induction
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 9 →
      (∀ a ∈ S, r ≤ (inN adj a ∩ S).card) → 3 * r < S.card) : SmallIn adj := by
  intro S hn hs
  have hp := card_pos.mpr hn
  by_contra h
  have hm : ∀ a ∈ S, (S.card - 1) / 3 + 1 ≤ (inN adj a ∩ S).card := by
    intro a ha
    have hh : ¬ (inN adj a ∩ S).card ≤ (S.card - 1) / 3 := fun hc => h ⟨a, ha, hc⟩
    omega
  have := ih S ((S.card - 1) / 3 + 1) hn (by omega) (by omega) hm
  omega

theorem second_ge_seven (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (small : SmallOut adj) (regular : ∀ v, (outN adj v).card = 9) (v : V) :
    7 ≤ (second adj v).card := by
  obtain ⟨a, ha, hsmall⟩ := small (outN adj v)
    (card_pos.mp (by rw [regular]; omega)) (by rw [regular])
  have hb := degree_bound (outN adj a) (outN adj v) (second adj v)
    (heads_two_steps adj noDigon ha)
  rw [regular] at hb
  rw [regular] at hsmall
  omega

@[expose] def highFrame (H : Ambient adj) (v : V) (high : (inN adj v).card = 10) :
    Frame adj where
  A := outN adj v
  Z := second adj v
  cardA := H.regular v
  cardZ := by
    have := second_ge_seven adj H.noDigon H.small H.regular v
    have := H.bad v
    omega
  disj := by
    apply disjoint_left.mpr
    intro a ha hs
    exact ((mem_second adj v a).mp hs).2.1 (by simpa using ha)
  headsA := fun a ha => heads_two_steps adj H.noDigon ha
  reachedZ := by
    intro z hz
    obtain ⟨_, _, a, hva, haz⟩ := (mem_second adj v z).mp hz
    exact ⟨a, by simpa using hva, haz⟩

theorem high_head_charge (H : Ambient adj) (v : V) (high : (inN adj v).card = 10) :
    9 ≤ ∑ a ∈ outN adj v, CH.CompromiseTransport.deficit adj 9 a := by
  have hd := (highFrame adj H v high).local_dichotomy H
  apply CH.CompromiseTransport.nine_charge_of_dichotomy adj v (H.regular v)
  have heq : outN adj v ∩ univ.filter (fun a => (inN adj a).card ≤ 7) =
      (outN adj v).filter (fun a => (inN adj a).card ≤ 7) := by
    ext a
    simp
  rw [heq]
  exact hd

/-- Full conditional unit compromise at exact out-degree nine. -/
theorem compromise_nine (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (smallRev : SmallIn adj)
    (regular : ∀ v, (outN adj v).card = 9)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ v, 18 ≤ (second adj v).card + (inN adj v).card := by
  by_contra hn
  have bad (v : V) : (second adj v).card + (inN adj v).card ≤ 17 := by
    have hh : ¬ 18 ≤ (second adj v).card + (inN adj v).card := fun h => hn ⟨v, h⟩
    omega
  have cap (v : V) : (inN adj v).card ≤ 10 := by
    have := second_ge_seven adj noDigon small regular v
    have := bad v
    omega
  let H : Ambient adj := ⟨loopless, noDigon, noTri, small, smallRev, regular, cap, bad⟩
  have balanced := CH.CompromiseTransport.deficit_transport adj 9 (by omega) regular cap
    (high_head_charge adj H)
  obtain ⟨v, hv⟩ := seymour
  have := balanced v
  have := bad v
  rw [regular] at hv
  omega

/-- The same theorem with the supplied induction statements spelled out. -/
theorem compromise_nine_from_induction (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 9 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card)
    (ihRev : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 9 →
      (∀ a ∈ S, r ≤ (inN adj a ∩ S).card) → 3 * r < S.card)
    (regular : ∀ v, (outN adj v).card = 9)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ v, 18 ≤ (second adj v).card + (inN adj v).card :=
  compromise_nine adj loopless noDigon noTri (small_out_of_induction adj ih)
    (small_in_of_induction adj ihRev) regular seymour

/-- Four-set disjointness converts the compromise conclusion to the CH bound. -/
theorem order_bound_nine (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (smallRev : SmallIn adj)
    (regular : ∀ v, (outN adj v).card = 9)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    28 ≤ Fintype.card V := by
  obtain ⟨v, hv⟩ := compromise_nine adj loopless noDigon noTri small smallRev regular seymour
  have hoi : Disjoint (outN adj v) (inN adj v) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact noDigon v a (by simpa using ha) (by simpa using hb)
  have hos : Disjoint (outN adj v) (second adj v) := by
    apply disjoint_left.mpr
    intro a ha hs
    exact ((mem_second adj v a).mp hs).2.1 (by simpa using ha)
  have his : Disjoint (inN adj v) (second adj v) := by
    apply disjoint_left.mpr
    intro a ha hs
    obtain ⟨_, _, b, hvb, hba⟩ := (mem_second adj v a).mp hs
    exact noTri v b a hvb hba (by simpa using ha)
  have hvnot : v ∉ outN adj v ∪ inN adj v ∪ second adj v := by
    simp [loopless]
  have hc := card_le_card (subset_univ
    (insert v (outN adj v ∪ inN adj v ∪ second adj v)))
  rw [card_insert_of_notMem hvnot,
    card_union_of_disjoint (disjoint_union_left.mpr ⟨hos, his⟩),
    card_union_of_disjoint hoi, regular, card_univ] at hc
  omega

end CH.CompromiseNine

#print axioms CH.CompromiseNineFrame.Frame.local_dichotomy
#print axioms CH.CompromiseNine.high_head_charge
#print axioms CH.CompromiseNine.compromise_nine
#print axioms CH.CompromiseNine.compromise_nine_from_induction
#print axioms CH.CompromiseNine.order_bound_nine
