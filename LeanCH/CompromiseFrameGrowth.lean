module

public import LeanCH.CompromiseTenFrame

set_option linter.style.header false

/-! A degree-independent inside-growth inequality. The chosen head's
entire out-neighbourhood is counted, including its heads in the second
frame set. No compromise failure or omission budget is needed. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseFrameGrowth

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem selected (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (A Z : Finset V) (disj : Disjoint A Z)
    (heads : ∀ a ∈ A, outN adj a ⊆ A ∪ Z)
    (R : ℕ) (regular : ∀ a ∈ A, (outN adj a).card = R)
    (a : V) (ha : a ∈ A) (b : V) (hb : b ∈ outN adj a ∩ A)
    (k : ℕ) (small : (outN adj b ∩ (outN adj a ∩ A)).card ≤ k) :
    (outN adj a ∩ A).card ≤ (second adj a ∩ (A ∪ Z)).card + k := by
  let W := outN adj a ∩ A
  let C := outN adj a ∩ Z
  let I := second adj a ∩ (A ∪ Z)
  have ab := (mem_outN adj a b).mp (mem_inter.mp hb).1
  have bA := (mem_inter.mp hb).2
  have subset : outN adj b ⊆ W ∪ (C ∪ I) := by
    intro x hx
    have bx := (mem_outN adj b x).mp hx
    by_cases ax : adj a x
    · rcases mem_union.mp (heads a ha ((mem_outN adj a x).mpr ax)) with xA | xZ
      · exact mem_union_left _ (mem_inter.mpr ⟨(mem_outN adj a x).mpr ax, xA⟩)
      · exact mem_union_right _ (mem_union_left _
          (mem_inter.mpr ⟨(mem_outN adj a x).mpr ax, xZ⟩))
    · apply mem_union_right
      apply mem_union_right
      refine mem_inter.mpr ⟨(mem_second adj a x).mpr ⟨?_, ax, b, ab, bx⟩, heads b bA hx⟩
      intro equal
      subst x
      exact noDigon a b ab bx
  have ci : Disjoint C I := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact ((mem_second adj a x).mp (mem_inter.mp hx').1).2.1
      ((mem_outN adj a x).mp (mem_inter.mp hx).1)
  have count := degree_bound (outN adj b) W (C ∪ I) subset
  rw [regular b bA, card_union_of_disjoint ci] at count
  have union : W ∪ C = outN adj a := by
    dsimp [W, C]
    rw [← inter_union_distrib_left, inter_eq_left.mpr (heads a ha)]
  have split := card_union_of_disjoint (disj.mono
    (inter_subset_right : W ⊆ A) (inter_subset_right : C ⊆ Z))
  rw [union, regular a ha] at split
  change R = W.card + C.card at split
  change (outN adj b ∩ W).card ≤ k at small
  change W.card ≤ I.card + k
  omega

/-- The supplied smaller-degree induction selects the required head.
The ambient order and the size of Z are unrestricted. -/
theorem from_induction (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (A Z : Finset V) (disj : Disjoint A Z)
    (heads : ∀ a ∈ A, outN adj a ⊆ A ∪ Z)
    (R : ℕ) (rank : 2 ≤ R) (sizeA : A.card = R)
    (regular : ∀ a ∈ A, (outN adj a).card = R)
    (ih : ∀ (S : Finset V) (r : ℕ), S ⊆ A → S.Nonempty → 1 ≤ r → r < R →
      (∀ b ∈ S, r ≤ (outN adj b ∩ S).card) → 3 * r < S.card)
    (a : V) (ha : a ∈ A) (positive : 0 < (outN adj a ∩ A).card) :
    (outN adj a ∩ A).card ≤ (second adj a ∩ (A ∪ Z)).card +
      ((outN adj a ∩ A).card - 1) / 3 := by
  let W := outN adj a ∩ A
  have size : W.card ≤ R := (card_le_card inter_subset_right).trans (by omega)
  have choice : ∃ b ∈ W, (outN adj b ∩ W).card ≤ (W.card - 1) / 3 := by
    by_contra none
    have minimum (b : V) (hb : b ∈ W) :
        (W.card - 1) / 3 + 1 ≤ (outN adj b ∩ W).card := by
      have h : ¬ (outN adj b ∩ W).card ≤ (W.card - 1) / 3 := fun h => none ⟨b, hb, h⟩
      omega
    have contradiction := ih W ((W.card - 1) / 3 + 1) inter_subset_right
      (card_pos.mp positive) (by omega) (by omega) minimum
    omega
  obtain ⟨b, hb, small⟩ := choice
  exact selected adj noDigon A Z disj heads R regular a ha b hb ((W.card - 1) / 3) small

end CH.CompromiseFrameGrowth

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem full_inside_growth (a : V) (ha : a ∈ f.A) :
    2 + f.extra a ≤ (f.inside a).card + (f.extra a + 1) / 3 := by
  let W := outN adj a ∩ f.A
  have row := f.row_counts H a ha
  change W.card = 2 + f.extra a at row
  obtain ⟨b, hb, small⟩ := H.small W (card_pos.mp (by omega))
    ((card_le_card inter_subset_right).trans (by rw [f.cardA]))
  have bound := CH.CompromiseFrameGrowth.selected adj H.noDigon f.A f.Z f.disj f.headsA
    10 (fun b _ => H.regular b) a ha b hb ((W.card - 1) / 3) small
  change W.card ≤ (f.inside a).card + (W.card - 1) / 3 at bound
  omega

theorem inside_at_least_two (a : V) (ha : a ∈ f.A) : 2 ≤ (f.inside a).card := by
  have := f.full_inside_growth H a ha
  omega

theorem extra_le_seven (a : V) (ha : a ∈ f.A) : f.extra a ≤ 7 := by
  have count := card_le_card (insert_subset ha
    (inter_subset_right : outN adj a ∩ f.A ⊆ f.A))
  rw [card_insert_of_notMem (by simp [H.loopless]), f.cardA] at count
  have row := f.row_counts H a ha
  change (outN adj a ∩ f.A).card = 2 + f.extra a at row
  omega

theorem inside_at_least_extra (a : V) (ha : a ∈ f.A) : f.extra a ≤ (f.inside a).card := by
  have := f.full_inside_growth H a ha
  have := f.extra_le_seven H a ha
  omega

theorem inside_extra_positive (a : V) (ha : a ∈ f.A) (positive : 1 ≤ f.extra a) :
    3 ≤ (f.inside a).card := by
  have := f.full_inside_growth H a ha
  omega

theorem no_thin_row (a : V) (ha : a ∈ f.A) : ¬ (f.inside a).card ≤ 1 := by
  have := f.inside_at_least_two H a ha
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseFrameGrowth.selected
#print axioms CH.CompromiseFrameGrowth.from_induction
#print axioms CH.CompromiseTenFrame.Frame.full_inside_growth
#print axioms CH.CompromiseTenFrame.Frame.no_thin_row
