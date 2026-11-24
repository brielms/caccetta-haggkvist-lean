module

public import LeanCH.CompromiseTenSoleCharge

set_option linter.style.header false

/-! Global reduction after closure of the two-exception frame. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenTwoException

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem residual_root (H : CH.CompromiseTenFrame.Ambient adj)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ y, (inN adj y).card = 11 ∧ (second adj y).card = 8 ∧
      (∑ a ∈ outN adj y, (10 - (inN adj a).card)) ≤ 9 ∧
      3 ≤ ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ∧
      ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ≤ 4 ∧
      ∃ a ∈ outN adj y, 10 ≤ (inN adj a).card ∧ ∃ z ∈ second adj y,
        adj a z ∧ 4 ≤ (outN adj y \ inN adj z).card ∧ ∃ b ∈ outN adj y, adj z b := by
  obtain ⟨y, eleven, eight, under⟩ := CH.CompromiseTenUndercharged.root adj H seymour
  let f := CH.CompromiseTenResidual.eightFrame adj H y eight
  have counts := f.undercharged_three_exceptions H under
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
      3 ≤ ((second adj y).filter (fun z => 4 ≤ (outN adj y \ inN adj z).card)).card ∧
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

end CH.CompromiseTenTwoException

#print axioms CH.CompromiseTenTwoException.residual_root_from_induction
