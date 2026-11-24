module

public import LeanCH.CompromiseTenNoReturn
public import LeanCH.CompromiseTenResidual

set_option linter.style.header false

/-! A hypothetical degree-ten counterexample has an actually undercharged
root, and that root must have an exceptional second neighbour with low
internal degree or an edge back into the first neighbourhood. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal CH.CompromiseTenFrame
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

theorem undercharged_good_minimum (H : Ambient adj) (f : Frame adj)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    ∀ z ∈ f.good, 2 ≤ f.zOut z := by
  intro z hz
  by_contra small
  have bound := f.good_low_fourteen H z hz (by omega)
  omega

theorem undercharged_exception (H : Ambient adj) (f : Frame adj)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    ∃ z ∈ f.Z, 4 ≤ f.omission z ∧
      (f.zOut z ≤ 1 ∨ ∃ a ∈ f.A, adj z a) := by
  have obstruction : ∃ z ∈ f.Z, f.zOut z ≤ 1 ∨ ∃ a ∈ f.A, adj z a := by
    by_contra none
    have minimum (z : V) (hz : z ∈ f.Z) : 2 ≤ f.zOut z := by
      have hn : ¬ f.zOut z ≤ 1 := fun h => none ⟨z, hz, Or.inl h⟩
      omega
    have noReturn (z : V) (hz : z ∈ f.Z) (a : V) (ha : a ∈ f.A) : ¬ adj z a :=
      fun h => none ⟨z, hz, Or.inr ⟨a, ha, h⟩⟩
    have charge := f.no_return_charge H minimum noReturn
    omega
  obtain ⟨z, hz, bad⟩ := obstruction
  refine ⟨z, hz, ?_, bad⟩
  by_contra small
  have good : z ∈ f.good := mem_filter.mpr ⟨hz, by omega⟩
  rcases bad with low | ⟨a, ha, edge⟩
  · have bound := f.undercharged_good_minimum H under z good
    omega
  · exact f.good_avoids_A H z good a ha edge

theorem undercharged_exceptional_card (H : Ambient adj) (f : Frame adj)
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    1 ≤ f.exceptional.card ∧ f.exceptional.card ≤ 4 := by
  obtain ⟨z, hz, large, _⟩ := f.undercharged_exception H under
  have member : z ∈ f.exceptional := mem_sdiff.mpr ⟨hz, by
    intro good
    have := (mem_filter.mp good).2
    omega⟩
  exact ⟨card_pos.mpr ⟨z, member⟩, f.exceptional_le_four H⟩

end CH.CompromiseTenFrame.Frame

namespace CH.CompromiseTenUndercharged

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem root (H : Ambient adj)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ y, (inN adj y).card = 11 ∧ (second adj y).card = 8 ∧
      (∑ a ∈ outN adj y, (10 - (inN adj a).card)) ≤ 9 := by
  by_contra none
  have charge (y : V) (high : 10 < (inN adj y).card) :
      10 * ((inN adj y).card - 10) ≤ ∑ a ∈ outN adj y, (10 - (inN adj a).card) := by
    have cap := H.toAmbient.indegree_cap y
    by_cases twelve : (inN adj y).card = 12
    · have bound := CH.CompromiseTenResidual.twelve_charge adj H y twelve
      omega
    have eleven : (inN adj y).card = 11 := by omega
    have lower := H.toAmbient.second_ge_seven y
    have bad := H.bad y
    by_cases seven : (second adj y).card = 7
    · have bound := CH.CompromiseTenResidual.seven_charge adj H y seven
      omega
    have eight : (second adj y).card = 8 := by omega
    have enough : ¬ (∑ a ∈ outN adj y, (10 - (inN adj a).card)) ≤ 9 :=
      fun h => none ⟨y, eleven, eight, h⟩
    omega
  have balanced := CH.CompromiseSurplus.transport adj 10 (by omega) H.regular charge
  obtain ⟨v, hv⟩ := seymour
  have equal := balanced v
  have bad := H.bad v
  rw [H.regular] at hv
  omega

theorem exceptional_root (H : Ambient adj)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ y, (inN adj y).card = 11 ∧ (second adj y).card = 8 ∧
      (∑ a ∈ outN adj y, (10 - (inN adj a).card)) ≤ 9 ∧
      ∃ z ∈ second adj y, 4 ≤ (outN adj y \ inN adj z).card ∧
        ((outN adj z ∩ second adj y).card ≤ 1 ∨ ∃ a ∈ outN adj y, adj z a) := by
  obtain ⟨y, eleven, eight, under⟩ := root adj H seymour
  refine ⟨y, eleven, eight, under, ?_⟩
  exact (CH.CompromiseTenResidual.eightFrame adj H y eight).undercharged_exception H under

theorem exceptional_root_from_induction
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
      ∃ z ∈ second adj y, 4 ≤ (outN adj y \ inN adj z).card ∧
        ((outN adj z ∩ second adj y).card ≤ 1 ∨ ∃ a ∈ outN adj y, adj z a) := by
  have outFlip (v : V) : outN (fun u w => adj w u) v = inN adj v := by ext x; simp
  have reverse : SmallOut (fun u v => adj v u) := by
    apply CH.CompromiseTenLocal.small_of_induction
    intro S r hn hr hrTen minimum
    apply ihRev S r hn hr hrTen
    intro a ha
    simpa only [outFlip] using minimum a ha
  let H : Ambient adj := {
    loopless := loopless
    noDigon := noDigon
    noTri := noTri
    small := CH.CompromiseTenLocal.small_of_induction adj ih
    smallRev := reverse
    regular := regular
    bad := bad }
  exact exceptional_root adj H seymour

end CH.CompromiseTenUndercharged

#print axioms CH.CompromiseTenFrame.Frame.undercharged_exception
#print axioms CH.CompromiseTenUndercharged.root
#print axioms CH.CompromiseTenUndercharged.exceptional_root_from_induction
