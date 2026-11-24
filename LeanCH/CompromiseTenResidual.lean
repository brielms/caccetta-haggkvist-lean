module

public import LeanCH.CompromiseTenCharge
public import LeanCH.CompromiseSurplus

set_option linter.style.header false

/-! A necessary remaining configuration for a degree-ten unit compromise
counterexample. This is a reduction, not the full compromise theorem. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal CH.CompromiseTenFrame
public section

namespace CH.CompromiseTenResidual

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def eightFrame (H : Ambient adj) (y : V) (eight : (second adj y).card = 8) :
    Frame adj where
  A := outN adj y
  Z := second adj y
  cardA := H.regular y
  cardZ := eight
  disj := disjoint_left.mpr (fun _ ha hz =>
    ((mem_second adj y _).mp hz).2.1 ((mem_outN adj y _).mp ha))
  headsA := fun _ ha => heads_two_steps adj H.noDigon ha

@[expose] def sevenFrame (H : Ambient adj) (y : V) (seven : (second adj y).card = 7) :
    CH.CompromiseTenTop.TopFrame adj := by
  let A := outN adj y
  let Z := second adj y
  have sizeA : A.card = 10 := H.regular y
  have sizeZ : Z.card = 7 := seven
  have disj : Disjoint A Z := disjoint_left.mpr (fun _ ha hz =>
    ((mem_second adj y _).mp hz).2.1 ((mem_outN adj y _).mp ha))
  have heads (a : V) (ha : a ∈ A) : outN adj a ⊆ A ∪ Z := heads_two_steps adj H.noDigon ha
  have minimum (a : V) (ha : a ∈ A) : 3 ≤ (outN adj a ∩ A).card := by
    have bound := degree_bound (outN adj a) A Z (heads a ha)
    rw [H.regular] at bound
    change 10 ≤ (outN adj a ∩ A).card + (second adj y).card at bound
    omega
  have rigid := rigid_small adj H.loopless H.noDigon H.noTri H.small A 3
    (by omega) (by omega) sizeA minimum
  refine ⟨A, Z, sizeA, seven, disj, heads, ?_, fun a ha => (rigid a ha).1,
    fun a ha => (rigid a ha).2⟩
  intro a ha z hz
  have union : (outN adj a ∩ A) ∪ (outN adj a ∩ Z) = outN adj a := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr (heads a ha)]
  have count := card_union_of_disjoint (disj.mono
    (inter_subset_right : outN adj a ∩ A ⊆ A)
    (inter_subset_right : outN adj a ∩ Z ⊆ Z))
  rw [union, H.regular, (rigid a ha).1] at count
  have equal : outN adj a ∩ Z = Z := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact (mem_outN adj a z).mp (mem_inter.mp (equal.symm ▸ hz)).1

theorem top_frame_charge (H : Ambient adj) (f : CH.CompromiseTenTop.TopFrame adj) :
    30 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have point (a : V) (ha : a ∈ f.A) : 3 ≤ 10 - (inN adj a).card := by
    have := f.heads_seven H.toAmbient a ha
    omega
  have bound := sum_le_sum point
  simpa only [sum_const, smul_eq_mul, f.cardA] using bound

theorem seven_charge (H : Ambient adj) (y : V) (seven : (second adj y).card = 7) :
    30 ≤ ∑ a ∈ outN adj y, (10 - (inN adj a).card) :=
  top_frame_charge adj H (sevenFrame adj H y seven)

theorem twelve_charge (H : Ambient adj) (y : V) (twelve : (inN adj y).card = 12) :
    30 ≤ ∑ a ∈ outN adj y, (10 - (inN adj a).card) :=
  top_frame_charge adj H (H.toAmbient.frame y twelve)

/-- Every strict counterexample with a Seymour vertex has an
in-degree-eleven root whose densely reached second neighbours all
have at least two heads in the second neighbourhood. -/
theorem residual_root (H : Ambient adj)
    (seymour : ∃ v, (outN adj v).card ≤ (second adj v).card) :
    ∃ y, (inN adj y).card = 11 ∧ (second adj y).card = 8 ∧
      ∀ z ∈ second adj y, (outN adj y \ inN adj z).card ≤ 3 →
        2 ≤ (outN adj z ∩ second adj y).card := by
  by_contra none
  have charge (y : V) (high : 10 < (inN adj y).card) :
      10 * ((inN adj y).card - 10) ≤ ∑ a ∈ outN adj y, (10 - (inN adj a).card) := by
    have cap := H.toAmbient.indegree_cap y
    by_cases twelve : (inN adj y).card = 12
    · have bound := twelve_charge adj H y twelve
      omega
    have eleven : (inN adj y).card = 11 := by omega
    have lower := H.toAmbient.second_ge_seven y
    have bad := H.bad y
    by_cases seven : (second adj y).card = 7
    · have bound := seven_charge adj H y seven
      omega
    have eight : (second adj y).card = 8 := by omega
    have low : ∃ z ∈ second adj y, (outN adj y \ inN adj z).card ≤ 3 ∧
        (outN adj z ∩ second adj y).card ≤ 1 := by
      by_contra missing
      apply none
      refine ⟨y, eleven, eight, ?_⟩
      intro z hz good
      have noLow : ¬ (outN adj z ∩ second adj y).card ≤ 1 := fun h => missing ⟨z, hz, good, h⟩
      omega
    obtain ⟨z, hz, good, low⟩ := low
    let f := eightFrame adj H y eight
    have member : z ∈ f.good := mem_filter.mpr ⟨hz, good⟩
    have bound := f.good_low_charge H z member low
    change 10 ≤ ∑ a ∈ outN adj y, (10 - (inN adj a).card) at bound
    omega
  have balanced := CH.CompromiseSurplus.transport adj 10 (by omega) H.regular charge
  obtain ⟨v, hv⟩ := seymour
  have equal := balanced v
  have bad := H.bad v
  rw [H.regular] at hv
  omega

/-- Both induction directions and the Seymour input are explicit. -/
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
      ∀ z ∈ second adj y, (outN adj y \ inN adj z).card ≤ 3 →
        2 ≤ (outN adj z ∩ second adj y).card := by
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
  exact residual_root adj H seymour

end CH.CompromiseTenResidual

#print axioms CH.CompromiseTenResidual.seven_charge
#print axioms CH.CompromiseTenResidual.twelve_charge
#print axioms CH.CompromiseTenResidual.residual_root
#print axioms CH.CompromiseTenResidual.residual_root_from_induction
