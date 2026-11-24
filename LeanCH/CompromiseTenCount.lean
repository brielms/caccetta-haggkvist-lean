module

public import LeanCH.CompromiseTenTop
public import LeanCH.CompromiseSurplus

set_option linter.style.header false

/-! A global cost for the maximum-indegree sector at degree ten.
The ambient assumptions include the smaller-degree CH input and a
strict unit compromise counterexample; no full rank-ten theorem is claimed. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal CH.CompromiseTenTop
public section

namespace CH.CompromiseTenCount

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def highOne : Finset V := univ.filter (fun v => (inN adj v).card = 11)
@[expose] def highTwo : Finset V := univ.filter (fun v => (inN adj v).card = 12)
@[expose] def lowHeads : Finset V := (highTwo adj).biUnion (outN adj)

omit [DecidableEq V] in
@[simp] theorem mem_highOne (v : V) : v ∈ highOne adj ↔ (inN adj v).card = 11 := by
  simp [highOne]

omit [DecidableEq V] in
@[simp] theorem mem_highTwo (v : V) : v ∈ highTwo adj ↔ (inN adj v).card = 12 := by
  simp [highTwo]

theorem heads_subset (y : V) (hy : y ∈ highTwo adj) : outN adj y ⊆ lowHeads adj := by
  intro a ha
  exact mem_biUnion.mpr ⟨y, hy, ha⟩

theorem low_cap (H : Ambient adj) (a : V) (ha : a ∈ lowHeads adj) :
    (inN adj a).card ≤ 7 := by
  obtain ⟨y, hy, ha⟩ := mem_biUnion.mp ha
  exact (H.frame y ((mem_highTwo adj y).mp hy)).heads_seven H a ha

theorem incoming_high_cap (H : Ambient adj) (a : V) (ha : a ∈ lowHeads adj) :
    (inN adj a ∩ highTwo adj).card ≤ 4 := by
  obtain ⟨y, hy, hay⟩ := mem_biUnion.mp ha
  have inner := (H.frame y ((mem_highTwo adj y).mp hy)).internalIn a hay
  change (inN adj a ∩ outN adj y).card = 3 at inner
  have disj : Disjoint (inN adj a ∩ highTwo adj) (inN adj a ∩ outN adj y) := by
    apply disjoint_left.mpr
    intro b hb hb'
    have cap := low_cap adj H b (heads_subset adj y hy (mem_inter.mp hb').2)
    have high := (mem_highTwo adj b).mp (mem_inter.mp hb).2
    omega
  have count := card_le_card (union_subset
    (inter_subset_left : inN adj a ∩ highTwo adj ⊆ inN adj a)
    (inter_subset_left : inN adj a ∩ outN adj y ⊆ inN adj a))
  rw [card_union_of_disjoint disj, inner] at count
  have cap := low_cap adj H a ha
  omega

theorem high_edges (H : Ambient adj) :
    10 * (highTwo adj).card ≤ 4 * (lowHeads adj).card := by
  have count := double_count adj (highTwo adj) (lowHeads adj)
  have lhs : (∑ y ∈ highTwo adj, (outN adj y ∩ lowHeads adj).card) =
      10 * (highTwo adj).card := by
    calc
      _ = ∑ _y ∈ highTwo adj, 10 := sum_congr rfl (fun y hy => by
        rw [inter_eq_left.mpr (heads_subset adj y hy), H.regular])
      _ = _ := by simp [Nat.mul_comm]
  have rhs := sum_le_sum (fun a ha => incoming_high_cap adj H a ha)
  rw [← count, lhs] at rhs
  simpa [Nat.mul_comm] using rhs

theorem deficit_budget (H : Ambient adj) :
    (∑ v, (10 - (inN adj v).card)) = (highOne adj).card + 2 * (highTwo adj).card := by
  rw [CH.CompromiseSurplus.balance adj 10 H.regular]
  have point (v : V) : (inN adj v).card - 10 =
      (if (inN adj v).card = 11 then 1 else 0) +
      2 * (if (inN adj v).card = 12 then 1 else 0) := by
    have cap := H.indegree_cap v
    split_ifs <;> omega
  simp_rw [point]
  rw [sum_add_distrib, ← mul_sum]
  simp [highOne, highTwo]

theorem low_deficit (H : Ambient adj) :
    3 * (lowHeads adj).card ≤ (highOne adj).card + 2 * (highTwo adj).card := by
  have lower : (∑ _a ∈ lowHeads adj, 3) ≤
      ∑ a ∈ lowHeads adj, (10 - (inN adj a).card) := by
    apply sum_le_sum
    intro a ha
    have cap := low_cap adj H a ha
    omega
  have upper := sum_le_sum_of_subset (f := fun a => 10 - (inN adj a).card)
    (subset_univ (lowHeads adj))
  rw [deficit_budget adj H] at upper
  simp only [sum_const, smul_eq_mul] at lower
  omega

theorem disjoint_low_one (H : Ambient adj) : Disjoint (lowHeads adj) (highOne adj) := by
  apply disjoint_left.mpr
  intro a ha hh
  have cap := low_cap adj H a ha
  have high := (mem_highOne adj a).mp hh
  omega

theorem disjoint_low_two (H : Ambient adj) : Disjoint (lowHeads adj) (highTwo adj) := by
  apply disjoint_left.mpr
  intro a ha hh
  have cap := low_cap adj H a ha
  have high := (mem_highTwo adj a).mp hh
  omega

omit [DecidableEq V] in
theorem disjoint_one_two : Disjoint (highOne adj) (highTwo adj) := by
  classical
  apply disjoint_left.mpr
  intro a ha hh
  have one := (mem_highOne adj a).mp ha
  have two := (mem_highTwo adj a).mp hh
  omega

theorem cardinal_budget (H : Ambient adj) :
    (lowHeads adj).card + (highOne adj).card + (highTwo adj).card ≤ Fintype.card V := by
  have count := card_le_univ (s := (lowHeads adj ∪ highOne adj) ∪ highTwo adj)
  rw [card_union_of_disjoint (disjoint_union_left.mpr
    ⟨disjoint_low_two adj H, disjoint_one_two adj⟩),
    card_union_of_disjoint (disjoint_low_one adj H)] at count
  exact count

theorem high_one_cost (H : Ambient adj) :
    11 * (highTwo adj).card ≤ 2 * (highOne adj).card := by
  have := high_edges adj H
  have := low_deficit adj H
  omega

theorem low_order_cost (H : Ambient adj) :
    18 * (lowHeads adj).card ≤ 5 * Fintype.card V := by
  have := high_edges adj H
  have := low_deficit adj H
  have := cardinal_budget adj H
  omega

theorem order_at_least_thirty_six (H : Ambient adj) (y : V)
    (high : (inN adj y).card = 12) : 36 ≤ Fintype.card V := by
  have bound := card_le_card (heads_subset adj y ((mem_highTwo adj y).mpr high))
  rw [H.regular] at bound
  have := low_order_cost adj H
  omega

theorem sizes_at_thirty_six (H : Ambient adj) (y : V)
    (high : (inN adj y).card = 12) (order : Fintype.card V = 36) :
    (lowHeads adj).card = 10 ∧ (highOne adj).card = 22 ∧ (highTwo adj).card = 4 := by
  have bound := card_le_card (heads_subset adj y ((mem_highTwo adj y).mpr high))
  rw [H.regular] at bound
  have := high_edges adj H
  have := low_deficit adj H
  have := cardinal_budget adj H
  omega

/-- The apparent equality case in the global count is itself impossible. -/
theorem not_order_thirty_six (H : Ambient adj) (y : V)
    (high : (inN adj y).card = 12) (order : Fintype.card V = 36) : False := by
  obtain ⟨sizeL, sizeOne, sizeTwo⟩ := sizes_at_thirty_six adj H y high order
  let f := H.frame y high
  have highOut (v : V) (hv : v ∈ highTwo adj) : outN adj v = lowHeads adj :=
    eq_of_subset_of_card_le (heads_subset adj v hv) (by rw [sizeL, H.regular])
  have frameA : f.A = lowHeads adj := highOut y ((mem_highTwo adj y).mpr high)
  have covered : (lowHeads adj ∪ highOne adj) ∪ highTwo adj = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_union_of_disjoint (disjoint_union_left.mpr
      ⟨disjoint_low_two adj H, disjoint_one_two adj⟩),
      card_union_of_disjoint (disjoint_low_one adj H), card_univ, sizeL, sizeOne, sizeTwo, order]
  have cases (v : V) : v ∈ lowHeads adj ∨ v ∈ highOne adj ∨ v ∈ highTwo adj := by
    have member : v ∈ (lowHeads adj ∪ highOne adj) ∪ highTwo adj := covered.symm ▸ mem_univ v
    simpa only [mem_union, or_assoc] using member
  have noOneToLow (v : V) (hv : v ∈ highOne adj) (a : V) (ha : a ∈ lowHeads adj) :
      ¬ adj v a := by
    have internal : (inN adj a ∩ lowHeads adj).card = 3 := by
      rw [← frameA]
      exact f.internalIn a (frameA.symm ▸ ha)
    have disj : Disjoint (inN adj a ∩ lowHeads adj) (highTwo adj) :=
      (disjoint_low_two adj H).mono_left inter_subset_right
    have subset : (inN adj a ∩ lowHeads adj) ∪ highTwo adj ⊆ inN adj a := by
      apply union_subset inter_subset_left
      intro b hb
      apply (mem_inN adj a b).mpr
      apply (mem_outN adj b a).mp
      rw [highOut b hb]
      exact ha
    have equal : (inN adj a ∩ lowHeads adj) ∪ highTwo adj = inN adj a := by
      apply eq_of_subset_of_card_le subset
      rw [card_union_of_disjoint disj, internal, sizeTwo]
      exact low_cap adj H a ha
    intro edge
    have member := (mem_inN adj a v).mpr edge
    rw [← equal] at member
    rcases mem_union.mp member with hl | ht
    · exact disjoint_left.mp (disjoint_low_one adj H) (mem_inter.mp hl).2 hv
    · exact disjoint_left.mp (disjoint_one_two adj) hv ht
  have headsOne (v : V) (hv : v ∈ highOne adj) :
      outN adj v ⊆ highOne adj ∪ highTwo adj := by
    intro a ha
    rcases cases a with hl | ho | ht
    · exact (noOneToLow v hv a hl ((mem_outN adj v a).mp ha)).elim
    · exact mem_union_left _ ho
    · exact mem_union_right _ ht
  have minimum (v : V) (hv : v ∈ highOne adj) : 6 ≤ (outN adj v ∩ highOne adj).card := by
    have bound := degree_bound (outN adj v) (highOne adj) (highTwo adj) (headsOne v hv)
    rw [H.regular, sizeTwo] at bound
    omega
  have inBound (v : V) (hv : v ∈ highOne adj) : (inN adj v ∩ highOne adj).card ≤ 10 := by
    have headSize := card_le_card (inter_subset_left : outN adj v ∩ highOne adj ⊆ outN adj v)
    rw [H.regular] at headSize
    have bound := local_degree_bound adj H.loopless H.noDigon H.noTri H.small
      (highOne adj) 6 (by omega) minimum v hv headSize
    have lower := minimum v hv
    rw [sizeOne] at bound
    omega
  have count := card_sdiff_add_card_inter (highOne adj) f.Z
  have bound := card_le_card (inter_subset_right : highOne adj ∩ f.Z ⊆ f.Z)
  rw [sizeOne] at count
  rw [f.cardZ] at bound
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (highOne adj \ f.Z).card by omega)
  have uOne := (mem_sdiff.mp hu).1
  have uNotZ := (mem_sdiff.mp hu).2
  have uNotLow : u ∉ lowHeads adj := fun hl =>
    disjoint_left.mp (disjoint_low_one adj H) hl uOne
  have incoming : inN adj u ⊆ highOne adj := by
    intro v hv
    have edge := (mem_inN adj u v).mp hv
    rcases cases v with hl | ho | ht
    · have heads := f.headsA v (frameA.symm ▸ hl) ((mem_outN adj v u).mpr edge)
      rcases mem_union.mp heads with ha | hz
      · exact (uNotLow (frameA ▸ ha)).elim
      · exact (uNotZ hz).elim
    · exact ho
    · have member := (mem_outN adj v u).mpr edge
      rw [highOut v ht] at member
      exact (uNotLow member).elim
  have upper := inBound u uOne
  rw [inter_eq_left.mpr incoming, (mem_highOne adj u).mp uOne] at upper
  omega

theorem order_at_least_thirty_seven (H : Ambient adj) (y : V)
    (high : (inN adj y).card = 12) : 37 ≤ Fintype.card V := by
  have lower := order_at_least_thirty_six adj H y high
  have unequal : Fintype.card V ≠ 36 := not_order_thirty_six adj H y high
  omega

theorem indegree_at_most_eleven (H : Ambient adj) (order : Fintype.card V ≤ 36) (v : V) :
    (inN adj v).card ≤ 11 := by
  have cap := H.indegree_cap v
  by_contra greater
  have high : (inN adj v).card = 12 := by omega
  have := order_at_least_thirty_seven adj H v high
  omega

/-- The induction input is exposed rather than hidden in an ambient record. -/
theorem indegree_at_most_eleven_from_induction
    (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 10 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card)
    (regular : ∀ v, (outN adj v).card = 10)
    (bad : ∀ v, (second adj v).card + (inN adj v).card ≤ 19)
    (order : Fintype.card V ≤ 36) (v : V) : (inN adj v).card ≤ 11 :=
  indegree_at_most_eleven adj
    ⟨loopless, noDigon, noTri, small_of_induction adj ih, regular, bad⟩ order v

end CH.CompromiseTenCount

#print axioms CH.CompromiseTenCount.high_edges
#print axioms CH.CompromiseTenCount.high_one_cost
#print axioms CH.CompromiseTenCount.order_at_least_thirty_six
#print axioms CH.CompromiseTenCount.not_order_thirty_six
#print axioms CH.CompromiseTenCount.indegree_at_most_eleven
#print axioms CH.CompromiseTenCount.indegree_at_most_eleven_from_induction
