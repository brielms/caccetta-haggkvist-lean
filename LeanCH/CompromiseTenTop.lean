module

public import LeanCH.CompromiseTenLocal

set_option linter.style.header false

/-! The maximum-indegree sector of a degree-ten unit compromise
counterexample. All small-set CH inputs are explicit. This module
does not assert the full degree-ten compromise conclusion. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenTop

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

structure Ambient : Prop where
  loopless : ∀ v, ¬ adj v v
  noDigon : ∀ u v, adj u v → ¬ adj v u
  noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u
  small : SmallOut adj
  regular : ∀ v, (outN adj v).card = 10
  bad : ∀ v, (second adj v).card + (inN adj v).card ≤ 19

structure TopFrame where
  A : Finset V
  Z : Finset V
  cardA : A.card = 10
  cardZ : Z.card = 7
  disj : Disjoint A Z
  headsA : ∀ a ∈ A, outN adj a ⊆ A ∪ Z
  complete : ∀ a ∈ A, ∀ z ∈ Z, adj a z
  internalOut : ∀ a ∈ A, (outN adj a ∩ A).card = 3
  internalIn : ∀ a ∈ A, (inN adj a ∩ A).card = 3

namespace Ambient

variable {adj}

theorem second_ge_seven (H : Ambient adj) (v : V) : 7 ≤ (second adj v).card := by
  obtain ⟨a, ha, hs⟩ := H.small (outN adj v)
    (card_pos.mp (by rw [H.regular]; omega)) (by rw [H.regular])
  have count := degree_bound (outN adj a) (outN adj v) (second adj v)
    (heads_two_steps adj H.noDigon ha)
  rw [H.regular] at count hs
  omega

theorem indegree_cap (H : Ambient adj) (v : V) : (inN adj v).card ≤ 12 := by
  have := H.second_ge_seven v
  have := H.bad v
  omega

@[expose] def frame (H : Ambient adj) (y : V) (high : (inN adj y).card = 12) : TopFrame adj := by
  let A := outN adj y
  let Z := second adj y
  have sizeA : A.card = 10 := H.regular y
  have sizeZ : Z.card = 7 := by have := H.second_ge_seven y; have := H.bad y; dsimp [Z]; omega
  have disj : Disjoint A Z := by
    apply disjoint_left.mpr
    intro a ha hz
    exact ((mem_second adj y a).mp hz).2.1 ((mem_outN adj y a).mp ha)
  have heads (a : V) (ha : a ∈ A) : outN adj a ⊆ A ∪ Z := heads_two_steps adj H.noDigon ha
  have minimum (a : V) (ha : a ∈ A) : 3 ≤ (outN adj a ∩ A).card := by
    have bound := degree_bound (outN adj a) A Z (heads a ha)
    rw [H.regular, sizeZ] at bound
    omega
  have rigid := rigid_small adj H.loopless H.noDigon H.noTri H.small A 3 (by omega)
    (by omega) sizeA minimum
  refine ⟨A, Z, sizeA, sizeZ, disj, heads, ?_, fun a ha => (rigid a ha).1,
    fun a ha => (rigid a ha).2⟩
  intro a ha z hz
  have union : (outN adj a ∩ A) ∪ (outN adj a ∩ Z) = outN adj a := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr (heads a ha)]
  have count := card_union_of_disjoint (disj.mono
    (inter_subset_right : outN adj a ∩ A ⊆ A)
    (inter_subset_right : outN adj a ∩ Z ⊆ Z))
  rw [union, H.regular, (rigid a ha).1] at count
  have equal : outN adj a ∩ Z = Z := eq_of_subset_of_card_le inter_subset_right (by omega)
  have member : z ∈ outN adj a ∩ Z := equal.symm ▸ hz
  exact (mem_outN adj a z).mp (mem_inter.mp member).1

end Ambient

namespace TopFrame

variable {adj} (f : TopFrame adj)

theorem z_avoids_A (H : Ambient adj) (z : V) (hz : z ∈ f.Z) (a : V) (ha : a ∈ f.A) : ¬ adj z a := by
  intro edge
  obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (outN adj a ∩ f.A).card by rw [f.internalOut a ha]; omega)
  exact H.noTri z a b edge ((mem_outN adj a b).mp (mem_inter.mp hb).1)
    (f.complete b (mem_inter.mp hb).2 z hz)

theorem internal_second_three (H : Ambient adj) (a : V) (ha : a ∈ f.A) :
    3 ≤ (second adj a ∩ f.A).card := by
  let W := outN adj a ∩ f.A
  have cardW : W.card = 3 := f.internalOut a ha
  obtain ⟨b, hb, hs⟩ := H.small W (card_pos.mp (by omega)) (by omega)
  have bound : outN adj b ∩ f.A ⊆ W ∪ (second adj a ∩ f.A) := by
    intro x hx
    by_cases edge : adj a x
    · exact mem_union_left _ (mem_inter.mpr ⟨(mem_outN adj a x).mpr edge, (mem_inter.mp hx).2⟩)
    · apply mem_union_right
      refine mem_inter.mpr ⟨(mem_second adj a x).mpr ⟨?_, edge, b,
        (mem_outN adj a b).mp (mem_inter.mp hb).1,
        (mem_outN adj b x).mp (mem_inter.mp hx).1⟩, (mem_inter.mp hx).2⟩
      intro equal
      subst x
      exact H.noDigon a b ((mem_outN adj a b).mp (mem_inter.mp hb).1)
        ((mem_outN adj b a).mp (mem_inter.mp hx).1)
  have count := degree_bound (outN adj b ∩ f.A) W (second adj a ∩ f.A) bound
  have equal : (outN adj b ∩ f.A) ∩ W = outN adj b ∩ W := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (mem_inter.mp h.2).2⟩, h.2⟩⟩
  rw [equal, f.internalOut b (mem_inter.mp hb).2] at count
  rw [cardW] at hs
  omega

@[expose] def external (z : V) : Finset V := outN adj z \ (f.A ∪ f.Z)

theorem external_count (H : Ambient adj) (z : V) (hz : z ∈ f.Z) :
    (f.external z).card + (outN adj z ∩ f.Z).card = 10 := by
  have count := card_sdiff_add_card_inter (outN adj z) (f.A ∪ f.Z)
  have equal : outN adj z ∩ (f.A ∪ f.Z) = outN adj z ∩ f.Z := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp (mem_inter.mp hx).2 with ha | hZ
      · exact (f.z_avoids_A H z hz x ha ((mem_outN adj z x).mp (mem_inter.mp hx).1)).elim
      · exact mem_inter.mpr ⟨(mem_inter.mp hx).1, hZ⟩
    · intro hx
      exact mem_inter.mpr ⟨(mem_inter.mp hx).1, mem_union_right _ (mem_inter.mp hx).2⟩
  rw [equal, H.regular] at count
  exact count

theorem external_second (a : V) (ha : a ∈ f.A) (z : V) (hz : z ∈ f.Z) :
    f.external z ⊆ second adj a := by
  intro x hx
  have outside := (mem_sdiff.mp hx).2
  refine (mem_second adj a x).mpr ⟨?_, ?_, z, f.complete a ha z hz,
    (mem_outN adj z x).mp (mem_sdiff.mp hx).1⟩
  · intro equal
    subst x
    exact outside (mem_union_left _ ha)
  · intro edge
    exact outside (f.headsA a ha ((mem_outN adj a x).mpr edge))

theorem head_bound_from_z (H : Ambient adj) (a : V) (ha : a ∈ f.A) (z : V) (hz : z ∈ f.Z)
    (q : ℕ) (smallZ : (outN adj z ∩ f.Z).card ≤ q) : (inN adj a).card ≤ 6 + q := by
  have disj : Disjoint (second adj a ∩ f.A) (f.external z) := by
    apply disjoint_left.mpr
    intro x hx he
    exact (mem_sdiff.mp he).2 (mem_union_left _ (mem_inter.mp hx).2)
  have subset : (second adj a ∩ f.A) ∪ f.external z ⊆ second adj a :=
    union_subset inter_subset_left (f.external_second a ha z hz)
  have count := card_le_card subset
  rw [card_union_of_disjoint disj] at count
  have inside := f.internal_second_three H a ha
  have outside := f.external_count H z hz
  have bad := H.bad a
  omega

theorem heads_eight (H : Ambient adj) (a : V) (ha : a ∈ f.A) : (inN adj a).card ≤ 8 := by
  obtain ⟨z, hz, small⟩ := H.small f.Z
    (card_pos.mp (by rw [f.cardZ]; omega)) (by rw [f.cardZ]; omega)
  rw [f.cardZ] at small
  exact f.head_bound_from_z H a ha z hz 2 (by omega)

theorem z_in_lower (z : V) (hz : z ∈ f.Z) :
    10 + (inN adj z ∩ f.Z).card ≤ (inN adj z).card := by
  have subset : f.A ∪ (inN adj z ∩ f.Z) ⊆ inN adj z := by
    intro x hx
    rcases mem_union.mp hx with ha | hi
    · exact (mem_inN adj z x).mpr (f.complete x ha z hz)
    · exact (mem_inter.mp hi).1
  have count := card_le_card subset
  rw [card_union_of_disjoint (f.disj.mono_right inter_subset_right), f.cardA] at count
  exact count

theorem some_z_at_most_one (H : Ambient adj) : ∃ z ∈ f.Z, (outN adj z ∩ f.Z).card ≤ 1 := by
  by_contra missing
  have minimum (z : V) (hz : z ∈ f.Z) : 2 ≤ (outN adj z ∩ f.Z).card := by
    have h : ¬ (outN adj z ∩ f.Z).card ≤ 1 := fun h => missing ⟨z, hz, h⟩
    omega
  have rigid := rigid_small adj H.loopless H.noDigon H.noTri H.small f.Z 2
    (by omega) (by omega) f.cardZ minimum
  have high (z : V) (hz : z ∈ f.Z) : (inN adj z).card = 12 := by
    have lower := f.z_in_lower z hz
    rw [(rigid z hz).2] at lower
    have upper := H.indegree_cap z
    omega
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < f.Z.card by rw [f.cardZ]; omega)
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (outN adj z ∩ f.Z).card by rw [(rigid z hz).1]; omega)
  have bound := (H.frame z (high z hz)).heads_eight H u (mem_inter.mp hu).1
  have uh := high u (mem_inter.mp hu).2
  omega

theorem heads_seven (H : Ambient adj) (a : V) (ha : a ∈ f.A) : (inN adj a).card ≤ 7 := by
  obtain ⟨z, hz, small⟩ := f.some_z_at_most_one H
  exact f.head_bound_from_z H a ha z hz 1 small

end TopFrame

end CH.CompromiseTenTop

#print axioms CH.CompromiseTenTop.Ambient.indegree_cap
#print axioms CH.CompromiseTenTop.TopFrame.heads_eight
#print axioms CH.CompromiseTenTop.TopFrame.some_z_at_most_one
#print axioms CH.CompromiseTenTop.TopFrame.heads_seven
