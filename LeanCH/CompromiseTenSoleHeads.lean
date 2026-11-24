module

public import LeanCH.CompromiseTenSoleBounds

set_option linter.style.header false

/-! The nonreturning exception cannot head a good vertex. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame.SoleReturn

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable {f : Frame adj} (s : SoleReturn f) (H : Ambient adj)
include s H

theorem common_y_parents : f.goodOnes ⊆ inN adj s.y ∩ f.good := by
  intro g hg
  exact mem_inter.mpr ⟨(mem_inN adj s.y g).mpr
    ((mem_outN adj g s.y).mp (((s.common H).2 g hg).2 s.y_mem)), (mem_filter.mp hg).1⟩

theorem internal_two_parent_or_missed (b : V) (_hb : b ∈ f.A) (xb : adj s.x b)
    (g : V) (hg : g ∈ f.goodInternalTwos) :
    g ∈ (inN adj s.y ∩ f.good) ∪ (f.missing b ∩ f.good) := by
  have gGood := (mem_filter.mp hg).1
  by_cases parent : adj g s.y
  · exact mem_union_left _ (mem_inter.mpr ⟨(mem_inN adj s.y g).mpr parent, gGood⟩)
  · have degree := (mem_filter.mp hg).2
    have lower := s.good_minimum H g gGood
    have split := f.good_exceptional_degrees g
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (outN adj g ∩ f.exceptional).card by omega)
    have member := (mem_inter.mp hx).2
    rw [s.exceptions, mem_insert, mem_singleton] at member
    have gx : adj g s.x := by
      rcases member with equal | equal
      · subst x
        exact (mem_outN adj g s.x).mp (mem_inter.mp hx).1
      · subst x
        exact False.elim (parent ((mem_outN adj g s.y).mp (mem_inter.mp hx).1))
    exact mem_union_right _ (mem_inter.mpr ⟨mem_sdiff.mpr ⟨(mem_filter.mp gGood).1,
      fun outgoing => H.noTri g s.x b gx xb ((mem_outN adj b g).mp outgoing)⟩, gGood⟩)

theorem two_ones_many_y_parents (ones : f.goodOnes.card = 2)
    (b : V) (hb : b ∈ f.A) (xb : adj s.x b) : 4 ≤ (inN adj s.y ∩ f.good).card := by
  let P := inN adj s.y ∩ f.good
  let M := f.missing b ∩ f.good
  have lP : f.goodOnes ⊆ P := s.common_y_parents H
  have lM : f.goodOnes ⊆ M := by
    intro g hg
    exact mem_inter.mpr ⟨s.target_missing_common H b hb xb hg, (mem_filter.mp hg).1⟩
  have subset : f.goodOnes ∪ f.goodInternalTwos ⊆ P ∪ M := by
    intro g hg
    rcases mem_union.mp hg with one | two
    · exact mem_union_left _ (lP one)
    · exact s.internal_two_parent_or_missed H b hb xb g two
  have disj : Disjoint f.goodOnes f.goodInternalTwos := by
    apply disjoint_left.mpr
    intro g one two
    have oneDegree := (mem_filter.mp one).2
    have twoDegree := (mem_filter.mp two).2
    omega
  have first := card_le_card subset
  rw [card_union_of_disjoint disj] at first
  have second := card_le_card (subset_inter lP lM)
  have count := card_union_add_card_inter P M
  have many := f.two_high_three_internal_twos H s.two (s.good_minimum H) ones
  have missing := s.target_good_missing H b hb xb
  change M.card ≤ 3 at missing
  change 4 ≤ P.card
  omega

theorem y_head_bound (g : V) (hg : g ∈ f.good) (edge : adj s.y g) :
    f.zOut g + (inN adj s.y ∩ f.good).card ≤ 6 ∧
      (¬ adj g s.x → f.zOut g + (inN adj s.y ∩ f.good).card + 1 ≤ 6) := by
  let P := inN adj s.y ∩ f.good
  change f.zOut g + P.card ≤ 6 ∧ (¬ adj g s.x → f.zOut g + P.card + 1 ≤ 6)
  have noY : ¬ adj g s.y := H.noDigon s.y g edge
  have gNotP : g ∉ P := fun h => noY ((mem_inN adj s.y g).mp (mem_inter.mp h).1)
  have disj : Disjoint (outN adj g ∩ f.good) (insert g P) := by
    apply disjoint_left.mpr
    intro a ha hin
    have ga := (mem_outN adj g a).mp (mem_inter.mp ha).1
    rcases mem_insert.mp hin with equal | parent
    · subst a
      exact H.loopless g ga
    · exact H.noTri s.y g a edge ga ((mem_inN adj s.y a).mp (mem_inter.mp parent).1)
  have subset : (outN adj g ∩ f.good) ∪ insert g P ⊆ f.good :=
    union_subset inter_subset_right (insert_subset hg inter_subset_right)
  have bound := card_le_card subset
  rw [card_union_of_disjoint disj, card_insert_of_notMem gNotP] at bound
  have size : f.good.card = 6 := by have := f.good_exceptional_card; have := s.two; omega
  rw [size] at bound
  have outX : outN adj g ∩ f.exceptional ⊆ {s.x} := by
    intro a ha
    have member := (mem_inter.mp ha).2
    rw [s.exceptions, mem_insert, mem_singleton] at member
    rcases member with equal | equal
    · exact mem_singleton.mpr equal
    · subst a
      exact False.elim (noY ((mem_outN adj g s.y).mp (mem_inter.mp ha).1))
  have cap := card_le_card outX
  rw [card_singleton] at cap
  have split := f.good_exceptional_degrees g
  refine ⟨by omega, ?_⟩
  intro noX
  have zero : (outN adj g ∩ f.exceptional).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    have equal := mem_singleton.mp (outX ha)
    subst a
    exact noX ((mem_outN adj g s.x).mp (mem_inter.mp ha).1)
  omega

theorem y_avoids_good (b : V) (hb : b ∈ f.A) (xb : adj s.x b)
    (g : V) (hg : g ∈ f.good) : ¬ adj s.y g := by
  intro edge
  have bounds := s.y_head_bound H g hg edge
  have degree := s.good_minimum H g hg
  by_cases two : f.goodOnes.card = 2
  · have parents := s.two_ones_many_y_parents H two b hb xb
    omega
  · have shape := s.small_shape H
    have three : f.goodOnes.card = 3 := by omega
    have subset : f.goodOnes ⊆ f.missing b ∩ f.good := by
      intro a ha
      exact mem_inter.mpr ⟨s.target_missing_common H b hb xb ha, (mem_filter.mp ha).1⟩
    have cap := s.target_good_missing H b hb xb
    have equal : f.goodOnes = f.missing b ∩ f.good := eq_of_subset_of_card_le subset (by omega)
    have gNotOne : g ∉ f.goodOnes := by
      intro member
      have parent := s.common_y_parents H member
      exact H.noDigon s.y g edge ((mem_inN adj s.y g).mp (mem_inter.mp parent).1)
    have bg : adj b g := by
      by_contra misses
      apply gNotOne
      rw [equal]
      exact mem_inter.mpr ⟨mem_sdiff.mpr ⟨(mem_filter.mp hg).1,
        fun outgoing => misses ((mem_outN adj b g).mp outgoing)⟩, hg⟩
    have noX : ¬ adj g s.x := fun gx => H.noTri g s.x b gx xb bg
    have stronger := bounds.2 noX
    have parents := card_le_card (s.common_y_parents H)
    omega

theorem y_out_subset (b : V) (hb : b ∈ f.A) (xb : adj s.x b) :
    outN adj s.y ∩ f.Z ⊆ {s.x} := by
  intro z hz
  have edge := (mem_outN adj s.y z).mp (mem_inter.mp hz).1
  rcases s.good_or_xy z (mem_inter.mp hz).2 with good | equal | equal
  · exact False.elim (s.y_avoids_good H b hb xb z good edge)
  · exact mem_singleton.mpr equal
  · subst z
    exact False.elim (H.loopless s.y edge)

theorem y_at_most_one (b : V) (hb : b ∈ f.A) (xb : adj s.x b) : f.zOut s.y ≤ 1 := by
  have bound := card_le_card (s.y_out_subset H b hb xb)
  rw [card_singleton] at bound
  exact bound

theorem y_zero_of_target_sees (b : V) (hb : b ∈ f.A) (xb : adj s.x b) (byEdge : adj b s.y) :
    f.zOut s.y = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have equal := mem_singleton.mp (s.y_out_subset H b hb xb hz)
  subst z
  exact H.noTri s.x b s.y xb byEdge ((mem_outN adj s.y s.x).mp (mem_inter.mp hz).1)

end CH.CompromiseTenFrame.Frame.SoleReturn

#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.y_avoids_good
#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.y_at_most_one
#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.y_zero_of_target_sees
