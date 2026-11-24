import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BRq2Ball
/-! The graph content of extension clause 13216332 after simplifying the two
prefix counters on row 22. Only the pinned arc 0 → 5 and the exclusion of
digons are needed for the counting step on row 5. -/
namespace LeanCH.BR.SATBoundaryPilot
open LeanCH.BR LeanCH.BR.BRq2 LeanCH.BR.BRq3 Finset

theorem late_target {D : CH.Digraph} {V A T E : Finset ℕ} {x y r d : ℕ}
    (first : y ∈ ball D V x r) (choice : y ∈ A ∪ T) (targets : T ⊆ V)
    (need : ∀ a ∈ A, E.card + d ≤ (outN D (T ∪ E) a).card) :
    y ∈ T ∨ d ≤ (T ∩ ball D V x (r+1)).card := by
  rcases mem_union.mp choice with ha | ht
  · right
    have sub : outN D (T ∪ E) y ⊆ (T ∩ ball D V x (r+1)) ∪ E := by
      intro z hz
      obtain ⟨menu, edge⟩ := mem_outN.mp hz
      rcases mem_union.mp menu with zt | ze
      · exact mem_union_left _ (mem_inter.mpr ⟨zt,ball_step first (targets zt) edge⟩)
      · exact mem_union_right _ ze
    have bound := (card_le_card sub).trans (card_union_le _ _)
    have := need y ha
    omega
  · exact Or.inl ht

theorem late_13216332 {D : CH.Digraph} {V : Finset ℕ}
    (vertices : range 23 ⊆ V) (free : QFree D V 2) (pinned : D 0 5 = true)
    (first : D 22 5 = true ∨ D 22 6 = true)
    (count : 2 ≤ (outN D ((range 7).erase 5) 5).card) :
    D 5 2 = true ∨ (({1,4,6} : Finset ℕ) ∩ ball D V 22 2).Nonempty := by
  classical
  by_cases two : D 5 2 = true
  · exact Or.inl two
  right
  let T : Finset ℕ := {1,4,6}
  have ts : T ⊆ V := (show T ⊆ range 23 by decide).trans vertices
  have xmem := vertices (by decide : 22∈range 23)
  have five := vertices (by decide : 5∈range 23)
  obtain arc|arc := first
  · have zero : D 5 0 ≠ true := fun back=>free 0 2 (by decide) (by decide)
        (.step five pinned (.step (vertices (by decide : 0∈range 23)) back (.refl 0)))
    have sub : outN D ((range 7).erase 5) 5 ⊆ outN D (T ∪ {3}) 5 := by
      intro z hz
      obtain ⟨menu,edge⟩ := mem_outN.mp hz
      have ne0 : z≠0 := fun eq => zero (eq ▸ edge)
      have ne2 : z≠2 := fun eq => two (eq ▸ edge)
      obtain ⟨ne5,small⟩ := mem_erase.mp menu
      have lt := mem_range.mp small
      apply mem_outN.mpr
      refine ⟨?_,edge⟩
      simp only [T,mem_union,mem_insert,mem_singleton]
      omega
    have budget := count.trans (card_le_card sub)
    have path := (mem_ball_one xmem).mpr (Or.inr (mem_outN.mpr ⟨five,arc⟩))
    rcases late_target (A:={5}) (T:=T) (E:={3}) (d:=1) path (by decide) ts
        (by intro a ha; obtain rfl := mem_singleton.mp ha; simpa using budget) with h|h
    · exact False.elim ((by decide : 5∉T) h)
    · exact card_pos.mp h
  · have six : 6∈T := by decide
    have path := (mem_ball_one xmem).mpr (Or.inr (mem_outN.mpr ⟨ts six,arc⟩))
    exact ⟨6,mem_inter.mpr ⟨six,ball_mono_radius (by decide : 1≤2) path⟩⟩
#print axioms late_target
#print axioms late_13216332
end LeanCH.BR.SATBoundaryPilot

