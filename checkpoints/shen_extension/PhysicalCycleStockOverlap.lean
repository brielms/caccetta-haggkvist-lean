import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

/-- When all second-shell labels of one origin are in its cycle exterior,
that origin can reach a different origin of the same first-layer bank in
three steps only if the latter is the extra first head. -/
theorem first_side_single_contact {D V q u v w C} (free : QFree D V q) (hq : 4 ≤ q)
    (hu : u ∈ V) (hv : v ∈ V) (dist : u ≠ v)
    (first : outN D V u = insert w C) (toBank : C ⊆ outN D V v)
    (covered : N2 D V u ⊆ exterior D V C)
    (path : v ∈ ball D V u 3) : v = w := by
  obtain ⟨_, l, fit, road⟩ := mem_ball.mp path
  cases road with
  | refl => exact (dist rfl).elim
  | @step x a z m av xa tail =>
    have ha : a ∈ outN D V u := mem_outN.mpr ⟨av, xa⟩
    rcases mem_insert.mp (first ▸ ha) with e | common
    · subst a
      cases tail with
      | refl => rfl
      | @step x b z n bv wb endPath =>
        have place : b ∈ outN D V w := mem_outN.mpr ⟨bv, wb⟩
        rw [outN_X_eq (free.mono_bound hq) hu ha] at place
        rcases mem_union.mp (outN_subset place) with early | second
        · rcases mem_insert.mp (first ▸ early) with self | inside
          · exact (loopfree free (by omega) av (self ▸ wb)).elim
          · exact (free v _ (by omega) (by omega)
              (.step bv (mem_outN.mp (toBank inside)).2 endPath)).elim
        · obtain ⟨parents, _⟩ := mem_sdiff.mp (covered second)
          obtain ⟨p, pc, pb⟩ := mem_biUnion.mp parents
          exact (free v _ (by omega) (by omega)
            (.step (outN_subset (toBank pc)) (mem_outN.mp (toBank pc)).2
              (.step bv (mem_outN.mp pb).2 endPath))).elim
    · exact (free v _ (by omega) (by omega)
        (.step av (mem_outN.mp (toBank common)).2 tail)).elim

/-- Exterior excess beyond the whole actual second shell forces a physical
arc into the extra first head. -/
theorem first_side_fast_of_width {D V q u w C} (free : QFree D V q) (hq : 4 ≤ q)
    (hu : u ∈ V) (first : outN D V u = insert w C)
    (wide : (N2 D V u).card < (exterior D V C).card) :
    ∃ x ∈ C, D x w = true := by
  by_contra! no
  have inside : exterior D V C ⊆ N2 D V u := by
    intro y hy
    obtain ⟨parents, off⟩ := mem_sdiff.mp hy
    obtain ⟨a, ac, edge⟩ := mem_biUnion.mp parents
    have firstRow : a ∈ outN D V u := first.symm ▸ mem_insert_of_mem ac
    rw [outN_X_eq (free.mono_bound hq) hu firstRow] at edge
    rcases mem_union.mp (outN_subset edge) with low | hy
    · rcases mem_insert.mp (first ▸ low) with equal | hc
      · exact (no a ac (equal ▸ (mem_outN.mp edge).2)).elim
      · exact (off hc).elim
    · exact hy
  exact (not_lt_of_ge (card_le_card inside)) wide

#print axioms first_side_single_contact
#print axioms first_side_fast_of_width
end LeanCH.BR.PhysicalCycleStock
