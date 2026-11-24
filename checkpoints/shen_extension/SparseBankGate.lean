import checkpoints.shen_extension.SharedCycleContacts

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- A first-layer head in a complete exterior bank cannot return to any
row of the cycle. Count its remaining choices on the actual two layers. -/
theorem fast_head_budget {D V q C u w} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (wx : w∈outN D V u) (we : w∈exterior D V C) (cv : C⊆V)
    (paid : ∀v∈C,exterior D V C⊆outN D V v) :
    (outN D V w).card ≤ ((outN D V u\C).erase w).card+
      (N2 D V u\exterior D V C).card+(outN D (exterior D V C) w).card := by
  classical
  let E := exterior D V C
  have choices : outN D V w⊆((outN D V u\C).erase w ∪ (N2 D V u\E)) ∪ outN D E w := by
    intro a am
    have arc := (mem_outN.mp am).2
    by_cases ae : a∈E
    · exact mem_union_right _ (mem_outN.mpr ⟨ae,arc⟩)
    apply mem_union_left
    rcases mem_union.mp (headX (free.mono_bound hq) uv wx (outN_subset am) arc) with ax|ay
    · apply mem_union_left
      refine mem_erase.mpr ⟨?_,mem_sdiff.mpr ⟨ax,?_⟩⟩
      · rintro rfl
        exact free _ 1 (by decide) (by omega) (.step (outN_subset wx) arc (.refl _))
      · intro ac
        exact digonfree free (by omega) (outN_subset wx) (cv ac) arc (mem_outN.mp (paid a ac we)).2
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ay,ae⟩)
  exact (card_le_card choices).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))

/-- A sparse enough complete exterior bank has no fast origin. The cutoff,
degree, number of additional heads, and internal bank degree are free. -/
theorem sparse_gate {D V q C u d b} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (inside : C⊆outN D V u) (paid : ∀v∈C,exterior D V C⊆outN D V v)
    (minOut : ∀w∈outN D V u,b≤(outN D V w).card)
    (sparse : ∀w∈exterior D V C,(outN D (exterior D V C) w).card≤d)
    (small : 2*(outN D V u\C).card+(N2 D V u).card+d ≤ b+(exterior D V C).card) :
    Disjoint (outN D V u) (exterior D V C) ∧ exterior D V C⊆N2 D V u := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let E := exterior D V C
  have menu := exterior_subset_menu free hq uv inside
  have diff : E\Y⊆X\C := by
    intro a am
    exact (mem_union.mp (menu (mem_sdiff.mp am).1)).resolve_right (mem_sdiff.mp am).2
  have limited := card_le_card diff
  have exchange : (Y\E).card+E.card=(E\Y).card+Y.card := by
    have a := card_sdiff_add_card_inter Y E
    have b := card_sdiff_add_card_inter E Y
    rw [inter_comm E Y] at b
    omega
  have avoid : Disjoint X E := by
    apply disjoint_left.mpr
    intro w wx we
    have outside : w∈X\C := mem_sdiff.mpr ⟨wx,(mem_sdiff.mp we).2⟩
    have many := minOut w wx
    have few : (outN D E w).card≤d := sparse w we
    have gate := fast_head_budget free hq uv wx we (inside.trans outN_subset) paid
    rw [card_erase_of_mem outside] at gate
    have positive := card_pos.mpr ⟨w,outside⟩
    change 2*(X\C).card+Y.card+d≤b+E.card at small
    change (outN D V w).card≤(X\C).card-1+(Y\E).card+(outN D E w).card at gate
    omega
  exact ⟨avoid,fun a ae=>(mem_union.mp (menu ae)).resolve_left
    (fun ax=>disjoint_left.mp avoid (mem_sdiff.mp ax).1 ae)⟩

#print axioms fast_head_budget
#print axioms sparse_gate
end LeanCH.BR.LowShellCycleSelection
