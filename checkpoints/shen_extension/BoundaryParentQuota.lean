import checkpoints.shen_extension.BoundaryTightParentReach

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45 BypassRepair LoneRow

/-- Labels distinct from the marked row that neither send nor receive its arc. -/
def neutral (D : CH.Digraph) (H : Finset ℕ) (g : ℕ) :=
  (H.erase g)\(outN D H g ∪ inN D H g)

theorem partition_card {D H q g} (free : QFree D H q) (cut : 2≤q) (gm : g∈H) :
    (inN D H g).card+(outN D H g).card+(neutral D H g).card+1=H.card := by
  classical
  have sub : outN D H g ∪ inN D H g ⊆ H.erase g := by
    intro a am
    obtain m|m := mem_union.mp am
    · exact mem_erase.mpr ⟨fun e=>loopfree free (by omega) gm (e ▸ (mem_outN.mp m).2),outN_subset m⟩
    · exact mem_erase.mpr ⟨fun e=>loopfree free (by omega) gm (e ▸ (mem_inN.mp m).2),(mem_inN.mp m).1⟩
  have dis : Disjoint (outN D H g) (inN D H g) := disjoint_left.mpr fun a am an=>
    digonfree free cut gm (outN_subset am) (mem_outN.mp am).2 (mem_inN.mp an).2
  have step := card_sdiff_add_card_eq_card sub
  rw [card_union_of_disjoint dis] at step
  have := card_erase_add_one gm
  unfold neutral
  omega

/-- Each internal parent of a parent of g belongs to its parent set or to
the neutral set. All labels retain their original direction in this bound. -/
theorem parent_room {D H q g a} (free : QFree D H q) (cut : 3≤q) (gm : g∈H)
    (am : a∈inN D H g) :
    (inN D H a).card≤(inN D (inN D H g) a).card+(neutral D H g).card := by
  have ⟨ah,ag⟩ := mem_inN.mp am
  apply (card_le_card (t:=inN D (inN D H g) a ∪ neutral D H g) _).trans (card_union_le ..)
  intro h hm
  obtain ⟨hh,ha⟩ := mem_inN.mp hm
  by_cases par : h∈inN D H g
  · exact mem_union_left _ (mem_inN.mpr ⟨par,ha⟩)
  · have ne : h≠g := fun e=>digonfree free (by omega) gm ah (e ▸ ha) ag
    have off : h∉outN D H g := fun m=>free g 3 (by decide) cut
      (.step hh (mem_outN.mp m).2 (.step ah ha (.step gm ag (.refl _))))
    exact mem_union_right _ (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,hh⟩,fun m=>(mem_union.mp m).elim off par⟩)

/-- A single exceptional column still leaves a lower-quota obstruction on
the actual parents of g in the reversed graph. -/
theorem parent_order {D H q t g b k} (free : QFree D H q) (cut : 3≤q) (gm : g∈H)
    (live : (inN D H g).Nonempty)
    (col : ∀a∈inN D H g,t≤(inN D H a).card+(if a=b then 1 else 0))
    (fund : k+(neutral D H g).card≤t) (none : NoHost q k) (near : NoNearHost q k) :
    q*k<(inN D H g).card := by
  classical
  let P:=inN D H g
  let E : CH.Digraph := fun u v=>D v u
  have safe : QFree E P q := (free.mono_set (show P⊆H from fun _ m=>(mem_inN.mp m).1)).reverse
  have lower a (am : a∈P) : k≤(outN E P a).card+(if a=b then 1 else 0) := by
    have room := parent_room free cut gm am
    have cost := col a am
    change k≤(inN D (inN D H g) a).card+_
    omega
  by_contra! small
  by_cases all : ∀a∈P,k≤(outN E P a).card
  · exact none E P live small safe all
  push Not at all
  obtain ⟨a,am,short⟩ := all
  have pay := lower a am
  have eq : a=b := by by_contra ne; simp [ne] at pay; omega
  subst a
  apply near E P b am small safe
  · simp at pay
    omega
  · intro a am ne
    simpa [ne] using lower a am

attribute [aesop safe forward (immediate := [free,cut,gm,live,col,fund,none,near]) (rule_sets := [CHGraphFamilies])]
  parent_order
#print axioms partition_card
#print axioms parent_room
#print axioms parent_order
end LeanCH.BR.BoundaryTightParentReach
