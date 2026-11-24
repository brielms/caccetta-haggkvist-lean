import checkpoints.shen_extension.BoundaryShortRowReturn

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota CHRuleCatalog

/-- Retain the full head selected at v. Either a second actual head
covers the whole shell, or every missing shortcut from g through that
shell back into H has a q-1 return wholly inside H. -/
theorem full_or_returns {D V q r t v g} (free : QFree D V q) (cut : 2≤q) (vm : v∈V)
    (reg : OutEq r D V) (gm : g∈outN D V v) (mult : r=q*t+1)
    (boundary : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2 \ ball D V v 1).card+t=r+1)
    (full : (ball D V v 2 \ ball D V v 1)⊆outN D V g)
    (excess : ∃x∈outN D V v,t<(outN D (outN D V v) x).card) :
    (∃a∈outN D V v,a≠g ∧ (ball D V v 2 \ ball D V v 1)⊆outN D V a) ∨
    (∀z∈ball D V v 2 \ ball D V v 1,∀b∈outN D V v,D z b=true → D g b≠true →
      Walk D (outN D V v) b g (q-1)) := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  change Y.card+t=r+1 at one
  have rows a (am : a∈H) : (Y\outN D V a).card+r=Y.card+(outN D H a).card :=
    missing_count free cut vm am (reg a (mem_outN.mp am).1)
  have row := rows g gm
  rw [sdiff_eq_empty_iff_subset.mpr full,card_empty] at row
  by_cases more : ∃a∈H,a≠g ∧ Y⊆outN D V a
  · exact Or.inl more
  right
  have others a (am : a∈H) (ne : a≠g) : t≤(outN D H a).card := by
    have off : ¬Y⊆outN D V a := fun does=>more ⟨a,am,ne,does⟩
    have pos : 0<(Y\outN D V a).card :=
      card_pos.mpr (nonempty_iff_ne_empty.mpr (fun e=>off (sdiff_eq_empty_iff_subset.mp e)))
    have := rows a am
    omega
  intro z zm b bm zb miss
  exact punctured_return free outN_subset cut ((reg v vm).trans mult) boundary gm bm
    (ball_subset (mem_sdiff.mp zm).1) (mem_outN.mp (full zm)).2 zb miss (show t≤(outN D H g).card+1 by omega) others excess

attribute [aesop safe forward (immediate := [free,cut,vm,reg,gm,mult,boundary,one,full,excess])
  (rule_sets := [CHGraphFamilies])] full_or_returns
ch_family_split_result full_or_returns
#print axioms full_or_returns
end LeanCH.BR.LabelledCompromiseRecipe
