import checkpoints.shen_extension.ReceiverLastArcCut

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota

/-- The entire set of shell parents of a missed shortcut is priced
at once. Two parents pay the cut, and b keeps its own strict row. -/
theorem second_full_or_cap {D V q r t v g} (free : QFree D V q) (cut : 3≤q)
    (vm : v∈V) (reg : OutEq r D V) (gm : g∈outN D V v) (mult : r=q*t+1)
    (br : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2 \ ball D V v 1).card+t=r+1)
    (full : (ball D V v 2 \ ball D V v 1)⊆outN D V g) :
    (∃a∈outN D V v,a≠g ∧ (ball D V v 2 \ ball D V v 1)⊆outN D V a) ∨
      ∀b∈outN D V v,D g b≠true → (inN D (ball D V v 2 \ ball D V v 1) b).card≤1 := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  change Y.card+t=r+1 at one
  have row a (am : a∈H) : (Y\outN D V a).card+r=Y.card+(outN D H a).card :=
    missing_count free (by omega) vm am (reg a (outN_subset am))
  by_cases more : ∃a∈H,a≠g ∧ Y⊆outN D V a
  · exact Or.inl more
  right
  intro b bm gb
  by_contra! large
  let Z:=inN D Y b
  change 1<Z.card at large
  have zv : Z⊆V := fun _ zm=>ball_subset (mem_sdiff.mp (mem_inN.mp zm).1).1
  have toB z (zm : z∈Z) := (mem_inN.mp zm).2
  have gz z (zm : z∈Z) := (mem_outN.mp (full (mem_inN.mp zm).1)).2
  obtain ⟨z,zm⟩ := card_pos.mp (show 0<Z.card by omega)
  have ne : b≠g := fun eq=>digonfree free (by omega) (outN_subset gm) (zv zm) (gz z zm) (eq ▸ toB z zm)
  have bg : D b g≠true := fun arc=>free g 3 (by decide) cut
    (.step (zv zm) (gz z zm) (.step (outN_subset bm) (toB z zm) (.step (outN_subset gm) arc (.refl _))))
  have paid a (am : a∈H) (off : ∀z∈Z,D a z≠true) : t<(outN D H a).card := by
    have sub : Z⊆Y\outN D V a := fun w wm=>mem_sdiff.mpr ⟨(mem_inN.mp wm).1,
      fun arc=>off w wm (mem_outN.mp arc).2⟩
    have := card_le_card sub
    have := row a am
    omega
  apply blocked_lastCut (H:=H) free outN_subset (by omega) ((reg v vm).trans mult) br gm bm ne gb zv toB
    ⟨z,zm,gz z zm⟩
  · have pay := row g gm
    rw [sdiff_eq_empty_iff_subset.mpr full,card_empty] at pay
    omega
  · intro a am ne
    have positive : 0<(Y\outN D V a).card := by
      by_contra! zero
      exact more ⟨a,am,ne,sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))⟩
    have := row a am
    omega
  · exact ⟨b,bm,paid b bm (fun w wm=>digonfree free (by omega) (zv wm) (outN_subset bm) (toB w wm)),Or.inl bg⟩
  · intro a am off _
    exact paid a am off

attribute [aesop safe forward (immediate := [free,cut,vm,reg,gm,mult,br,one,full])
  (rule_sets := [CHGraphFamilies])] second_full_or_cap
ch_family_split_result second_full_or_cap
#print axioms second_full_or_cap
end LeanCH.BR.LabelledCompromiseRecipe
