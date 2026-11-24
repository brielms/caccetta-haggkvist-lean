import checkpoints.shen_extension.ReceiverCommonRepair

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota

/-- Every head b with more incoming shell vertices than the whole
short bank can afford must already be a head of one of its rows.
The maximum with one also covers the empty short bank. -/
theorem full_bank_cover {D V q r t v} (free : QFree D V q) (cut : 3≤q)
    (vm : v∈V) (reg : OutEq r D V) (mult : r=q*t+1)
    (br : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2 \ ball D V v 1).card+t=r+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    ∀b∈H,max 1 F.card<(inN D Y b).card → ∃g∈F,D g b=true := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let F:=H.filter fun g=>Y⊆outN D V g
  change Y.card+t=r+1 at one
  change ∀b∈H,max 1 F.card<(inN D Y b).card → ∃g∈F,D g b=true
  intro b bm heavy
  by_contra! fresh
  let Z:=inN D Y b
  change max 1 F.card<Z.card at heavy
  have row a (am : a∈H) : (Y\outN D V a).card+r=Y.card+(outN D H a).card :=
    missing_count free (by omega) vm am (reg a (outN_subset am))
  have zv : Z⊆V := fun _ zm=>ball_subset (mem_sdiff.mp (mem_inN.mp zm).1).1
  have toB w (wm : w∈Z) := (mem_inN.mp wm).2
  have gz g (gm : g∈F) w (wm : w∈Z) := (mem_outN.mp ((mem_filter.mp gm).2 (mem_inN.mp wm).1)).2
  obtain ⟨z,zm⟩ := card_pos.mp (show 0<Z.card by omega)
  have bmiss w (wm : w∈Z) : D b w≠true :=
    digonfree free (by omega) (zv wm) (outN_subset bm) (toB w wm)
  have bill a (am : a∈H) (miss : ∀w∈Z,D a w≠true) : t+Z.card≤(outN D H a).card+1 := by
    have sub : Z⊆Y\outN D V a := fun w wm=>mem_sdiff.mpr ⟨(mem_inN.mp wm).1,
      fun arc=>miss w wm (mem_outN.mp arc).2⟩
    have := card_le_card sub
    have := row a am
    omega
  apply common_repair_false (H:=H) (F:=F) free outN_subset (by omega) ((reg v vm).trans mult) br bm
    (fun bf=>bmiss z zm (gz b bf z zm)) zv toB (fun g gm hit=>by simpa [hit] using fresh g gm)
  · intro g gm
    have budget := row g (mem_filter.mp gm).1
    rw [sdiff_eq_empty_iff_subset.mpr (mem_filter.mp gm).2,card_empty] at budget
    exact ⟨by omega,z,zm,gz g gm z zm⟩
  · intro a am af
    have pos : 0<(Y\outN D V a).card := by
      by_contra! zero
      exact af (mem_filter.mpr ⟨am,sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))⟩)
    have := row a am
    omega
  · intro a am miss
    have := bill a am miss
    have cap := card_le_card (inter_subset_right : outN D H a∩F⊆F)
    omega
  · have := bill b bm bmiss
    omega
  · apply disjoint_left.mpr
    intro g bg gm
    exact free g 3 (by decide) cut (.step (zv zm) (gz g gm z zm)
      (.step (outN_subset bm) (toB z zm) (.step (outN_subset (mem_filter.mp gm).1) (mem_outN.mp bg).2 (.refl _))))

theorem marked_full_bank_cover {D V q} {law : ReceiverLaw} {v}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (size : (ball D V v 2 \ ball D V v 1).card=law.shell)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    ∀b∈H,max 1 F.card<(inN D Y b).card → ∃g∈F,D g b=true := by
  obtain ⟨cut,two,region,mult,_,_⟩ := fit
  exact full_bank_cover free cut vm reg mult (WeightedSD.boundary_regular_outside_pressure_region cut two region)
    (size ▸ one)

attribute [aesop safe forward (immediate := [free,cut,vm,reg,mult,br,one])
  (rule_sets := [CHGraphFamilies])] full_bank_cover
attribute [aesop safe forward (immediate := [free,vm,reg,size,fit,one])
  (rule_sets := [CHGraphFamilies])] marked_full_bank_cover
#print axioms full_bank_cover
#print axioms marked_full_bank_cover
end LeanCH.BR.LabelledCompromiseRecipe
