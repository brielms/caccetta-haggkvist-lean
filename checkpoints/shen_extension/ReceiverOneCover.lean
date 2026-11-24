import checkpoints.shen_extension.ReceiverMenuRepair

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota

/-- One actual full head covers the whole collection B at once. -/
theorem one_cover {D V q r t v} {B : Finset ℕ} (free : QFree D V q) (cut : 3≤q)
    (vm : v∈V) (reg : OutEq r D V) (mult : r=q*t+1)
    (br : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2 \ ball D V v 1).card+t=r+1)
    (bh : B⊆outN D V v) (live : B.Nonempty) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    (∀b∈B,max 1 F.card<(inN D Y b).card) → ∃g∈F,B⊆outN D H g := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let F:=H.filter fun g=>Y⊆outN D V g
  change Y.card+t=r+1 at one
  change (∀b∈B,max 1 F.card<(inN D Y b).card) → ∃g∈F,B⊆outN D H g
  intro heavy
  by_contra! fresh
  have yv : Y⊆V := sdiff_subset.trans ball_subset
  have row a (am : a∈H) : (Y\outN D V a).card+r=Y.card+(outN D H a).card :=
    missing_count free (by omega) vm am (reg a (outN_subset am))
  have sees g (gm : g∈F) z (zm : z∈Y) := (mem_outN.mp ((mem_filter.mp gm).2 zm)).2
  have witness b (bm : b∈B) : ∃z∈Y,D z b=true := by
    obtain ⟨z,zm⟩ := card_pos.mp (show 0<(inN D Y b).card by have := heavy b bm; omega)
    exact ⟨z,(mem_inN.mp zm).1,(mem_inN.mp zm).2⟩
  have dis : Disjoint B F := disjoint_left.mpr fun b bm bf=>by
    obtain ⟨z,zm,zb⟩ := witness b bm
    exact digonfree free (by omega) (yv zm) (outN_subset (bh bm)) zb (sees b bf z zm)
  have bill a (am : a∈H) b (bm : b∈B) (miss : ∀z∈inN D Y b,D a z≠true) :
      t+(inN D Y b).card≤(outN D H a).card+1 := by
    have sub : inN D Y b⊆Y\outN D V a := fun w wm=>mem_sdiff.mpr ⟨(mem_inN.mp wm).1,
      fun arc=>miss w wm (mem_outN.mp arc).2⟩
    have := card_le_card sub
    have := row a am
    omega
  apply menu_repair_false (D:=D) (H:=H) (F:=F) free outN_subset (by omega) ((reg v vm).trans mult) br bh dis yv
  · intro g gm
    have budget := row g (mem_filter.mp gm).1
    rw [sdiff_eq_empty_iff_subset.mpr (mem_filter.mp gm).2,card_empty] at budget
    refine ⟨by omega,?_,?_⟩
    · intro b bm
      obtain ⟨z,zm,zb⟩ := witness b bm
      exact ⟨z,zm,sees g gm z zm,zb⟩
    · have nope := fresh g gm
      by_contra! all
      exact nope (fun b bm=>mem_outN.mpr ⟨bh bm,by simpa using all b bm⟩)
  · intro a am af
    have pos : 0<(Y\outN D V a).card := by
      by_contra! zero
      exact af (mem_filter.mpr ⟨am,sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))⟩)
    have := row a am
    omega
  · intro a am bad
    have misses : ∃b∈B,∀z∈inN D Y b,D a z≠true := by
      by_contra! all
      apply bad
      intro b bm
      obtain ⟨z,zm,az⟩ := all b bm
      exact ⟨z,(mem_inN.mp zm).1,az,(mem_inN.mp zm).2⟩
    obtain ⟨b,bm,off⟩ := misses
    have := bill a am b bm off
    have := heavy b bm
    have := card_le_card (inter_subset_right : outN D H a∩F⊆F)
    omega
  · obtain ⟨b,bm⟩ := live
    have miss z (zm : z∈inN D Y b) : D b z≠true :=
      digonfree free (by omega) (yv (mem_inN.mp zm).1) (outN_subset (bh bm)) (mem_inN.mp zm).2
    have := bill b (bh bm) b bm miss
    have := heavy b bm
    refine ⟨b,bh bm,by omega,disjoint_left.mpr ?_⟩
    intro g bg gm
    obtain ⟨z,zy,zb⟩ := witness b bm
    exact free g 3 (by decide) cut (.step (yv zy) (sees g gm z zy)
      (.step (outN_subset (bh bm)) zb (.step (outN_subset (mem_filter.mp gm).1) (mem_outN.mp bg).2 (.refl _))))

#print axioms one_cover
end LeanCH.BR.LabelledCompromiseRecipe
