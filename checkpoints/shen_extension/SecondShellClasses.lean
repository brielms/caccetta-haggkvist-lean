import checkpoints.shen_extension.ConsecutiveShellBanks

namespace LeanCH.BR.SecondShellClasses
open Finset BRq2 BRq3 BR45 BRsGen

/-- A direction between two labelled roots is impossible when their second
shells are nested in that direction and the target row has at least as many
heads. This needs neither regularity nor any prescribed shell size. -/
theorem missed {D V q u v} (free : QFree D V q) (hq : 2≤q) (uv : u∈V) (vv : v∈V)
    (dist : u≠v) (layers : N2 D V u⊆N2 D V v)
    (degree : (outN D V u).card≤(outN D V v).card) : v∉ball D V u q := by
  have early : v∉ball D V u 1 := by
    intro hit
    have uvHead := ((mem_ball_one uv).mp hit).resolve_left (Ne.symm dist)
    have inside : outN D V v ⊆ (outN D V u).erase v := by
      intro b bm
      have arc := (mem_outN.mp bm).2
      have last : b∈ball D V u 2 := ball_step hit (outN_subset bm) arc
      have first : b∈ball D V u 1 := by
        by_contra no
        exact (mem_N2.mp (layers (mem_N2.mpr ⟨last,no⟩))).2 (X_B1 bm)
      have bu : b≠u := by
        intro same
        subst b
        exact free u 2 (by decide) hq (.step vv (mem_outN.mp uvHead).2 (.step uv arc (.refl u)))
      have bv : b≠v := by rintro rfl; exact loopfree free (by omega) vv arc
      exact mem_erase.mpr ⟨bv,((mem_ball_one uv).mp first).resolve_left bu⟩
    have cut := card_erase_add_one uvHead
    have cap := card_le_card inside
    omega
  apply SharedLayerBarrier.barrier (k:=2) free vv (by decide) early
  intro y ym
  have atV := mem_N2.mp (layers ym)
  obtain ⟨_,j,fit,path⟩ := mem_ball.mp atV.1
  exact ⟨j,by by_contra! no; exact atV.2 (mem_ball.mpr ⟨ball_subset atV.1,j,by omega,path⟩),fit,path⟩

/-- All distinct ordered pairs in a class of equal second shells are
actual holes in the reach relation, including at the full cutoff. -/
theorem class_pairs {D V q} (free : QFree D V q) (hq : 2≤q) {S Y : Finset ℕ}
    (sub : S⊆V) (layers : ∀u∈S,N2 D V u=Y)
    (degree : ∀u∈S,∀v∈S,(outN D V u).card=(outN D V v).card) :
    S.offDiag ⊆ DotClonePairCompletion.orderedIncomparable D V q := by
  intro e em
  obtain ⟨us,vs,ne⟩ := mem_offDiag.mp em
  have eq := (layers e.1 us).trans (layers e.2 vs).symm
  have sizes := degree e.1 us e.2 vs
  exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨sub us,sub vs,ne⟩,
    missed free hq (sub us) (sub vs) ne eq.subset sizes.le,
    missed free hq (sub vs) (sub us) ne.symm eq.symm.subset sizes.ge⟩

attribute [aesop safe forward (immediate := [free,hq,uv,vv,dist,layers,degree])
  (rule_sets := [CHGraphFamilies])] missed
attribute [aesop safe forward (immediate := [free,hq,sub,layers,degree])
  (rule_sets := [CHGraphFamilies])] class_pairs

#print axioms missed
#print axioms class_pairs
end LeanCH.BR.SecondShellClasses
