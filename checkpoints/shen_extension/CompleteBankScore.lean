import checkpoints.shen_extension.ShortShellPayer

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen PhysicalCycleStock ExteriorPacking

/-- A full labelled bank B and its next bank W expose two full layers plus
all the exterior heads of W. This count is independent of the ambient order. -/
theorem complete_bank_reach {D V q r B} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (bv : B⊆V) (live : B.Nonempty) (root : ∀b∈B,Rooted D V b B)
    (width : (exterior D V B).card=r-1) :
    let W := exterior D V B
    B.card+W.card+(exterior D V W).card≤(neighborhood D V B 2).card := by
  classical
  let W := exterior D V B
  let T := exterior D V W
  have wv : W⊆V := by
    intro w wm; obtain ⟨b,_,hit⟩ := mem_biUnion.mp (mem_sdiff.mp wm).1
    exact outN_subset hit
  have hit b (bm : b∈B) w (wm : w∈W) : D b w=true :=
    (mem_outN.mp (mem_of_mem_erase ((complete_row (root b bm) (reg _ (bv bm)) width).symm ▸ (show w∈exterior D V B from wm)))).2
  have bw : Disjoint B W := disjoint_left.mpr (fun _ bm wm=>(mem_sdiff.mp wm).2 bm)
  have dis : Disjoint (B∪W) T := by
    apply disjoint_left.mpr
    intro a am at'
    obtain ⟨w,wm,wa⟩ := mem_biUnion.mp (mem_sdiff.mp at').1
    rcases mem_union.mp am with bm|wm'
    · exact digonfree free hq (bv bm) (wv wm) (hit a bm w wm) (mem_outN.mp wa).2
    · exact (mem_sdiff.mp at').2 wm'
  have seen : B∪W∪T⊆neighborhood D V B 2 := by
    obtain ⟨b,bm⟩ := live
    intro a am
    rcases mem_union.mp am with prev|far
    · rcases mem_union.mp prev with old|mid
      · exact mem_biUnion.mpr ⟨a,old,self_mem_ball (bv old)⟩
      · exact mem_biUnion.mpr ⟨b,bm,ball_mono_radius (by decide : 1≤2) (ball_of_adj (wv mid) (hit b bm a mid))⟩
    obtain ⟨w,wm,wa⟩ := mem_biUnion.mp (mem_sdiff.mp far).1
    exact mem_biUnion.mpr ⟨b,bm,ball_step (ball_of_adj (wv wm) (hit b bm w wm)) (outN_subset wa) (mem_outN.mp wa).2⟩
  have bound := card_le_card seen
  rwa [card_union_of_disjoint dis,card_union_of_disjoint bw] at bound

/-- No competing numerical growth rule is needed to price two successive
complete banks. One spare native head at the next step increases the score. -/
theorem double_bank_high {D V q r A} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (hr : 2≤r) (fit : r≤q+2) (root : ∀v∈A,Rooted D V v A)
    (width : (exterior D V A).card=r-1)
    (next : ∀z∈exterior D V A,Rooted D V z (exterior D V A))
    (width' : (exterior D V (exterior D V A)).card=r-1) :
    ∀a∈A,3*r<(ball D V a 3).card := by
  let B := exterior D V A
  let W := exterior D V B
  have extV {C : Finset ℕ} : exterior D V C⊆V := by
    intro x xm; obtain ⟨z,_,edge⟩ := mem_biUnion.mp (mem_sdiff.mp xm).1; exact outN_subset edge
  have bb : B.card=r-1 := width
  have ww : W.card=r-1 := width'
  have bound : r-1≤(exterior D V W).card := by
    by_contra! small
    exact (Nat.ne_of_lt small) (short_exterior free (by omega) reg (extV (C:=B))
      (by omega : W.card≤q+1) (card_pos.mp (by omega : 0<W.card)) small.le (by omega)).1
  have grow := complete_bank_reach free (by omega) reg (extV (C:=A))
    (card_pos.mp (by omega : 0<B.card)) next width'
  change B.card+W.card+(exterior D V W).card≤_ at grow
  have all a (am : a∈A) : B⊆outN D V a := by
    intro z zm
    exact mem_of_mem_erase ((complete_row (root a am) (reg a ((root a am).sub am)) width).symm ▸ (show z∈exterior D V A from zm))
  intro a am
  have paid := score_from_bank (m:=0) free (root a am).sub (extV (C:=A))
    (fun x xm=>((root x xm).one x xm).ge) hq (by omega) am (all a am)
    (by rw [filter_true_of_mem all]; omega) grow
  omega

#print axioms complete_bank_reach
#print axioms double_bank_high
end LeanCH.BR.LowShellCycleSelection
