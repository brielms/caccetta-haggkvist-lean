import checkpoints.shen_extension.MixedResidualDebt

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- When every cycle row reaches a complete bank, every row also reaches
the next two exteriors within three steps. A returning label of the first
exterior cannot occupy either later set. Count the actual direct heads
of each row, including its exceptional head if it has one. -/
theorem restored_rows {D V q r C Z} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (hr : 3≤r) (fit : r≤q+2) (roots : ∀c∈C,Rooted D V c C)
    (zv : Z⊆V) (width : Z.card=r-1) (zroot : ∀z∈Z,Rooted D V z Z)
    (outer : (exterior D V Z).card=r-1) (hit : ∀c∈C,∃z∈Z,D c z=true)
    (back : ∀d∈exterior D V C,d∉Z → ∃c∈C,D d c=true) :
    ∀c∈C,3*r<(ball D V c 3).card := by
  classical
  let W := exterior D V Z
  let T := exterior D V W
  have wv : W⊆V := by
    intro w wm; obtain ⟨z,_,arc⟩ := mem_biUnion.mp (mem_sdiff.mp wm).1; exact outN_subset arc
  have ww : W.card=r-1 := outer
  have tcount : r-1≤T.card := by
    by_contra! small
    exact small.ne (short_exterior free (by omega) reg wv (by omega) (card_pos.mp (by omega)) small.le (by omega)).1
  have zw z (zm : z∈Z) w (wm : w∈W) : D z w=true :=
    (mem_outN.mp (mem_of_mem_erase ((complete_row (zroot z zm) (reg _ (zv zm)) outer).symm ▸
      (show w∈exterior D V Z from wm)))).2
  have toW c (cm : c∈C) w (wm : w∈W) : Walk D V c w 2 := by
    obtain ⟨z,zm,cz⟩ := hit c cm
    exact .step (zv zm) cz (.step (wv wm) (zw z zm w wm) (.refl w))
  have toT c (cm : c∈C) x (xm : x∈T) : Walk D V c x 3 := by
    obtain ⟨w,wm,wx⟩ := mem_biUnion.mp (mem_sdiff.mp xm).1
    exact (toW c cm w wm).snoc (outN_subset wx) (mem_outN.mp wx).2
  have avoid c (cm : c∈C) x (xm : x∈W∪T) (edge : D x c=true) : False := by
    rcases mem_union.mp xm with wm|tm
    · exact free c 3 (by decide) (by omega) ((toW c cm x wm).snoc ((roots c cm).sub cm) edge)
    · exact free c 4 (by decide) hq ((toT c cm x tm).snoc ((roots c cm).sub cm) edge)
  have separated : Disjoint C (W∪T) := by
    apply disjoint_left.mpr
    intro c cm wm
    rcases mem_union.mp wm with w|tt
    · exact free c 2 (by decide) (by omega) (toW c cm c w)
    · exact free c 3 (by decide) (by omega) (toT c cm c tt)
  have exteriorDis : Disjoint (exterior D V C) (W∪T) := by
    apply disjoint_left.mpr
    intro x xe other
    by_cases xz : x∈Z
    · rcases mem_union.mp other with xw|xt
      · exact (mem_sdiff.mp xw).2 xz
      obtain ⟨w,wm,wx⟩ := mem_biUnion.mp (mem_sdiff.mp xt).1
      exact digonfree free (by omega) (zv xz) (wv wm) (zw x xz w wm) (mem_outN.mp wx).2
    obtain ⟨c,cm,arc⟩ := back x xe xz
    exact avoid c cm x other arc
  intro c cm
  let B := ball D C c 3
  let H := (outN D V c).erase (internalHead D C c)
  have sub : H⊆exterior D V C := by
    dsimp only [H]
    rw [row_exterior (roots c cm)]
    exact inter_subset_left
  have bh : Disjoint B H := disjoint_left.mpr (fun x xb xh=>(mem_sdiff.mp (sub xh)).2 (ball_subset xb))
  have bw : Disjoint (B∪H) (W∪T) := disjoint_union_left.mpr ⟨separated.mono_left ball_subset,exteriorDis.mono_left sub⟩
  have wt : Disjoint W T := disjoint_left.mpr (fun _ wm tm=>(mem_sdiff.mp tm).2 wm)
  have covered : (B∪H)∪(W∪T)⊆ball D V c 3 := by
    refine union_subset (union_subset (ShellCycleSupply.lift_ball (roots c cm).sub) ?_) (union_subset ?_ ?_)
    · intro x xm
      exact ball_mono_radius (by decide : 1≤3) (X_B1 (mem_of_mem_erase xm))
    · intro w wm
      exact mem_ball.mpr ⟨wv wm,2,by decide,toW c cm w wm⟩
    · intro x xm
      obtain ⟨w,wm,wx⟩ := mem_biUnion.mp (mem_sdiff.mp xm).1
      exact mem_ball.mpr ⟨outN_subset wx,3,le_rfl,toT c cm x xm⟩
  have sizes := card_le_card covered
  rw [card_union_of_disjoint bw,card_union_of_disjoint bh,card_union_of_disjoint wt] at sizes
  have bc : 4≤B.card := ball_one_growth (free.mono_set (roots c cm).sub) (fun a am=>((roots a am).one a am).ge) cm 3 (by omega)
  have heads : H.card=r-1 := by
    rw [show H=(outN D V c).erase (internalHead D C c) from rfl,card_erase_of_mem
      (outN_mono (roots c cm).sub c (successor_mem (roots c cm))),reg c ((roots c cm).sub cm)]
  omega

#print axioms restored_rows
end LeanCH.BR.LowShellCycleSelection
