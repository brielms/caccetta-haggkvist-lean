import checkpoints.shen_extension.SameExteriorMiddle

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Rows of the original cycle reach a full third shell through the second
cycle. The union accounting uses the original cycle itself as first carrier. -/
theorem same_exterior_high {D V u C q r} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (uv : u∈V) (first : C⊆outN D V u) (len : q<C.card) (cy : ∀c∈C,Rooted D V c C)
    (fit : r≤q+2) (size : C.card+1=r) (ys : (N2 D V u).card=r)
    (zs : (N3 D V u).card+1=r) (same : exterior D V C=N2 D V u) :
    ∀c∈C,3*r<(ball D V c 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have cv := first.trans xv
  obtain ⟨miss,returning⟩ := middle_return_budgets free (by omega) reg uv first len cy size ys same
  obtain ⟨K,ky,kl,thin,roots⟩ := same_exterior_cycle free hq reg uv first len cy fit size ys (by omega) same
  change K⊆Y at ky
  change (Y\K).card≤1 at thin
  change Y.card=r at ys
  change Z.card+1=r at zs
  have diff := card_sdiff_of_subset first
  rw [reg u uv] at diff
  have xs : (X\C).card≤1 := by dsimp [X]; omega
  have xmenu y (ym : y∈Y) : outN D V y⊆(X∪Y)∪Z := fun b bm=>mem_union.mpr
    (headY (free.mono_bound (by omega : 4≤q)) uv ym (outN_subset bm) (mem_outN.mp bm).2)
  have bank : K.card≤(K.filter (fun k=>Z⊆outN D V k)).card+2 := by
    by_cases anyReturn : ∃w∈X\C,∃y∈Y,D y w=true
    · obtain ⟨w,wm,y,ym,yw⟩ := anyReturn
      have wv := xv (mem_sdiff.mp wm).1
      have lim := returning w wm ⟨y,ym,yw⟩
      change (Y\outN D V w).card+_≤C.card at lim
      have budget : (Y\outN D V w).card≤3 := by omega
      have away : y∉K := fun yk=>no_middle_return free yv wv ky roots (by omega) yk (.refl y) yw (by omega) budget
      have full k (km : k∈K) : Z⊆outN D V k := by
        have sub : outN D V k⊆outN D K k∪(Z∩outN D V k) := by
          intro a am
          have arc := (mem_outN.mp am).2
          rcases mem_union.mp (xmenu k (ky km) am) with early|az
          · rcases mem_union.mp early with ax|ay
            · by_cases ac : a∈C
              · have block := crossed_omissions free (by omega) yv ky kl roots km (cv ac) arc
                have m := miss a ac
                change (Y\outN D V a).card≤1 at m
                omega
              have eq := card_le_one.mp xs a (mem_sdiff.mpr ⟨ax,ac⟩) w wm
              exact (no_middle_return free yv wv ky roots (by omega) km (.refl k) (eq ▸ arc) (by omega) budget).elim
            · by_cases ak : a∈K
              · exact mem_union_left _ (mem_outN.mpr ⟨ak,arc⟩)
              have eq := card_le_one.mp thin a (mem_sdiff.mpr ⟨ay,ak⟩) y (mem_sdiff.mpr ⟨ym,away⟩)
              exact (no_middle_return free yv wv ky roots (by omega) km (Walk.step (yv ym) (eq ▸ arc) (.refl y)) yw (by omega) budget).elim
          · exact mem_union_right _ (mem_inter.mpr ⟨az,am⟩)
        have cost := (card_le_card sub).trans (card_union_le _ _)
        rw [reg _ (yv (ky km)),(roots k km).one k km] at cost
        exact eq_of_subset_of_card_le (inter_subset_left (s₂:=outN D V k) : Z∩outN D V k⊆Z) (by omega) ▸ inter_subset_right
      rw [filter_true_of_mem full]; omega
    · have menu y (ym : y∈Y) : outN D V y⊆(C∪Y)∪Z := by
        intro a am
        rcases mem_union.mp (xmenu y ym am) with early|az
        · rcases mem_union.mp early with ax|ay
          · have ac : a∈C := by by_contra off; exact anyReturn ⟨a,mem_sdiff.mpr ⟨ax,off⟩,y,ym,(mem_outN.mp am).2⟩
            exact mem_union_left _ (mem_union_left _ ac)
          · exact mem_union_left _ (mem_union_right _ ay)
        · exact mem_union_right _ az
      exact full_second_bank free (by omega) reg cv yv ky kl roots thin zs menu
        (fun c cm=>(miss c cm).trans (by decide : 1≤2)) (by omega)
        (by intro nonempty; have := card_pos.mpr nonempty; have := card_sdiff_of_subset ky; omega)
  have yz : Disjoint Y Z := disjoint_left.mpr (fun a ay az=>(mem_N3.mp az).2 (mem_N2.mp ay).1)
  have xz : Disjoint X Z := disjoint_left.mpr (fun a ax az=>(mem_N3.mp az).2 (ball_mono_radius (by decide : 1≤2) (X_B1 ax)))
  have margin := three_ball_margin free (by omega) reg cv yv zv (disjXY.mono_left first) (xz.mono_left first) yz ky kl roots
    (fun c cm=>(miss c cm).trans (by decide : 1≤2)) bank (card_pos.mp (by omega)) (by omega) (by omega)
  intro c cm
  have grow := ball_one_growth (free.mono_set cv) (fun a am=>((cy a am).one a am).ge) cm 3 (by omega)
  have used := margin c cm
  omega

#print axioms same_exterior_high
end LeanCH.BR.LowShellCycleSelection
