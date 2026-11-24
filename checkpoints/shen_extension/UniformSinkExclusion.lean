import checkpoints.shen_extension.SinkBankReturn
import checkpoints.shen_extension.ReturnBankEscape
namespace LeanCH.BR.SinkBankReturn
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- A rank-d obstruction on the punctured third ball bounds the missed
second-layer labels at the unique return destination by d−2. The
return-bank theorem then excludes a sink at any eligible root. -/
theorem no_sink {D V q r u s d} (free : QFree D V q) (hq : 5≤q) (reg : OutEq r D V)
    (root : u∈V) (sx : s∈outN D V u) (width : (N2 D V u).card=r) (third : (N3 D V u).card+1=r)
    (two : (ball D V s 2).card=2*r+1) (three : (ball D V s 3).card≤3*r)
    (dl : 2≤d) (du : d≤5) (enough : d+1≤r) (rankFits : 3*r≤q*d+1)
    (window : r≤q+3) (large : r≤2*(min q (r-(d-2)))) (retained : r-1+(d-2)≤2*q) :
    ¬Sink D (outN D V u) s := by
  intro sink
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4\ball D V u 3
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have cut := free.mono_bound (show 4≤q by omega)
  have deg x (xm : x∈V) := (reg x xm).ge
  have dx : X.card=r := reg u root
  have row := card_B1 cut root
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  change W.card+_=_ at diff
  have du' := reg u root
  have size : (ball D V u 3).card=3*r := by omega
  have grow := PrefixDegreeGrowth.small_rank_step (j:=3) (d:=d) free root (by omega) deg hq dl du
    (by omega) (by omega)
  change (ball D V u 3).card+r<(ball D V u 4).card+d at grow
  obtain ⟨b,bx,_,yp,returns,bill⟩ := single_target free (by omega) reg root sx sink width third two
  change W.card+(outN D X b).card+2*r+1≤_ at bill
  have sumX : (outN D X b).card+(outN D Y b).card=r := by
    rw [←card_outN_union disjXY,←outN_X_eq cut root bx,reg b (xv bx)]
  have internal : 1≤(outN D X b).card := by
    obtain ⟨y,ym⟩ := yp
    have yb := (mem_inN.mp ym).2
    have no : y∈Y\outN D Y b := mem_sdiff.mpr ⟨(mem_inN.mp ym).1,fun head=>
      free y 2 (by decide) (by omega) (.step (xv bx) yb (.step (yv (mem_inN.mp ym).1) (mem_outN.mp head).2 (.refl y)))⟩
    have one := card_pos.mpr (show (Y\outN D Y b).Nonempty from ⟨y,no⟩)
    have total := card_sdiff_add_card_eq_card (outN_subset : outN D Y b⊆Y)
    change Y.card=r at width
    omega
  apply ReturnBankEscape.window (m:=d-2) free xv yv zv (disjoint_left.mpr (fun _ ym zm=>
    (mem_N3.mp zm).2 (mem_N2.mp ym).1)) hq dx width third deg _ _ _ bx yp
    (by change Y.card=r at width; omega) (by omega) window large (by change Z.card+1=r at third; exact (show Z.card=r-1 by omega) ▸ retained)
    (by omega) (show W.card+2≤r by omega)
  · exact fun _ xm _ am=>headX cut root xm (outN_subset am) (mem_outN.mp am).2
  · intro y ym a am
    rcases headY cut root ym (outN_subset am) (mem_outN.mp am).2 with early|za
    · rcases mem_union.mp early with ax|ay
      · exact mem_union_right _ (mem_singleton.mpr (returns y ym a ax (mem_outN.mp am).2))
      · exact mem_union_left _ (mem_union_left _ ay)
    · exact mem_union_left _ (mem_union_right _ za)
  · intro z zm a am
    have arc := (mem_outN.mp am).2
    rcases split4 (E:=D) root a with back|ax|ay|az|far
    · exact (no_back_arc free root (mem_N3.mp zm).1 (by omega) (back ▸ arc)).elim
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ ax))
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ay))
    · exact mem_union_left _ (mem_union_right _ az)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_step (mem_N3.mp zm).1 (outN_subset am) arc,far⟩)

attribute [aesop safe forward (immediate := [free,hq,reg,root,sx,width,third,two,three,dl,du,enough,rankFits,window,large,retained])
  (rule_sets := [CHGraphFamilies])] no_sink
#print axioms no_sink
end LeanCH.BR.SinkBankReturn
