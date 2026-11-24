import checkpoints.shen_extension.SinkReturnAncestors

namespace LeanCH.BR.SinkReturnAncestors
open Finset BRq2 BRq3 BR45 BRsGen

/-- On three labelled layers, a missed return from a sink must be paid
from the last layer alone. One missing entry per first sink then bounds
the entire middle layer, without a regularity hypothesis. -/
theorem window {D V X Y Z q r} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : X.card+2≤q) (size : Y.card≤q) (width : Y.card≤r+1) (few : Z.card<r)
    (quotaX : ∀x∈X,r≤(outN D V x).card) (quotaY : ∀y∈Y,r≤(outN D V y).card)
    (first : ∀x∈X,outN D V x⊆X∪Y) (second : ∀y∈Y,outN D V y⊆(X∪Y)∪Z) :
    Y.card≤X.card := by
  apply one_omission free xv yv time size
  · intro s sm last
    have sub : outN D V s⊆Y := by
      intro a am
      exact (mem_union.mp (first s sm am)).resolve_left (fun ax=>last a ax (mem_outN.mp am).2)
    rw [card_sdiff_of_subset sub]
    have := quotaX s sm
    omega
  · intro y ym last
    by_contra empty
    have sub : outN D V y⊆Z := by
      intro a am
      apply (mem_union.mp (second y ym am)).resolve_left
      intro early
      rcases mem_union.mp early with ax|ay
      · exact empty ⟨a,mem_outN.mpr ⟨ax,(mem_outN.mp am).2⟩⟩
      · exact last a ay (mem_outN.mp am).2
    exact (Nat.not_lt_of_ge ((quotaY y ym).trans (card_le_card sub))) few

/-- At an actual root, if the second layer is one larger than its row
and each of its rows must spend a return, the next layer has enough space
for the entire quota. -/
theorem first_layers {D V q r u} (free : QFree D V q) (uv : u∈V) (hq : 4≤q)
    (degree : ∀v∈V,r≤(outN D V v).card)
    (time : (outN D V u).card+2≤q) (wide : (outN D V u).card<(N2 D V u).card)
    (width : (N2 D V u).card≤r+1) : r≤(N3 D V u).card := by
  by_contra! few
  have size := degree u uv
  exact (Nat.not_lt_of_ge (window free outN_subset (fun _ h=>N2_subV h) time
    (by omega) width few (fun _ xm=>degree _ (outN_subset xm)) (fun _ ym=>degree _ (N2_subV ym))
    (fun _ xm _ am=>headX (free.mono_bound hq) uv xm (outN_subset am) (mem_outN.mp am).2)
    (fun _ ym _ am=>mem_union.mpr (headY (free.mono_bound hq) uv ym (outN_subset am) (mem_outN.mp am).2)))) wide

/-- When the first two layers have equal size, each first-layer vertex
can reach each second-layer vertex through its own sink. Every third-
layer vertex has an actual second-layer parent. This prevents returns
to the first layer from both and allows the window to slide one layer. -/
theorem shifted_layers {D V q r u} (free : QFree D V q) (uv : u∈V) (hq : 4≤q)
    (degree : ∀v∈V,r≤(outN D V v).card) (rootRow : (outN D V u).card=r)
    (time : r+2≤q) (width : (N2 D V u).card=r)
    (next : (N3 D V u).card=r+1) : r≤(ball D V u 4 \ ball D V u 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4 \ ball D V u 3
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have dx : X.card=r := rootRow
  have dy : Y.card=r := width
  have dz : Z.card=r+1 := next
  have findSink (x) (xm : x∈X) := reach_sink_of_card (free.mono_set xv) (show X.card≤q by omega) xm
  have allS (s) (sm : s∈X) (last : Sink D X s) : Y⊆outN D V s := by
    apply (eq_of_subset_of_card_le (s:=outN D V s) (t:=Y) ?_ ?_).symm.subset
    · intro a am
      exact (mem_union.mp (headX (free.mono_bound hq) uv sm (outN_subset am) (mem_outN.mp am).2)).resolve_left
        (fun ax=>last a ax (mem_outN.mp am).2)
    · exact dy.le.trans (degree s (xv sm))
  have route x (xm : x∈X) y (ym : y∈Y) : ∃k,k≤r ∧ Walk D V x y k := by
    obtain ⟨s,sm,last,k,kl,path⟩ := findSink x xm
    exact ⟨k+1,by omega,(path.mono xv).snoc (yv ym) (mem_outN.mp (allS s sm last ym)).2⟩
  have first y (ym : y∈Y) : outN D V y⊆Y∪Z := by
    intro a am
    rcases headY (free.mono_bound hq) uv ym (outN_subset am) (mem_outN.mp am).2 with early|za
    · rcases mem_union.mp early with ax|ay
      · obtain ⟨k,le,path⟩ := route a ax y ym
        exact (free a _ (by omega) (by omega) (path.snoc (outN_subset am) (mem_outN.mp am).2)).elim
      · exact mem_union_left _ ay
    · exact mem_union_right _ za
  have second z (zm : z∈Z) : outN D V z⊆(Y∪Z)∪W := by
    obtain ⟨y,ym,edge⟩ := ball_succ_pred uv (mem_N3.mp zm).1 (mem_N3.mp zm).2
    have yy : y∈Y := mem_sdiff.mpr ⟨ym,fun early=>(mem_N3.mp zm).2 (ball_step early (zv zm) edge)⟩
    intro a am
    have av := outN_subset am
    have arc := (mem_outN.mp am).2
    by_cases a3 : a∈ball D V u 3
    · apply mem_union_left
      by_cases a2 : a∈ball D V u 2
      · apply mem_union_left
        refine mem_sdiff.mpr ⟨a2,?_⟩
        intro a1
        rcases (mem_ball_one uv).mp a1 with eq|ax
        · subst a
          exact no_back_arc free uv (mem_N3.mp zm).1 (by omega) arc
        · obtain ⟨k,le,path⟩ := route a ax y yy
          exact free a _ (by omega) (by omega) ((path.snoc (zv zm) edge).snoc av arc)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨a3,a2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_step (mem_N3.mp zm).1 av arc,a3⟩)
  by_contra! few
  have cap := window free yv zv (by omega) (by omega) (by omega) few
    (fun _ ym=>degree _ (yv ym)) (fun _ zm=>degree _ (zv zm)) first second
  omega

attribute [aesop safe forward (immediate := [free,xv,yv,time,size,width,few,quotaX,quotaY,first,second])
  (rule_sets := [CHGraphFamilies])] window
attribute [aesop safe forward (immediate := [free,uv,hq,degree,time,wide,width])
  (rule_sets := [CHGraphFamilies])] first_layers
attribute [aesop safe forward (immediate := [free,uv,hq,degree,rootRow,time,width,next])
  (rule_sets := [CHGraphFamilies])] shifted_layers
#print axioms window
#print axioms first_layers
#print axioms shifted_layers
end LeanCH.BR.SinkReturnAncestors
