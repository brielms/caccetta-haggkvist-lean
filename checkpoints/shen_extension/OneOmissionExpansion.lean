import checkpoints.shen_extension.OneOmissionTransit
namespace LeanCH.BR.OneOmissionSinkBank
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- If the second of four consecutive sets has one extra label, discard
the rows that point back into the first. Each sink of the rest reaches the
whole third set. The same witnesses give short returns to the first two
sets, forcing the degree of a sink of the third into the fourth. -/
theorem expansion {D V X Y Z W q r} (free : QFree D V q) (xv : X⊆V)
    (yv : Y⊆V) (zv : Z⊆V) (apart : Disjoint X Y) (hr : 4≤r) (time : r+2≤q)
    (dx : X.card=r) (dy : Y.card=r+1) (dz : Z.card≤r)
    (degree : ∀v∈V,r≤(outN D V v).card)
    (first : ∀x∈X,outN D V x⊆X∪Y) (second : ∀y∈Y,outN D V y⊆(X∪Y)∪Z)
    (third : ∀z∈Z,outN D V z⊆((X∪Y)∪Z)∪W) : r≤W.card := by
  classical
  let O := returning D X Y
  let A := Y\O
  have ay : A⊆Y := sdiff_subset
  have av := ay.trans yv
  have smallA := (card_le_card ay).trans (show Y.card≤q by omega)
  have budget s (sx : s∈X) (sink : Sink D X s) : (Y\outN D V s).card≤1 := by
    have sub : outN D V s⊆Y := by
      intro a am
      exact (mem_union.mp (first s sx am)).resolve_left (fun ax=>sink a ax (mem_outN.mp am).2)
    rw [card_sdiff_of_subset sub]
    have := degree s (xv sx)
    omega
  have allZ t (ta : t∈A) (sink : Sink D A t) : Z=outN D V t := by
    symm
    apply eq_of_subset_of_card_le _ (dz.trans (degree t (av ta)))
    intro v vm
    apply (mem_union.mp (second t (ay ta) vm)).resolve_left
    intro early
    have arc := (mem_outN.mp vm).2
    rcases mem_union.mp early with ex|ey
    · exact (mem_sdiff.mp ta).2 (mem_filter.mpr ⟨ay ta,v,mem_outN.mpr ⟨ex,arc⟩⟩)
    · by_cases vo : v∈O
      · exact no_parent free xv yv (by omega) budget (ay ta) vo arc
      · exact sink v (mem_sdiff.mpr ⟨ey,vo⟩) arc
  have quota x (xm : x∈X) : r≤(outN D (X∪Y) x).card := by
    apply (degree x (xv xm)).trans (card_le_card ?_)
    exact fun a am=>mem_outN.mpr ⟨first x xm am,(mem_outN.mp am).2⟩
  have transit x (xm : x∈X) := cheap_sink free xv yv hr time dx dy xm (quota x xm) apart budget
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<X.card by omega)
  obtain ⟨t,ta,last,_⟩ := transit x xm
  have nz := degree t (av ta)
  rw [←allZ t ta last] at nz
  obtain ⟨z,zm,sinkZ⟩ := exists_sink (free.mono_set zv) (card_pos.mp (by omega)) (by omega : Z.card≤q)
  have sub : outN D V z⊆W := by
    intro a am
    apply (mem_union.mp (third z zm am)).resolve_left
    intro early
    have arc := (mem_outN.mp am).2
    have vm := outN_subset am
    rcases mem_union.mp early with xy|az
    · rcases mem_union.mp xy with ax|ay'
      · obtain ⟨s,sm,ss,k,le,_,walk⟩ := transit a ax
        have head := (mem_outN.mp ((allZ s sm ss) ▸ zm)).2
        exact free a _ (by omega) (by omega) ((walk.snoc (zv zm) head).snoc vm arc)
      · by_cases ao : a∈O
        · obtain ⟨_,u,um⟩ := mem_filter.mp ao
          obtain ⟨s,sm,ss,k,_,save,walk⟩ := transit u (outN_subset um)
          have fast := save ⟨a,mem_inN.mpr ⟨ay',(mem_outN.mp um).2⟩⟩
          have head := (mem_outN.mp ((allZ s sm ss) ▸ zm)).2
          exact free u _ (by omega) (by omega) (((walk.snoc (zv zm) head).snoc vm arc).snoc
            (xv (outN_subset um)) (mem_outN.mp um).2)
        · obtain ⟨s,sm,ss,k,le,walk⟩ := reach_sink_of_card (free.mono_set av) smallA
            (show a∈A from mem_sdiff.mpr ⟨ay',ao⟩)
          have cap := card_le_card ay
          have head := (mem_outN.mp ((allZ s sm ss) ▸ zm)).2
          exact free a _ (by omega) (by omega) (((walk.mono av).snoc (zv zm) head).snoc vm arc)
    · exact sinkZ a az arc
  exact (degree z (zv zm)).trans (card_le_card sub)

theorem fourth_layer {D V q r u} (free : QFree D V q) (root : u∈V)
    (degree : ∀v∈V,r≤(outN D V v).card)
    (hr : 4≤r) (time : r+2≤q) (row : (outN D V u).card=r)
    (width : (N2 D V u).card=r+1) (thirdSize : (N3 D V u).card≤r) :
    r≤(ball D V u 4\ball D V u 3).card := by
  have ff := free.mono_bound (show 4≤q by omega)
  apply expansion free outN_subset (fun _ h=>N2_subV h) (fun _ h=>N3_subV h)
    disjXY hr time row width thirdSize degree
  · exact fun _ xm _ am=>headX ff root xm (outN_subset am) (mem_outN.mp am).2
  · exact fun _ ym _ am=>mem_union.mpr (headY ff root ym (outN_subset am) (mem_outN.mp am).2)
  · intro z zm a am
    have arc := (mem_outN.mp am).2
    have a4 := ball_step (mem_N3.mp zm).1 (outN_subset am) arc
    by_cases a3 : a∈ball D V u 3
    · apply mem_union_left
      by_cases a2 : a∈ball D V u 2
      · apply mem_union_left
        by_cases a1 : a∈ball D V u 1
        · exact mem_union_left _ (((mem_ball_one root).mp a1).resolve_left
            (fun eq=>no_back_arc free root (mem_N3.mp zm).1 (by omega) (eq ▸ arc)))
        · exact mem_union_right _ (mem_sdiff.mpr ⟨a2,a1⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨a3,a2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨a4,a3⟩)

attribute [aesop safe forward (immediate := [free,xv,yv,zv,apart,hr,time,dx,dy,dz,degree,first,second,third])
  (rule_sets := [CHGraphFamilies])] expansion
attribute [aesop safe forward (immediate := [free,root,degree,hr,time,row,width,thirdSize])
  (rule_sets := [CHGraphFamilies])] fourth_layer
#print axioms expansion
#print axioms fourth_layer
end LeanCH.BR.OneOmissionSinkBank
