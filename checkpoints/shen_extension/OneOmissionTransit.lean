import checkpoints.shen_extension.OneOmissionSinkBank
namespace LeanCH.BR.OneOmissionSinkBank
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- Starting at the same receiving vertex x, an actual predecessor from Y
saves a step. A path of maximum length instead forces both a unique sink
and enough direct entries into the nonreturning part of Y. -/
theorem cheap_sink {D V X Y q r x} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (hr : 4≤r) (time : r+2≤q) (dx : X.card=r) (dy : Y.card=r+1) (xm : x∈X)
    (quota : r≤(outN D (X∪Y) x).card) (apart : Disjoint X Y)
    (budget : ∀s∈X,Sink D X s → (Y\outN D V s).card≤1) :
    let A := Y\returning D X Y
    ∃t∈A,Sink D A t ∧ ∃k,k≤r ∧ ((inN D Y x).Nonempty → k+1≤r) ∧ Walk D V x t k := by
  classical
  let O := returning D X Y
  let A := Y\O
  have oy : O⊆Y := filter_subset _ _
  have ay : A⊆Y := sdiff_subset
  have av : A⊆V := ay.trans yv
  have sizeA := (card_le_card ay).trans (show Y.card≤q by omega)
  obtain ⟨tally,a,am,shared⟩ := shared_entry free xv yv (by omega) (by omega) budget
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) (by omega) xm
  let s := p.vertex p.len
  have sx : s∈X := p.mem _ le_rfl
  have ss : s∈sinks D X := mem_filter.mpr ⟨sx,p.sink⟩
  have path : Walk D V x s p.len := by
    simpa only [p.start,Nat.sub_zero] using (p.walk (Nat.zero_le _) le_rfl).mono xv
  have omitA (u) : A\outN D A u⊆Y\outN D V u := by
    intro z zm
    obtain ⟨za,off⟩ := mem_sdiff.mp zm
    exact mem_sdiff.mpr ⟨ay za,fun arc=>off (mem_outN.mpr ⟨za,(mem_outN.mp arc).2⟩)⟩
  by_cases short : p.len+2≤r
  · obtain ⟨t,tm,last,l,ll,way⟩ := SinkTransit.from_heads free av sizeA
      (show (outN D A s).Nonempty from ⟨a,mem_outN.mpr ⟨am,shared s ss⟩⟩)
    have lim := (card_le_card (omitA s)).trans (budget s sx p.sink)
    by_cases parent : (inN D Y x).Nonempty
    · obtain ⟨y,ym⟩ := parent
      have yy := (mem_inN.mp ym).1
      have yx := (mem_inN.mp ym).2
      have xy : x∈outN D X y := mem_outN.mpr ⟨xm,yx⟩
      have yo : y∈O := mem_filter.mpr ⟨yy,x,xy⟩
      have sy : y∈Y\outN D V s := mem_sdiff.mpr ⟨yy,fun hit=>free x _ (by omega) (by omega)
        ((path.snoc (yv yy) (mem_outN.mp hit).2).snoc (xv xm) yx)⟩
      have st : D s t=true := by
        by_contra miss
        have off : t∈Y\outN D V s := mem_sdiff.mpr ⟨ay tm,fun head=>miss (mem_outN.mp head).2⟩
        exact (mem_sdiff.mp tm).2 ((card_le_one.mp (budget s sx p.sink) y sy t off) ▸ yo)
      exact ⟨t,tm,last,p.len+1,by omega,fun _=>by omega,path.snoc (av tm) st⟩
    exact ⟨t,tm,last,p.len+l,by omega,fun v=>(parent v).elim,path.append way⟩
  have qx : X.card≤q := by omega
  have depth := depth_count (free.mono_set xv) qx p
  have internal := SinkTransit.internal_depth (free.mono_set xv) qx p
  rw [card_outN_union apart] at quota
  have rest := card_sdiff_add_card_eq_card (outN_subset : outN D Y x⊆Y)
  have roomA := card_le_card (omitA x)
  have missingEq : (Y\outN D V x)=(Y\outN D Y x) := by
    ext z
    simp only [mem_sdiff,mem_outN]
    exact ⟨fun ⟨zy,h⟩=>⟨zy,fun a=>h ⟨yv zy,a.2⟩⟩,
      fun ⟨zy,h⟩=>⟨zy,fun a=>h ⟨zy,a.2⟩⟩⟩
  rw [missingEq] at roomA
  have countA := card_sdiff_add_card_eq_card oy
  change A.card+O.card=Y.card at countA
  change O.card≤_ at tally
  have rem := card_sdiff_add_card_eq_card (outN_subset : outN D A x⊆A)
  obtain ⟨t,tm,last,k,le,walk⟩ := SinkTransit.from_heads free av sizeA
    (x:=x) (card_pos.mp (by omega))
  exact ⟨t,tm,last,k,by omega,fun _=>by omega,walk⟩

attribute [aesop safe forward (immediate := [free,xv,yv,hr,time,dx,dy,xm,quota,apart,budget])
  (rule_sets := [CHGraphFamilies])] cheap_sink
#print axioms cheap_sink
end LeanCH.BR.OneOmissionSinkBank
