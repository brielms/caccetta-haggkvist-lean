import checkpoints.shen_extension.WidePrimaryReceipt

namespace LeanCH.BR.LowShellCycleSelection
open scoped Classical
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank

/-- Each sink that returns to C costs at least q-1 different missed
incidences in its own column. Every row of C has at most d such misses. -/
theorem return_columns {D V C Y S q d} (free : QFree D V q) (hq : 2≤q)
    (cv : C⊆V) (yv : Y⊆V) (inside : ∀x∈C,1≤(outN D C x).card)
    (miss : ∀x∈C,(Y\outN D V x).card≤d)
    (sy : S⊆Y) (ret : ∀s∈S,∃x∈C,D s x=true) :
    S.card*(q-1)≤C.card*d := by
  classical
  let gap := fun x s=>D x s≠true
  have cost s (sm : s∈S) : q-1≤(C.bipartiteBelow gap s).card := by
    obtain ⟨x,xc,e⟩ := ret s sm
    have src := yv (sy sm)
    have h := exception_parents free cv inside src xc (.step (cv xc) e (.refl x)) (by omega)
    have cover : C.bipartiteBelow gap s=C\inN D C s := by ext; simp [gap,inN]; tauto
    rw [cover,card_sdiff_of_subset (show inN D C s⊆C from fun _ h=>(mem_inN.mp h).1)]
    omega
  have budget x (xm : x∈C) : (S.bipartiteAbove gap x).card≤d := by
    apply (card_le_card ?_).trans (miss x xm)
    intro s sm
    exact mem_sdiff.mpr ⟨sy (mem_filter.mp sm).1,fun h=>(mem_filter.mp sm).2 (mem_outN.mp h).2⟩
  have lo := sum_le_sum cost
  have hi := sum_le_sum budget
  rw [sum_const_nat (fun _ _=>rfl)] at lo hi
  exact lo.trans ((sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=C) (t:=S) gap).ge.trans hi)

theorem sink_columns {D V C Y q d} (free : QFree D V q) (hq : 2≤q)
    (cv : C⊆V) (yv : Y⊆V) (inside : ∀x∈C,1≤(outN D C x).card)
    (miss : ∀x∈C,(Y\outN D V x).card≤d)
    (ret : ∀s∈sinks D Y,∃x∈C,D s x=true) :
    (sinks D Y).card*(q-1)≤C.card*d := return_columns free hq cv yv inside miss (filter_subset _ _) ret

/-- If every sink returns to a row missing at most d labels, at most d
vertices can flow to that sink in an acyclic Y. Long paths already give
d+1 distinct forbidden labels on their suffix. -/
theorem sink_cover {D V Y C q d} (free : QFree D V q) (yv : Y⊆V) (cv : C⊆V)
    (dag : QFree D Y Y.card) (time : d+2≤q)
    (miss : ∀x∈C,(Y\outN D V x).card≤d)
    (ret : ∀s∈sinks D Y,∃x∈C,D s x=true) :
    Y⊆(sinks D Y).biUnion (fun s=>Y.filter (fun a=>s∈ball D Y a d)) := by
  classical
  let old s := Y.filter (fun a=>s∈ball D Y a d)
  have budget s (sm : s∈sinks D Y) : (old s).card≤d := by
    obtain ⟨x,xc,e⟩ := ret s sm
    apply (card_le_card ?_).trans (miss x xc)
    intro a am
    obtain ⟨ay,hit⟩ := mem_filter.mp am
    obtain ⟨_,k,limit,path⟩ := mem_ball.mp hit
    exact mem_sdiff.mpr ⟨ay,fun h=>free x _ (by omega) (by omega)
      ((Walk.step (yv ay) (mem_outN.mp h).2 (path.mono yv)).snoc (cv xc) e)⟩
  have cover : Y⊆(sinks D Y).biUnion old := by
    intro a ay
    obtain ⟨p⟩ := exists_shortest_sink_path dag le_rfl ay
    let s := p.vertex p.len
    have sm : s∈sinks D Y := mem_filter.mpr ⟨p.mem _ le_rfl,p.sink⟩
    have small : p.len≤d := by
      by_contra! long
      let I := Icc (p.len-d) p.len
      have incl : (↑I : Set ℕ)⊆range (p.len+1) := fun i im=>mem_range.mpr (by have := (mem_Icc.mp im).2; omega)
      have use : I.image p.vertex⊆old s := by
        intro w wm
        obtain ⟨i,im,rfl⟩ := mem_image.mp wm
        obtain ⟨low,high⟩ := mem_Icc.mp im
        exact mem_filter.mpr ⟨p.mem _ high,mem_ball.mpr ⟨p.mem _ le_rfl,_,by omega,p.walk high le_rfl⟩⟩
      have cost := (card_le_card use).trans (budget s sm)
      rw [card_image_of_injOn ((p.injective dag le_rfl).mono incl)] at cost
      change (Icc (p.len-d) p.len).card≤d at cost
      rw [Nat.card_Icc] at cost
      omega
    have path : Walk D Y a s p.len := by simpa only [s,p.start,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
    exact mem_biUnion.mpr ⟨s,sm,mem_filter.mpr ⟨ay,mem_ball.mpr ⟨p.mem _ le_rfl,_,small,path⟩⟩⟩
  exact cover

theorem sink_ancestry {D V Y C q d} (free : QFree D V q) (yv : Y⊆V) (cv : C⊆V)
    (dag : QFree D Y Y.card) (time : d+2≤q)
    (miss : ∀x∈C,(Y\outN D V x).card≤d)
    (ret : ∀s∈sinks D Y,∃x∈C,D s x=true) :
    Y.card≤(sinks D Y).card*d := by
  classical
  let old s := Y.filter (fun a=>s∈ball D Y a d)
  have budget s (sm : s∈sinks D Y) : (old s).card≤d := by
    obtain ⟨x,xc,e⟩ := ret s sm
    apply (card_le_card ?_).trans (miss x xc)
    intro a am
    obtain ⟨ay,hit⟩ := mem_filter.mp am
    obtain ⟨_,k,limit,path⟩ := mem_ball.mp hit
    exact mem_sdiff.mpr ⟨ay,fun h=>free x _ (by omega) (by omega)
      ((Walk.step (yv ay) (mem_outN.mp h).2 (path.mono yv)).snoc (cv xc) e)⟩
  have cover := sink_cover free yv cv dag time miss ret
  have total := (card_le_card (show Y⊆(sinks D Y).biUnion old from cover)).trans (card_biUnion_le.trans (sum_le_sum budget))
  simpa only [sum_const_nat (fun _ _=>rfl)] using total

/-- A return through an exceptional row outside the cycle pays for all its
sinks at once, using that row's single set of omissions. -/
theorem split_sink_budget {D V Y X C q d} (free : QFree D V q) (yv : Y⊆V) (xv : X⊆V)
    (cx : C⊆X) (dag : QFree D Y Y.card) (time : d+2≤q)
    (inside : ∀x∈C,1≤(outN D C x).card)
    (miss : ∀x∈X,(Y\outN D V x).card≤d) (ret : ∀s∈sinks D Y,∃x∈X,D s x=true) :
    ∃S⊆sinks D Y,S.card*(q-1)≤C.card*d ∧ Y.card≤S.card*d+(X\C).card*d := by
  classical
  let S := (sinks D Y).filter (fun s=>∃x∈C,D s x=true)
  let old s := Y.filter (fun a=>s∈ball D Y a d)
  have lost s (sm : s∈sinks D Y) x (xm : x∈X) (arc : D s x=true) : old s⊆Y\outN D V x := by
    intro a am
    obtain ⟨ay,hit⟩ := mem_filter.mp am
    obtain ⟨_,k,lim,path⟩ := mem_ball.mp hit
    exact mem_sdiff.mpr ⟨ay,fun h=>free x _ (by omega) (by omega)
      ((Walk.step (yv ay) (mem_outN.mp h).2 (path.mono yv)).snoc (xv xm) arc)⟩
  have lo := return_columns free (by omega) (cx.trans xv) yv inside (fun x xm=>miss x (cx xm))
    (show S⊆Y from (filter_subset _ _).trans (filter_subset _ _))
    (fun s (sm : s∈S)=>(mem_filter.mp sm).2)
  refine ⟨S,filter_subset _ _,lo,?_⟩
  have cover : Y⊆S.biUnion old∪(X\C).biUnion (fun x=>Y\outN D V x) := by
    intro a am
    obtain ⟨s,sm,near⟩ := mem_biUnion.mp (sink_cover free yv xv dag time miss ret am)
    by_cases sc : s∈S
    · exact mem_union_left _ (mem_biUnion.mpr ⟨s,sc,near⟩)
    obtain ⟨x,xm,arc⟩ := ret s sm
    have off : x∈X\C := mem_sdiff.mpr ⟨xm,fun cm=>sc (mem_filter.mpr ⟨sm,x,cm,arc⟩)⟩
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,off,lost s sm x xm arc near⟩)
  have small s (sm : s∈S) : (old s).card≤d := by
    obtain ⟨x,xm,arc⟩ := (mem_filter.mp sm).2
    exact (card_le_card (lost s (mem_filter.mp sm).1 x (cx xm) arc)).trans (miss x (cx xm))
  have h := (card_le_card cover).trans (card_union_le _ _)
  apply h.trans
  apply Nat.add_le_add
  · exact card_biUnion_le.trans ((sum_le_sum small).trans_eq (sum_const_nat (fun _ _=>rfl)))
  · exact card_biUnion_le.trans ((sum_le_sum (fun x (xm : x∈X\C)=>miss x (mem_sdiff.mp xm).1)).trans_eq
      (sum_const_nat (fun _ _=>rfl)))

theorem returning_sink_budget {D V Y C q d} (free : QFree D V q)
    (yv : Y⊆V) (cv : C⊆V) (dag : QFree D Y Y.card) (time : d+2≤q)
    (inside : ∀x∈C,1≤(outN D C x).card)
    (miss : ∀x∈C,(Y\outN D V x).card≤d)
    (ret : ∀s∈sinks D Y,∃x∈C,D s x=true) :
    Y.card*(q-1)≤(C.card*d)*d := by
  have a := sink_ancestry free yv cv dag time miss ret
  have b := sink_columns free (by omega) cv yv inside miss ret
  exact (Nat.mul_le_mul_right (q-1) a).trans ((Nat.mul_right_comm _ _ _).symm ▸ Nat.mul_le_mul_right d b)

/-- On the actual short root from the wide-exterior obstruction, the second
shell must contain a directed cycle. All cardinalities and the cutoff are free. -/
theorem wide_short_second_cycle {D V q r u C} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀x∈C,Rooted D V x C) (first : C⊆outN D V u)
    (upper : (N2 D V u).card≤r) (wide : r<(exterior D V C).card)
    (short : (ball D V u 3).card<3*r) : ¬QFree D (N2 D V u) (N2 D V u).card := by
  classical
  intro dag
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xsize : X.card=r := reg u uv
  have gaps := card_sdiff_of_subset first
  have cc := card_le_card first
  change (X\C).card=X.card-C.card at gaps
  change C.card≤X.card at cc
  have slots : (X\C).card≤1 := by omega
  have bal := gate_balance free (by omega) uv first
  change _+_+(exterior D V C).card=(X\C).card+Y.card at bal
  have ysize : Y.card=r := by change Y.card≤r at upper; omega
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  rw [reg _ uv] at b1
  have zsize : Z.card+2≤r := by change (N2 D V u).card=r at ysize; dsimp [Z]; omega
  have cv : C⊆V := first.trans outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have missing c (cm : c∈C) : (Y\outN D V c).card≤2 := by
    have keep : outN D X c⊆outN D C c∪(X\C) := by
      intro a am
      by_cases ac : a∈C
      · exact mem_union_left _ (mem_outN.mpr ⟨ac,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset am,ac⟩)
    have small := (card_le_card keep).trans (card_union_le _ _)
    rw [(rooted c cm).one c cm] at small
    have reserve := SinkDepthCover.omitted_heads (reg c (cv cm)).ge
      (fun a (am : a∈outN D V c)=>headX (free.mono_bound (by omega : 4≤q)) uv (first cm)
        (outN_subset am) (mem_outN.mp am).2) (by omega : (outN D X c).card≤2)
    change (Y\outN D V c).card+r≤Y.card+2 at reserve
    omega
  have ret s (sm : s∈sinks D Y) : ∃x∈C,D s x=true := by
    by_contra! none
    have menu : outN D V s⊆(X\C)∪Z := by
      intro a am
      have edge := (mem_outN.mp am).2
      rcases headY (free.mono_bound (by omega : 4≤q)) uv (mem_filter.mp sm).1 (outN_subset am) edge with early|late
      · have ax := (mem_union.mp early).resolve_right (fun ay=>(mem_filter.mp sm).2 a ay edge)
        exact mem_union_left _ (mem_sdiff.mpr ⟨ax,fun ac=>by have := none a ac; simp_all⟩)
      · exact mem_union_right _ late
    have bound := (card_le_card menu).trans (card_union_le _ _)
    rw [reg s (yv (mem_filter.mp sm).1)] at bound
    omega
  have limit := returning_sink_budget free yv cv dag (by omega : 2+2≤q)
    (fun x xm=>((rooted x xm).one x xm).ge) missing ret
  have lower := Nat.mul_le_mul_left Y.card (show 5≤q-1 by omega)
  omega

attribute [aesop safe forward (immediate := [free,hq,reg,uv,fits,len,rooted,first,upper,wide,short])
  (rule_sets := [CHGraphFamilies])] wide_short_second_cycle
#print axioms wide_short_second_cycle
#print axioms returning_sink_budget
end LeanCH.BR.LowShellCycleSelection
