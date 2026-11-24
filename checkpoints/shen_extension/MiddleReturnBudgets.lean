import checkpoints.shen_extension.UniqueMiddleClaim

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank
open scoped Classical

/-- Distinguish the omission allowance on the cycle from that on the exceptional rows. -/
theorem separate_sink_budgets {D V Y X C q d e} (free : QFree D V q) (yv : Y⊆V) (xv : X⊆V)
    (cx : C⊆X) (dag : QFree D Y Y.card) (time : e+2≤q)
    (inside : ∀x∈C,1≤(outN D C x).card)
    (cycleMiss : ∀x∈C,(Y\outN D V x).card≤d)
    (miss : ∀x∈X,(Y\outN D V x).card≤e) (ret : ∀s∈sinks D Y,∃x∈X,D s x=true) :
    ∃S⊆sinks D Y,S.card*(q-1)≤C.card*d ∧ Y.card≤S.card*d+(X\C).card*e := by
  classical
  let S := (sinks D Y).filter (fun s=>∃x∈C,D s x=true)
  let old s := Y.filter (fun a=>s∈ball D Y a e)
  have lost s (sm : s∈sinks D Y) x (xm : x∈X) (arc : D s x=true) : old s⊆Y\outN D V x := by
    intro a am
    obtain ⟨ay,hit⟩ := mem_filter.mp am
    obtain ⟨_,k,lim,path⟩ := mem_ball.mp hit
    exact mem_sdiff.mpr ⟨ay,fun h=>free x _ (by omega) (by omega)
      ((Walk.step (yv ay) (mem_outN.mp h).2 (path.mono yv)).snoc (xv xm) arc)⟩
  have lo := return_columns free (by omega) (cx.trans xv) yv inside cycleMiss
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
    exact (card_le_card (lost s (mem_filter.mp sm).1 x (cx xm) arc)).trans (cycleMiss x xm)
  have h := (card_le_card cover).trans (card_union_le _ _)
  apply h.trans
  apply Nat.add_le_add
  · exact card_biUnion_le.trans ((sum_le_sum small).trans_eq (sum_const_nat (fun _ _=>rfl)))
  · exact card_biUnion_le.trans ((sum_le_sum (fun x (xm : x∈X\C)=>miss x (mem_sdiff.mp xm).1)).trans_eq
      (sum_const_nat (fun _ _=>rfl)))


/-- A marked path into x prevents x from targeting the last q-l labels
of the source cycle backwards from the departure. -/
theorem missed_cycle_segment {D V S q a x l} (free : QFree D V q) (sv : S⊆V)
    (cy : ∀v∈S,Rooted D V v S) (long : 1<S.card) (sa : a∈S) (xv : x∈V)
    (path : Walk D V a x l) (time : l+1≤q) :
    q-l≤(S\outN D V x).card := by
  have cap := exception_parents free.reverse sv (reverse_positive long cy) xv sa (path.reverse_of_mem (sv sa)) time
  have eq : inN (fun a b=>D b a) S x=S∩outN D V x := by
    ext y; simp only [mem_inN,mem_inter,mem_outN]; exact ⟨fun h=>⟨h.1,sv h.1,h.2⟩,fun h=>⟨h.1,h.2.2⟩⟩
  rw [eq] at cap
  have := card_sdiff_add_card_inter S (outN D V x)
  omega

/-- The same second shell is the physical exterior of C. A returning
row of Y therefore has a named predecessor on C. -/
theorem middle_return_budgets {D V u C q r} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (first : C⊆outN D V u) (len : q<C.card) (cy : ∀c∈C,Rooted D V c C)
    (size : C.card+1=r) (ys : (N2 D V u).card=r) (same : exterior D V C=N2 D V u) :
    (∀c∈C,(N2 D V u\outN D V c).card≤1) ∧
    ∀w∈outN D V u\C, (∃y∈N2 D V u,D y w=true) →
      (N2 D V u\outN D V w).card+(q-2)≤C.card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  have xv : X⊆V := outN_subset
  have cv := first.trans xv
  have menu x (xm : x∈X) : outN D V x⊆X∪Y := fun a am=>headX (free.mono_bound hq) uv xm (outN_subset am) (mem_outN.mp am).2
  have gap := card_sdiff_of_subset first
  rw [reg u uv] at gap
  have slots : (X\C).card≤1 := by dsimp [X]; omega
  constructor
  · intro c cm
    have inside : outN D X c⊆outN D C c := by
      intro a am
      have ax := outN_subset am
      have e := (mem_outN.mp am).2
      by_cases ac : a∈C
      · exact mem_outN.mpr ⟨ac,e⟩
      have outside : a∈exterior D V C := mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨c,cm,mem_outN.mpr ⟨xv ax,e⟩⟩,ac⟩
      exact (disjoint_left.mp disjXY ax (same ▸ outside)).elim
    have count := card_le_card inside
    rw [(cy c cm).one c cm] at count
    have h := SinkDepthCover.omitted_heads (reg c (cv cm)).ge (menu c (first cm)) count
    change (Y\outN D V c).card+r≤Y.card+1 at h
    change Y.card=r at ys
    change (Y\outN D V c).card≤1
    omega
  · rintro w wm ⟨y,ym,yw⟩
    obtain ⟨a,ac,ay⟩ := mem_biUnion.mp (mem_sdiff.mp (same.symm ▸ ym)).1
    have wx := (mem_sdiff.mp wm).1
    have miss := missed_cycle_segment free cv cy (by omega) ac (xv wx)
      (Walk.step (outN_subset ay) (mem_outN.mp ay).2 (.step (xv wx) yw (.refl w))) (by omega)
    have incl : outN D X w⊆C∩outN D V w := by
      intro a am
      have ax := outN_subset am
      have ac : a∈C := by
        by_contra off
        have eq := card_le_one.mp slots a (mem_sdiff.mpr ⟨ax,off⟩) w wm
        exact loopfree free (by omega) (xv wx) (eq ▸ (mem_outN.mp am).2)
      exact mem_inter.mpr ⟨ac,outN_mono xv w am⟩
    have bill := SinkDepthCover.omitted_heads (reg w (xv wx)).ge (menu w wx) (card_le_card incl)
    have := card_sdiff_add_card_inter C (outN D V w)
    change (Y\outN D V w).card+r≤Y.card+_ at bill
    change Y.card=r at ys
    change (Y\outN D V w).card+(q-2)≤C.card
    omega

#print axioms separate_sink_budgets
#print axioms missed_cycle_segment
#print axioms middle_return_budgets
end LeanCH.BR.LowShellCycleSelection
