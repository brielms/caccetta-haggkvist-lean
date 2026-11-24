import checkpoints.shen_extension.PureMiddleEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank
open scoped Classical

theorem fed_extra_omissions {D V q r C u} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀x∈C,Rooted D V x C) (first : C⊆outN D V u)
    (upper : (N2 D V u).card≤r) (fed : outN D V u\C⊆exterior D V C) :
    ∀x∈outN D V u,(N2 D V u\outN D V x).card≤2 := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  have sz := reg u uv
  have gaps := card_sdiff_of_subset first
  have cc := card_le_card first
  have slots : (X\C).card≤1 := by dsimp [X]; omega
  intro x xm
  have internal : (outN D X x).card≤2 := by
    by_cases xc : x∈C
    · have keep : outN D X x⊆outN D C x∪(X\C) := by
        intro a am
        by_cases ac : a∈C
        · exact mem_union_left _ (mem_outN.mpr ⟨ac,(mem_outN.mp am).2⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset am,ac⟩)
      have bound := (card_le_card keep).trans (card_union_le _ _)
      rw [(rooted x xc).one x xc] at bound
      omega
    have off : x∈X\C := mem_sdiff.mpr ⟨xm,xc⟩
    have xe := fed off
    obtain ⟨a,ac,ax⟩ := mem_biUnion.mp (mem_sdiff.mp xe).1
    have bill := crossed_omissions free (by omega) (first.trans outN_subset) (Subset.rfl : C⊆C)
      len rooted ac (outN_subset xm) (mem_outN.mp ax).2
    have sub : outN D X x⊆C∩outN D V x := by
      intro w wm
      have wc : w∈C := by
        by_contra n
        have same := card_le_one.mp slots w (mem_sdiff.mpr ⟨outN_subset wm,n⟩) x off
        exact loopfree free (by omega) (outN_subset xm) (same ▸ (mem_outN.mp wm).2)
      exact mem_inter.mpr ⟨wc,outN_mono (outN_subset : X⊆V) x wm⟩
    have h := card_le_card sub
    have := card_sdiff_add_card_inter C (outN D V x)
    have nonempty := card_pos.mpr ⟨x,off⟩
    change 0<(outN D V u\C).card at nonempty
    omega
  have h := SinkDepthCover.omitted_heads (reg x (outN_subset xm)).ge
    (fun a (am : a∈outN D V x)=>headX (free.mono_bound hq) uv xm (outN_subset am) (mem_outN.mp am).2) internal
  change (Y\outN D V x).card+r≤Y.card+2 at h
  change Y.card≤r at upper
  change (Y\outN D V x).card≤2
  omega

theorem bounded_middle_cycle {D V q r C u} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀x∈C,Rooted D V x C) (first : C⊆outN D V u)
    (ys : (N2 D V u).card=r) (zs : (N3 D V u).card+1=r)
    (proper : C.card<r) (miss : ∀x∈outN D V u,(N2 D V u\outN D V x).card≤2) :
    ∃K⊆N2 D V u,q<K.card ∧
      (N2 D V u\K).card≤1 ∧ ∀x∈K,Rooted D V x K := by
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  change Z.card+1=r at zs
  have cyclic : ¬QFree D Y Y.card := by
    intro dag
    have ret s (sm : s∈sinks D Y) : ∃x∈X,D s x=true := by
      by_contra! none
      have out : outN D V s⊆Z := by
        intro a am
        apply (headY (free.mono_bound (by omega : 4≤q)) uv (mem_filter.mp sm).1 (outN_subset am) (mem_outN.mp am).2).resolve_left
        intro h
        rcases mem_union.mp h with ax|ay
        · have := none a ax; have := (mem_outN.mp am).2; simp_all
        · exact (mem_filter.mp sm).2 a ay (mem_outN.mp am).2
      have bound := card_le_card out
      rw [reg _ (yv (mem_filter.mp sm).1)] at bound
      omega
    obtain ⟨S,_,charge,cover⟩ := split_sink_budget free yv xv first dag (by omega : 2+2≤q)
      (fun x xm=>((rooted x xm).one x xm).ge) miss ret
    have gaps := card_sdiff_of_subset first
    have bound := card_le_card first
    have dx := reg u uv
    change (X\C).card=X.card-C.card at gaps
    change X.card=r at dx
    change C.card≤X.card at bound
    have slots : (X\C).card≤1 := by omega
    have small : S.card≤2 := by
      by_contra! many
      have := Nat.mul_le_mul_right (q-1) (show 3≤S.card by omega)
      omega
    change Y.card=r at ys
    omega
  obtain ⟨K,ky,size,cy⟩ := actual_cycle free (by omega) yv cyclic
  exact ⟨K,ky,size,by change (Y\K).card≤1; have := card_sdiff_of_subset ky; change Y.card=r at ys; omega,cy⟩

theorem fed_middle_tiers {D V u C q r} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (uv : u∈V) (fits : r≤q+2) (len : q<C.card) (cy : ∀c∈C,Rooted D V c C)
    (first : C⊆outN D V u) (ys : (N2 D V u).card=r) (zs : (N3 D V u).card+1=r) (extraSize : C.card+1=r)
    (fed : outN D V u\C⊆exterior D V C) :
    C.card+6≤(C.filter (fun v=>3*r<(ball D V v 3).card)).card+
      2*(C.filter (fun v=>3*r+1<(ball D V v 3).card)).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have cv := first.trans xv
  have dx := reg u uv
  have miss := fed_extra_omissions free (by omega) reg uv fits len cy first ys.le fed
  obtain ⟨K,ky,kl,kg,roots⟩ := bounded_middle_cycle free hq reg uv fits len cy first ys zs (by omega) miss
  change Y.card=r at ys
  change Z.card+1=r at zs
  have kr := card_le_card ky
  change K.card≤Y.card at kr
  have cx := card_le_card first
  have full := full_second_bank (Z:=Z) free (by omega) reg xv yv ky kl roots kg zs
    (fun y ym a am=>mem_union.mpr (headY (free.mono_bound (by omega : 4≤q)) uv ym (outN_subset am) (mem_outN.mp am).2))
    miss (by omega) (by intro live; have := card_pos.mpr live; have := card_sdiff_of_subset ky; change (Y\K).card=Y.card-K.card at this; omega)
  have xz : Disjoint X Z := disjoint_left.mpr (fun a ax az=>(mem_N3.mp az).2 (ball_mono_radius (by decide : 1≤2) (X_B1 ax)))
  have yz : Disjoint Y Z := disjoint_left.mpr (fun a ay az=>(mem_N3.mp az).2 (mem_N2.mp ay).1)
  have margin := three_ball_margin free (by omega) reg xv yv zv disjXY xz yz ky kl roots miss full
    (card_pos.mp (by omega)) (by omega) (by omega)
  have gaps := card_sdiff_of_subset first
  change (X\C).card=X.card-C.card at gaps
  change X.card=r at dx
  change C.card≤X.card at cx
  have extra : (X\C).card=1 := by omega
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(X\C).card by omega)
  have wx := (mem_sdiff.mp wm).1
  have wc := (mem_sdiff.mp wm).2
  have we := fed wm
  obtain ⟨a,ac,aw⟩ := mem_biUnion.mp (mem_sdiff.mp we).1
  let P := ball (fun a b=>D b a) C a 2
  have grow := ball_one_growth (free.reverse.mono_set cv) (reverse_positive (by omega) cy) ac 2 (by omega)
  change 3≤P.card at grow
  have internal c (cm : c∈C) : 4≤(ball D C c 3).card :=
    ball_one_growth (free.mono_set cv) (fun v vm=>((cy v vm).one v vm).ge) cm 3 (by omega)
  have high c (cm : c∈C) : 3*r<(ball D V c 3).card := by
    have reserve := margin c (first cm)
    have used := (internal c cm).trans (card_le_card (ShellCycleSupply.lift_ball first : ball D C c 3⊆ball D X c 3))
    omega
  have inc : P⊆C.filter (fun v=>3*r+1<(ball D V v 3).card) := by
    intro c cm
    have cc : c∈C := ball_subset cm
    refine mem_filter.mpr ⟨cc,?_⟩
    obtain ⟨_,k,le,road⟩ := mem_ball.mp cm
    have localW : w∈ball D X c 3 := mem_ball.mpr ⟨wx,k+1,by omega,((road.reverse_of_mem ac).mono first).snoc wx (mem_outN.mp aw).2⟩
    have add : insert w (ball D C c 3)⊆ball D X c 3 := insert_subset localW (ShellCycleSupply.lift_ball first)
    have cost := card_le_card add
    rw [card_insert_of_notMem (fun inside=>wc (ball_subset inside))] at cost
    have reserve := margin c (first cc)
    have used := internal c cc
    omega
  have total := grow.trans (card_le_card inc)
  rw [filter_true_of_mem high]
  omega


#print axioms fed_extra_omissions
#print axioms bounded_middle_cycle
#print axioms fed_middle_tiers
end LeanCH.BR.LowShellCycleSelection
