import checkpoints.shen_extension.ReturningSinkBudget

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- An induced cycle in the second bank leaves at most one exceptional
label. Two missing exterior slots require every cycle row to feed the
exception. It can feed neither the cycle nor any row that sees the cycle. -/
theorem second_cycle_escape {D V X Y Z K q r d} (free : QFree D V q) (hq : 3≤q)
    (xv : X⊆V) (yv : Y⊆V) (ky : K⊆Y) (size : q<K.card)
    (rooted : ∀x∈K,Rooted D V x K) (thin : (Y\K).card≤1)
    (keep : ∀y∈Y,r≤(outN D V y).card) (menu : ∀y∈Y,outN D V y⊆(X∪Y)∪Z)
    (miss : ∀x∈X,(Y\outN D V x).card≤d) (depth : d<q-1) :
    r≤Z.card+1 := by
  classical
  by_contra! short
  have safe v (vm : v∈K) x (xm : x∈X) : D v x≠true := by
    intro arc
    have bill := crossed_omissions free (by omega) yv ky size rooted vm (xv xm) arc
    have := miss x xm
    omega
  have need v (vm : v∈K) : ∃b∈Y\K,D v b=true := by
    by_contra! none
    have sub : outN D V v⊆outN D K v∪Z := by
      intro a am
      have arc := (mem_outN.mp am).2
      rcases mem_union.mp (menu v (ky vm) am) with early|late
      · have ay := (mem_union.mp early).resolve_left (fun ax=>safe v vm a ax arc)
        have ak : a∈K := by by_contra no; have := none a (mem_sdiff.mpr ⟨ay,no⟩); simp_all
        exact mem_union_left _ (mem_outN.mpr ⟨ak,arc⟩)
      · exact mem_union_right _ late
    have h := (keep v (ky vm)).trans ((card_le_card sub).trans (card_union_le _ _))
    rw [(rooted v vm).one v vm] at h
    omega
  obtain ⟨v,vm⟩ := card_pos.mp (by omega : 0<K.card)
  obtain ⟨b,bm,_⟩ := need v vm
  have all v (vm : v∈K) : D v b=true := by
    obtain ⟨a,am,e⟩ := need v vm
    exact card_le_one.mp thin a am b bm ▸ e
  have bv := yv (mem_sdiff.mp bm).1
  have see x (xm : x∈X) : ∃w∈K,D x w=true := by
    by_contra! no
    have sub : K⊆Y\outN D V x := fun w wm=>mem_sdiff.mpr ⟨ky wm,fun arc=>by
      have := no w wm; have := (mem_outN.mp arc).2; simp_all⟩
    have := (card_le_card sub).trans (miss x xm)
    omega
  have outside : outN D V b⊆Z := by
    intro a am
    have arc := (mem_outN.mp am).2
    apply (mem_union.mp (menu b (mem_sdiff.mp bm).1 am)).resolve_left
    intro h
    rcases mem_union.mp h with ax|ay
    · obtain ⟨w,wm,e⟩ := see a ax
      exact free b 3 (by decide) hq (.step (xv ax) arc (.step (yv (ky wm)) e (.step bv (all w wm) (.refl b))))
    · by_cases ak : a∈K
      · exact digonfree free (by omega) bv (yv ay) arc (all a ak)
      have same := card_le_one.mp thin a (mem_sdiff.mpr ⟨ay,ak⟩) b bm
      exact loopfree free (by omega) bv (same ▸ arc)
  have := (keep _ (mem_sdiff.mp bm).1).trans (card_le_card outside)
  omega

/-- A first-layer bank with exterior wider than the degree uses its unique
extra first head. Even that extra row omits at most two second-shell labels. -/
theorem wide_all_rows {D V q r C u} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀x∈C,Rooted D V x C) (first : C⊆outN D V u)
    (upper : (N2 D V u).card≤r) (wide : r<(exterior D V C).card) :
    (N2 D V u).card=r ∧ ∀x∈outN D V u,(N2 D V u\outN D V x).card≤2 := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  have sz := reg u uv
  have gaps := card_sdiff_of_subset first
  have cc := card_le_card first
  have slots : (X\C).card≤1 := by dsimp [X]; omega
  have bal := gate_balance free hq uv first
  change _+_+(exterior D V C).card=(X\C).card+Y.card at bal
  change Y.card≤r at upper
  have ys : Y.card=r := by omega
  have empty : privateHeads D V C u=∅ := card_eq_zero.mp (by omega)
  refine ⟨ys,?_⟩
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
    have xe : x∈exterior D V C := by
      by_contra no
      have : x∈privateHeads D V C u := mem_sdiff.mpr ⟨off,no⟩
      simp [empty] at this
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
  change (Y\outN D V x).card≤2
  omega

theorem wide_short_false {D V q r C u} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀x∈C,Rooted D V x C) (first : C⊆outN D V u)
    (upper : (N2 D V u).card≤r) (wide : r<(exterior D V C).card) :
    3*r≤(ball D V u 3).card := by
  by_contra! short
  have dag := wide_short_second_cycle free hq reg uv fits len rooted first upper wide short
  obtain ⟨K,ky,size,rootK⟩ := actual_cycle free (by omega) (fun _ ym=>N2_subV ym) dag
  obtain ⟨ys,miss⟩ := wide_all_rows free (by omega) reg uv fits len rooted first upper wide
  have gap := card_sdiff_of_subset ky
  have cap := card_le_card ky
  have escaped := second_cycle_escape (Z:=N3 D V u) free (by omega) (outN_subset : outN D V u⊆V)
    (fun _ ym=>N2_subV ym) ky size rootK (by omega) (fun y ym=>(reg y (N2_subV ym)).ge)
    (fun y ym a am=>mem_union.mpr (headY (free.mono_bound (by omega : 4≤q)) uv ym (outN_subset am) (mem_outN.mp am).2))
    miss (by omega)
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  omega

/-- For an unpaid primary cycle with wide exterior, the short-source
alternative disappears. Only the actual score of its own rows remains. -/
theorem wide_score_ceiling {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) (wide : r<(exterior D V C).card) :
    (C.filter (fun v=>3*r<(ball D V v 3).card)).card+
    2*(C.filter (fun v=>3*r+1<(ball D V v 3).card)).card ≤ (r-q+1)*2^(omissions D V C r) := by
  apply (wide_price free reg short ready wide).resolve_left
  rintro ⟨Y,ym,low⟩
  obtain ⟨yk,yc⟩ := mem_filter.mp ym
  have hr := ready.growth.2.1
  have hq := ready.cycle.1
  have uv := rep_native sel yk
  have first := short.2.2.1 Y ym (by
    intro dag
    have h := (claim_data free reg (by omega) sel yk ready.cycle dag ready.close ready.space ready.distance ready.score).loss
    rw [yc] at h
    unfold omissions at h
    omega)
  have root := sel.rooted _ (sel.assigned _ yk)
  have len := sel.length _ (sel.assigned _ yk)
  rw [yc] at len root
  obtain ⟨_,a,b,c,d,_⟩ := ready.cycle
  have high := low_third_second free hq reg uv a b c d low.le
  change (ball D V (sel.rep Y) 2).card≤2*r+1 at high
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at one
  have two := @card_B2 D V (sel.rep Y)
  exact low.not_ge (wide_short_false free hq reg uv ready.close len root first (by omega) wide)

attribute [aesop safe forward (immediate := [free,reg,short,ready,wide]) (rule_sets := [CHGraphFamilies])] wide_score_ceiling
#print axioms wide_score_ceiling
#print axioms wide_short_false
end LeanCH.BR.LowShellCycleSelection
