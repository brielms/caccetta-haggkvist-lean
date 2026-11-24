import checkpoints.shen_extension.WideMiddleBank

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

theorem export_floor {D V Z q r} (free : QFree D V q) (hq : 1≤q) (zv : Z⊆V)
    (deg : ∀v∈Z,r≤(outN D V v).card) (live : Z.Nonempty) (small : Z.card≤2*q) :
    r-1≤(exterior D V Z).card := by
  by_contra! low
  have min2 v (vm : v∈Z) : 2≤(outN D Z v).card := by
    have kept : outN D V v⊆outN D Z v∪exterior D V Z := by
      intro a am
      by_cases az : a∈Z
      · exact mem_union_left _ (mem_outN.mpr ⟨az,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨v,vm,am⟩,az⟩)
    have := (deg _ vm).trans ((card_le_card kept).trans (card_union_le _ _)); omega
  have := corB hq (free.mono_set zv) min2 live
  omega

/-- If a row misses at most d labels of a rooted cycle, every cycle
label is reached from the row in at most d+1 steps. -/
theorem fills_cycle {D V K q d x} (free : QFree D V q) (cv : K⊆V)
    (cy : ∀k∈K,Rooted D V k K) (len : q<K.card) (time : d+1≤q)
    (sparse : (K\outN D V x).card≤d) : K⊆ball D V x (d+1) := by
  intro k km
  let P := ball (fun a b=>D b a) K k d
  have grow := ball_one_growth (free.reverse.mono_set cv) (reverse_positive (by omega) cy) km d time
  change d+1≤P.card at grow
  have hit : ∃v∈P,v∈outN D V x := by
    by_contra! no
    have bound := card_le_card (show P⊆K\outN D V x from fun a am=>mem_sdiff.mpr ⟨ball_subset am,no _ am⟩)
    omega
  obtain ⟨v,vm,xv⟩ := hit
  obtain ⟨_,l,le,path⟩ := mem_ball.mp vm
  exact mem_ball.mpr ⟨cv km,l+1,by omega,.step (outN_subset xv) (mem_outN.mp xv).2 ((path.reverse_of_mem km).mono cv)⟩

/-- The same counted labels serve every row in X. Its internal ball can
be added without overlap, including any reached first head off its cycle. -/
theorem three_ball_margin {D V X Y K Z q r} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (xv : X⊆V) (yv : Y⊆V) (zv : Z⊆V)
    (xy : Disjoint X Y) (xz : Disjoint X Z) (yz : Disjoint Y Z)
    (ky : K⊆Y) (len : q<K.card) (cy : ∀v∈K,Rooted D V v K)
    (miss : ∀x∈X,(Y\outN D V x).card≤2)
    (full : K.card≤(K.filter (fun v=>Z⊆outN D V v)).card+2)
    (pos : Z.Nonempty) (small : Z.card≤2*q) (fit : 4<K.card) :
    ∀x∈X,(ball D X x 3).card+K.card+Z.card+(r-1)≤(ball D V x 3).card := by
  classical
  let G := K.filter (fun v=>Z⊆outN D V v)
  let W := exterior D V Z
  have kv := ky.trans yv
  have toZ x (xm : x∈X) : Z⊆ball D V x 2 := by
    have yes : ∃v∈G,v∈outN D V x := by
      by_contra! no
      have cost := card_le_card (show G⊆Y\outN D V x from fun a am=>
        mem_sdiff.mpr ⟨ky (mem_filter.mp am).1,no _ am⟩)
      have := miss x xm; change K.card≤G.card+2 at full; omega
    obtain ⟨v,vm,xh⟩ := yes
    intro z zm
    exact ball_step (ball_of_adj (outN_subset xh) (mem_outN.mp xh).2) (zv zm) (mem_outN.mp ((mem_filter.mp vm).2 zm)).2
  have fromK k (km : k∈K) : Z⊆ball D V k 3 := by
    have reach : ∃v∈ball D K k 2,v∈G := by
      by_contra! no
      have all := card_le_card (show ball D K k 2⊆K\G from fun v vm=>mem_sdiff.mpr ⟨ball_subset vm,no _ vm⟩)
      have grow := ball_one_growth (free.mono_set kv) (fun v vm=>((cy v vm).one v vm).ge) km 2 (by omega)
      rw [card_sdiff_of_subset (filter_subset _ _ : G⊆K)] at all
      change (ball D K k 2).card≤K.card-G.card at all
      have gsub := card_le_card (filter_subset _ _ : G⊆K)
      change G.card≤K.card at gsub
      change K.card≤G.card+2 at full; omega
    obtain ⟨v,vm,good⟩ := reach
    intro z zm
    exact ball_step (ShellCycleSupply.lift_ball kv vm) (zv zm) (mem_outN.mp ((mem_filter.mp good).2 zm)).2
  have off {A : Finset ℕ} {i} (av : A⊆V) (time : i+1≤q)
      (reach : ∀a∈A,Z⊆ball D V a i) : Disjoint A W := by
    apply disjoint_left.mpr
    intro a am wm
    obtain ⟨z,zm,arc⟩ := mem_biUnion.mp (mem_sdiff.mp wm).1
    obtain ⟨_,l,le,path⟩ := mem_ball.mp (reach a am zm)
    exact free a _ (by omega) (by omega) (path.snoc (av am) (mem_outN.mp arc).2)
  have xw := off xv (by omega : 2+1≤q) toZ
  have kw := off kv (by omega : 3+1≤q) fromK
  have zw : Disjoint Z W := disjoint_left.mpr (fun _ zm wm=>(mem_sdiff.mp wm).2 zm)
  have size := export_floor free (by omega) zv (fun v vm=>(reg v (zv vm)).ge) pos small
  intro x xm
  have shrink := card_le_card (show K\outN D V x⊆Y\outN D V x from fun _ m=>mem_sdiff.mpr ⟨ky (mem_sdiff.mp m).1,(mem_sdiff.mp m).2⟩)
  have seen := fills_cycle free kv cy len (by omega : 2+1≤q) (shrink.trans (miss x xm))
  let A := ball D X x 3
  have sub : A∪K∪Z∪W⊆ball D V x 3 := by
    apply union_subset (union_subset (union_subset (ShellCycleSupply.lift_ball xv) seen)
      ((toZ x xm).trans (fun _ h=>ball_mono_radius (by decide : 2≤3) h)))
    intro w wm
    obtain ⟨z,zm,arc⟩ := mem_biUnion.mp (mem_sdiff.mp wm).1
    exact ball_step (toZ x xm zm) (outN_subset arc) (mem_outN.mp arc).2
  have cap := card_le_card sub
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨xw.mono_left ball_subset,kw⟩,zw⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨xz.mono_left ball_subset,yz.mono_left ky⟩),
    card_union_of_disjoint ((xy.mono_right ky).mono_left ball_subset)] at cap
  change r-1≤W.card at size
  omega

/-- The internal three-ball has at least four labels on C; reaching the
exterior first head adds a fifth at each of three distinct predecessor rows. -/
theorem wide_tiers {D V u C q r} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (uv : u∈V) (fits : r≤q+2) (len : q<C.card) (cy : ∀c∈C,Rooted D V c C)
    (first : C⊆outN D V u) (upper : (N2 D V u).card≤r) (wide : r<(exterior D V C).card)
    (low : (ball D V u 3).card≤3*r) :
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
  obtain ⟨ys,miss⟩ := wide_all_rows free (by omega) reg uv fits len cy first upper wide
  obtain ⟨zs,K,ky,kl,kg,roots⟩ := wide_middle_bank free hq reg uv fits len cy first upper wide low
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
  have bal := gate_balance free (by omega) uv first
  change _+_+(exterior D V C).card=(X\C).card+Y.card at bal
  have extra : (X\C).card=1 := by omega
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(X\C).card by omega)
  have wx := (mem_sdiff.mp wm).1
  have wc := (mem_sdiff.mp wm).2
  have we : w∈exterior D V C := by
    by_contra off
    have positive := card_pos.mpr (show (privateHeads D V C u).Nonempty from ⟨w,mem_sdiff.mpr ⟨wm,off⟩⟩)
    omega
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

/-- No underfunded primary cycle can have exterior wider than the row degree. -/
theorem paid_wide {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) : (exterior D V C).card≤r := by
  by_contra! wide
  have ceiling := wide_score_ceiling free reg short ready wide
  obtain ⟨Y,ym,first,_⟩ := short.2.1
  obtain ⟨yk,yc⟩ := mem_filter.mp ym
  have low := (mem_filter.mp (mem_filter.mp (sel.represents Y yk)).1).2
  have uv := rep_native sel yk
  obtain ⟨hq,a,b,c,d,_⟩ := ready.cycle
  have bound := low_third_second free hq reg uv a b c d low
  change (ball D V (sel.rep Y) 2).card≤2*r+1 at bound
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at one
  have two := @card_B2 D V (sel.rep Y)
  have root := sel.rooted _ (sel.assigned _ yk)
  have len := sel.length _ (sel.assigned _ yk)
  have om := sel.loss _ (sel.assigned _ yk)
  rw [yc] at root len om
  have high := wide_tiers free hq reg uv ready.close len root first (by omega) wide low
  have fit := ready.close
  have factor := Nat.pow_le_pow_right (n:=2) (by decide) (show omissions D V C r≤2 by omega)
  have product := Nat.mul_le_mul (show r-q+1≤3 by omega) factor
  norm_num at product
  omega

attribute [aesop safe forward (immediate := [free,reg,short,ready]) (rule_sets := [CHGraphFamilies])] paid_wide
#print axioms paid_wide
#print axioms three_ball_margin
end LeanCH.BR.LowShellCycleSelection
