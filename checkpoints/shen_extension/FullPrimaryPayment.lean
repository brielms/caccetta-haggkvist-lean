import checkpoints.shen_extension.NarrowPrimaryFrontier

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank

/-- A degree-wide cyclic first layer and a degree-wide second layer
force the full middle score at the root and strictly higher scores on
each of its heads, whenever the root itself has low score. -/
theorem full_first_high {D V q r u} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (long : q<r)
    (roots : ∀x∈outN D V u,Rooted D V x (outN D V u))
    (width : (N2 D V u).card=r) (low : (ball D V u 3).card≤3*r) :
    (ball D V u 3).card=3*r ∧ ∀x∈outN D V u,3*r<(ball D V x 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have dx : X.card=r := reg u uv
  have ys : Y.card=r := width
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have bound : Z.card+1≤r := by dsimp [Z]; omega
  have out := ShellCycleSupply.head_exterior free (by omega) uv
  have miss x (xm : x∈X) : (Y\outN D V x).card≤1 := by
    have eq := row_omissions (roots _ xm) (reg _ (xv xm))
    unfold omissions at eq
    rw [out,width] at eq
    change (N2 D V u\outN D V x).card≤1; omega
  have menu y (ym : y∈Y) : outN D V y⊆(X∪Y)∪Z := fun _ am=>mem_union.mpr
    (headY (free.mono_bound (by omega : 4≤q)) uv ym (outN_subset am) (mem_outN.mp am).2)
  have cyclic : ¬QFree D Y Y.card := by
    intro dag
    have ret s (sm : s∈sinks D Y) : ∃x∈X,D s x=true := by
      by_contra! lost
      have sub : outN D V s⊆Z := by
        intro a am
        apply (mem_union.mp (menu _ (mem_filter.mp sm).1 am)).resolve_left
        intro early
        rcases mem_union.mp early with ax|ay
        · have := lost a ax; have := (mem_outN.mp am).2; simp_all
        · exact (mem_filter.mp sm).2 a ay (mem_outN.mp am).2
      have paid := card_le_card sub; rw [reg _ (yv (mem_filter.mp sm).1)] at paid; omega
    have bill := returning_sink_budget free yv xv dag (by omega : 1+2≤q)
      (fun x xm=>((roots x xm).one x xm).ge) miss ret
    have many := Nat.mul_le_mul_left Y.card (show 2≤q-1 by omega)
    omega
  obtain ⟨K,ky,len,rc⟩ := actual_cycle free (by omega) yv cyclic
  have slots : (Y\K).card≤1 := by have := card_sdiff_of_subset ky; omega
  have escape := second_cycle_escape free (by omega) xv yv ky len rc slots (fun y ym=>(reg y (yv ym)).ge)
    menu miss (by omega)
  have size : Z.card+1=r := by omega
  have full := full_second_bank free (by omega) reg xv yv ky len rc slots size menu
    (fun x xm=>(miss x xm).trans (by decide : 1≤2)) (by omega) (by
      intro live
      have := card_pos.mpr live; have h := card_sdiff_of_subset ky; omega)
  have xz : Disjoint X Z := disjoint_left.mpr
    (fun _ xm zm=>(mem_N3.mp zm).2 (ball_mono_radius (by decide : 1≤2) (X_B1 xm)))
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ ym zm=>(mem_N3.mp zm).2 (mem_N2.mp ym).1)
  have gain := three_ball_margin free (by omega) reg xv yv zv disjXY xz yz ky len rc
    (fun x xm=>(miss x xm).trans (by decide : 1≤2)) full (card_pos.mp (by omega)) (by omega) (by omega)
  refine ⟨by change (N3 D V u).card+1=r at size; omega,?_⟩
  intro x xm
  have cost := gain x xm
  have steps := ball_one_growth (free.mono_set xv) (fun a am=>((roots a am).one a am).ge) xm 3 (by omega)
  change 4≤(ball D X x 3).card at steps
  omega

/-- A full cycle used from an acyclic first layer covers the third shell
at every cycle row; these are all its nonsuccessor heads. -/
theorem full_secondary_complete {D V q r Y target} (free : QFree D V q) (reg : OutEq r D V)
    (sel : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (ym : Y∈classes D V 3 (3*r)) (dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (size : (sel.pay Y).card=r) : (exterior D V (sel.pay Y)).card=r-1 := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  let C := sel.pay Y
  let Z := N3 D V (sel.rep Y)
  have fit := ready.close
  have space := ready.space
  obtain ⟨_,zs,count,_⟩ := selected_stock free reg (by omega) sel ym ready.cycle dag (by omega) ready.distance ready.score
  change Z.card+1=r at zs
  change C.card≤(C.filter (fun a=>Z⊆outN D V a)).card+(r-C.card)*(r-q) at count
  change C.card=r at size
  have every : C.filter (fun a=>Z⊆outN D V a)=C := eq_of_subset_of_card_le (filter_subset _ _)
    (by rwa [size,Nat.sub_self,Nat.zero_mul,Nat.add_zero,←size] at count)
  have uv := rep_native sel ym
  have key := rep_key sel ym
  have cy := (claim_data free reg (by omega) sel ym ready.cycle dag ready.close ready.space ready.distance ready.score).inside
  have sep : Disjoint C Z := disjoint_left.mpr
    (fun _ am zm=>(mem_N3.mp zm).2 (mem_N2.mp (key.symm ▸ cy am)).1)
  have feeds v (vm : v∈C) : Z⊆outN D V v := by
    have inside : v∈C.filter (fun a=>Z⊆outN D V a) := every.symm ▸ vm
    simp only [mem_filter] at inside
    exact inside.2
  have sub : Z⊆exterior D V C := by
    obtain ⟨x,xm⟩ := card_pos.mp (by omega : 0<C.card)
    have all := (mem_filter.mp (every.symm ▸ xm)).2
    exact fun z zm=>mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,xm,all zm⟩,fun cm=>disjoint_left.mp sep cm zm⟩
  have equal : exterior D V C=Z := by
    apply eq_of_subset_of_card_le ?_ (card_le_card sub)
    intro z zm
    obtain ⟨v,vm,arc⟩ := mem_biUnion.mp (mem_sdiff.mp zm).1
    have root := sel.rooted _ (sel.assigned _ ym) v vm
    have root : Rooted D V v C := root
    have inside : Z⊆(outN D V v).erase (internalHead D C v) := fun a am=>
      mem_erase.mpr ⟨fun e=>disjoint_left.mp sep (e.symm ▸ outN_subset (successor_mem root)) am,
        feeds v vm am⟩
    have card := card_erase_of_mem (outN_mono root.sub v (successor_mem root))
    rw [reg v (root.sub vm)] at card
    change ((outN D V v).erase (internalHead D C v)).card=r-1 at card
    have exactRow := eq_of_subset_of_card_le inside (by omega)
    rw [exactRow,row_exterior root] 
    exact mem_inter.mpr ⟨zm,arc⟩
  change (exterior D V C).card=r-1
  rw [equal]; omega

/-- If a primary cycle has one omission and occupies an entire first
layer, the cycle determines every claimant's second layer. The entire
bill is at most one, and the high rows pay it strictly. -/
theorem full_at_one_false {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) (full : C.card=r)
    (width : (exterior D V C).card=r) : False := by
  classical
  have fit := ready.close
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  obtain ⟨bookedC,first,canonical,bill⟩ := short
  have same Y (ym : Y∈claims sel C) : C=outN D V (sel.rep Y) := by
    obtain ⟨yk,yc⟩ := mem_filter.mp ym
    have uv := rep_native sel yk
    apply eq_of_subset_of_card_le (canonical Y ym ?_) (by rw [reg _ uv,full])
    intro dag
    have stock := full_secondary_complete free reg sel ready yk dag (yc ▸ full)
    rw [yc,width] at stock
    omega
  have key Y (ym : Y∈claims sel C) : Y=exterior D V C := by
    obtain ⟨yk,_⟩ := mem_filter.mp ym
    rw [same Y ym,ShellCycleSupply.head_exterior free (by omega) (rep_native sel yk),rep_key sel yk]
  obtain ⟨Y,ym,_,_⟩ := first
  obtain ⟨yk,yc⟩ := mem_filter.mp ym
  have unique : claims sel C={Y} := eq_singleton_iff_unique_mem.mpr ⟨ym,fun Z zm=>(key Z zm).trans (key Y ym).symm⟩
  have uv := rep_native sel yk
  have low := (mem_filter.mp (mem_filter.mp (sel.represents Y yk)).1).2
  have len := sel.length _ (sel.assigned _ yk)
  have root := sel.rooted _ (sel.assigned _ yk)
  rw [yc] at len root
  have cy := same Y ym ▸ root
  have ys := (congrArg card (rep_key sel yk)).trans ((congrArg card (key Y ym)).trans width)
  obtain ⟨mid,rows⟩ := full_first_high free hq reg uv fit (by omega) cy ys low
  have unit : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have lower := sel.least Y yk v vm
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [mid] at lower
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have clean : ¬StrongTerminal D V r C := fun t=>by have := t.nextSize; omega
  simp only [ite_eq_right clean,add_zero] at bill
  unfold netDebt at bill
  rw [unique,sum_singleton] at bill
  have capAll T (tm : T∈booked sel) : omissions D V T r≤r-q := by
    obtain ⟨Z,zk,rfl⟩ := mem_image.mp tm; exact sel.loss _ (sel.assigned _ zk)
  have high : C.filter (fun v=>3*r<(ball D V v 3).card)=C := filter_true_of_mem (fun v vm=>rows v (same Y ym ▸ vm))
  have bad := shortfall_of_bill free reg (by omega : r-q+2≤q) sel capAll bookedC (by
    change (↑(receipts sel C).card:ℚ)+rowStock sel (booked sel) C≤_
    rw [unique,sum_singleton]; linarith only [bill])
  have om : omissions D V C r=1 := by unfold omissions; rw [width]; omega
  rw [unique,sum_singleton,om] at bad
  have tier := tier_stock D V C 3 (3*r)
  rw [high] at tier
  have upperDebt := Nat.mul_le_mul_right ((r-q+1)*2^1) unit
  simp only [one_mul,pow_one] at bad upperDebt
  omega

attribute [aesop safe forward (immediate := [free,reg,short,ready,full,width]) (rule_sets := [CHGraphFamilies])] full_at_one_false
#print axioms full_at_one_false
#print axioms full_secondary_complete
#print axioms full_first_high
end LeanCH.BR.LowShellCycleSelection
