import checkpoints.shen_extension.EqualMixedShells

import checkpoints.shen_extension.OneSpareShellEscape

namespace LeanCH.BR.CyclicFirstLayer
open Finset BRq2 BRq3 BR45 BRsGen SparseCycleReturns

/-- A directed cycle can spend at most its row omissions on returning
labels. If their possible destinations together leave at most two-quota
room, an actual next-layer row must use all available outer labels. -/
theorem full_outer_row {D V X Y Z q r m k}
    (free : QFree D V q) (hq : 2≤q) (cv : X⊆V) (yv : Y⊆V) (zv : Z⊆V)
    (cycle : X.card=q+1) (one : OutEq 1 D X) (nonempty : Y.Nonempty)
    (entry : ∀y∈Y,∃x∈X,D x y=true)
    (misses : ∀x∈X,(Y\outN D Y x).card≤m)
    (internal : ∀x∈X,2≤(outN D Y x).card)
    (out : ∀y∈Y,outN D V y⊆(X∪Y)∪Z)
    (min : ∀y∈Y,r≤(outN D V y).card) (narrow : Z.card<r)
    (cap : X.card*m<(k+1)*(X.card-2)) (room : Y.card+2*k≤2*q) :
    ∃p∈Y,Z⊆outN D V p := by
  classical
  let A := Y.filter (fun a=>(outN D X a).Nonempty)
  let J := A.biUnion (fun a=>outN D X a)
  have ay : A⊆Y := filter_subset _ _
  have jx : J⊆X := by
    intro x xm
    obtain ⟨a,_,arc⟩ := mem_biUnion.mp xm
    exact outN_subset arc
  have bound := omission_budget free cv (ay.trans yv) (Subset.rfl : X⊆X)
    cycle (fun x xm=>(one x xm).ge) hq (fun y ym=>(mem_filter.mp ym).2) (fun x xm=>by
      apply le_trans (card_le_card ?_) (misses x xm)
      intro a am
      obtain ⟨aa,no⟩ := mem_sdiff.mp am
      exact mem_sdiff.mpr ⟨ay aa,fun h=>no (mem_outN.mpr ⟨aa,(mem_outN.mp h).2⟩)⟩)
  have few : A.card≤k := by
    by_contra! many
    have lo : (k+1)*(X.card-2)≤A.card*(X.card-2) := Nat.mul_le_mul_right _ many
    exact (not_lt_of_ge (lo.trans bound)) cap
  have per a (am : a∈A) : (outN D X a).card≤2 := by
    obtain ⟨x,xm,arc⟩ := entry a (ay am)
    exact reached_cap (k:=1) free cv cycle one xm (yv (ay am)) arc outN_subset
      (fun c cm=>ball_of_adj (cv (outN_subset cm)) (mem_outN.mp cm).2) hq
  have sizeJ : J.card≤2*k := by
    have := (card_biUnion_le (s:=A) (t:=fun a=>outN D X a)).trans (sum_le_sum per)
    simpa [J,Nat.mul_comm] using this.trans (by simp only [sum_const,smul_eq_mul]; omega : (∑ _a ∈ A, 2)≤2*k)
  by_contra! failure
  have count y (ym : y∈Y) : 2≤(outN D (Y∪J) y).card := by
    have part : outN D V y⊆outN D (Y∪J) y ∪ outN D Z y := by
      intro a am
      obtain ⟨av,arc⟩ := mem_outN.mp am
      rcases mem_union.mp (out y ym am) with early|az
      · rcases mem_union.mp early with ax|known
        · have ret := mem_outN.mpr ⟨ax,arc⟩
          have ar : y∈A := mem_filter.mpr ⟨ym,⟨a,ret⟩⟩
          exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_biUnion.mpr ⟨y,ar,ret⟩),arc⟩)
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ known,arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨az,arc⟩)
    have h := (min y ym).trans ((card_le_card part).trans (card_union_le _ _))
    have strict : (outN D Z y).card<Z.card := by
      apply card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨outN_subset,?_⟩)
      intro eq
      apply failure y ym
      intro a am
      have atZ : a∈outN D Z y := eq.symm ▸ am
      exact mem_outN.mpr ⟨zv am,(mem_outN.mp atZ).2⟩
    omega
  have rank a (am : a∈Y∪J) : 2≤(outN D (Y∪J) a).card := by
    rcases mem_union.mp am with h|h
    · exact count a h
    · exact (internal a (jx h)).trans (card_le_card (outN_mono subset_union_left a))
  have w := corB (by omega) (free.mono_set (union_subset yv (jx.trans cv))) rank (nonempty.mono subset_union_left)
  have := card_union_le Y J
  omega
#print axioms full_outer_row

/-- Full access to the outer bank leaves exactly the cyclic prefix and
three disjoint banks in the three-ball. The first two internal steps
then identify the same marked set of heads at three consecutive rows. -/
theorem cyclic_prefix_false {D V X Y Z W q r x}
    (free : QFree D V q) (hq : 4≤q) (hr : 3≤r) (fit : r≤q+1)
    (xv : X⊆V) (yv : Y⊆V) (xm : x∈X) (one : OutEq 1 D X)
    (row : ∀a∈X,(outN D Y a).card+1=r)
    (disXY : Disjoint X Y) (earlyZ : Disjoint (X∪Y) Z) (earlyW : Disjoint ((X∪Y)∪Z) W)
    (zs : Z.card+1=r) (ws : W.card+1=r)
    (seeZ : Z⊆ball D V x 3) (seeW : W⊆ball D V x 3)
    (small : (ball D V x 3).card≤3*r+1)
    (out : ∀y∈Y,outN D V y⊆(X∪Y)∪Z) (min : ∀y∈Y,r≤(outN D V y).card) : False := by
  classical
  let T := ball D X x 3
  let A := ball D X x 2
  let H := outN D Y x
  let E := ball D V x 3
  have tx : T⊆X := ball_subset
  have at' : A⊆T := ball_mono_radius (by decide : 2≤3)
  have hy : H⊆Y := outN_subset
  have te : T⊆E := ShellCycleSupply.lift_ball xv
  have oneE : H⊆ball D V x 1 := fun h hm=>ball_of_adj (yv (hy hm)) (mem_outN.mp hm).2
  have he : H⊆E := oneE.trans (ball_mono_radius (by decide : 1≤3))
  have dis1 : Disjoint T H := disXY.mono tx hy
  have sub1 : T∪H⊆X∪Y := union_subset_union tx hy
  have dis2 := earlyZ.mono_left sub1
  have dis3 := earlyW.mono_left (union_subset_union sub1 (Subset.rfl : Z⊆Z))
  have sub : ((T∪H)∪Z)∪W⊆E := union_subset (union_subset (union_subset te he) seeZ) seeW
  have tally := card_le_card sub
  rw [card_union_of_disjoint dis3,card_union_of_disjoint dis2,card_union_of_disjoint dis1] at tally
  have width : H.card+1=r := row x xm
  have length := ball_one_growth (free.mono_set xv) (fun a am=>(one a am).ge) xm 3 (by omega)
  change 4≤T.card at length
  change E.card≤3*r+1 at small
  have eq : ((T∪H)∪Z)∪W=E := by
    apply eq_of_subset_of_card_le sub
    rw [card_union_of_disjoint dis3,card_union_of_disjoint dis2,card_union_of_disjoint dis1]
    omega
  have all a (am : a∈E) : a∈T ∨ a∈H ∨ a∈Z ∨ a∈W := by
    rw [←eq] at am
    simpa only [mem_union,or_assoc] using am
  have xCell a (am : a∈E) (ax : a∈X) : a∈T := by
    rcases all a am with h|h|h|h
    · exact h
    · exact (disjoint_left.mp disXY ax (hy h)).elim
    · exact (disjoint_left.mp earlyZ (mem_union_left _ ax) h).elim
    · exact (disjoint_left.mp earlyW (mem_union_left _ (mem_union_left _ ax)) h).elim
  have yCell a (am : a∈E) (ay : a∈Y) : a∈H := by
    rcases all a am with h|h|h|h
    · exact (disjoint_left.mp disXY (tx h) ay).elim
    · exact h
    · exact (disjoint_left.mp earlyZ (mem_union_right _ ay) h).elim
    · exact (disjoint_left.mp earlyW (mem_union_left _ (mem_union_right _ ay)) h).elim
  have same a (am : a∈A) : outN D Y a=H := by
    apply eq_of_subset_of_card_le
    · intro y ym
      exact yCell y (ball_step (ShellCycleSupply.lift_ball xv am) (yv (outN_subset ym)) (mem_outN.mp ym).2) (outN_subset ym)
    · have := row a (tx (at' am))
      omega
  have longA := ball_one_growth (free.mono_set xv) (fun a am=>(one a am).ge) xm 2 (by omega)
  change 3≤A.card at longA
  have difference := card_sdiff_add_card_eq_card at'
  have only : (T\A).card≤1 := by omega
  have noX h (hm : h∈H) c (cm : c∈X) (arc : D h c=true) : False := by
    have c2 := ball_step (oneE hm) (xv cm) arc
    have ct := xCell c (ball_mono_radius (by decide : 2≤3) c2) cm
    have ca : c∉A := by
      intro present
      have ah : h∈outN D Y c := (same c present).symm ▸ hm
      exact no_back_arc free (xv cm) (ball_of_adj (yv (hy hm)) (mem_outN.mp ah).2) (by omega) arc
    have unique (a) (am : a∈T) (outside : a∉A) : a=c :=
      card_le_one.mp only a (mem_sdiff.mpr ⟨am,outside⟩) c (mem_sdiff.mpr ⟨ct,ca⟩)
    have pos a (am : a∈T) : 1≤(outN D T a).card := by
      obtain ⟨w,wm⟩ := card_pos.mp (show 0<(outN D X a).card by rw [one a (tx am)]; decide)
      have wt : w∈T := by
        by_cases aa : a∈A
        · exact ball_step aa (outN_subset wm) (mem_outN.mp wm).2
        · obtain rfl := unique a am aa
          exact xCell w (ball_step c2 (xv (outN_subset wm)) (mem_outN.mp wm).2) (outN_subset wm)
      exact card_pos.mpr ⟨w,mem_outN.mpr ⟨wt,(mem_outN.mp wm).2⟩⟩
    obtain ⟨a,am,sink⟩ := exists_sink (free.mono_set (tx.trans xv)) ⟨c,ct⟩ (show T.card≤q by omega)
    obtain ⟨w,wm⟩ := card_pos.mp (pos a am)
    exact sink w (outN_subset wm) (mem_outN.mp wm).2
  obtain ⟨h,hm,stop⟩ := exists_sink (free.mono_set (hy.trans yv)) (card_pos.mp (show 0<H.card by omega))
    (show H.card≤q by omega)
  have contained : outN D V h⊆Z := by
    intro a am
    rcases mem_union.mp (out h (hy hm) am) with e|z
    · rcases mem_union.mp e with ax|ay
      · exact (noX h hm a ax (mem_outN.mp am).2).elim
      · exact (stop a (yCell a (ball_mono_radius (by decide : 2≤3) (ball_step (oneE hm) (yv ay) (mem_outN.mp am).2)) ay)
          (mem_outN.mp am).2).elim
    · exact z
  have := (min h (hy hm)).trans (card_le_card contained)
  omega
#print axioms cyclic_prefix_false


/-- When the first four shells have widths r, r+1, r−1, r−1 and
each first neighbour has at most 3r+1 vertices in its three-ball,
the first shell is acyclic. All paths and all shells use D itself. -/
theorem acyclic {D V q r u} (free : QFree D V q) (hq : 4≤q) (hr : 7≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (uv : u∈V) (ys : (N2 D V u).card=r+1)
    (zs : (N3 D V u).card+1=r) (ws : (ball D V u 4\ball D V u 3).card+1=r)
    (small : ∀x∈outN D V u,(ball D V x 3).card≤3*r+1) :
    QFree D (outN D V u) (outN D V u).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4\ball D V u 3
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have cut := free.mono_bound hq
  have dx : X.card=r := reg u uv
  change Y.card=r+1 at ys
  change Z.card+1=r at zs
  change W.card+1=r at ws
  change QFree D X X.card
  by_contra cy
  have size : X.card=q+1 := by
    by_contra ne
    exact cy ((free.mono_set xv).mono_bound (by omega))
  have minC (x) (xm : x∈X) : 1≤(outN D X x).card := by
    unfold QFree at cy
    push Not at cy
    obtain ⟨a,k,pos,le,walk⟩ := cy
    have eq : k=q+1 := by
      by_contra h
      exact (free.mono_set xv) a k pos (by omega) walk
    subst k
    obtain ⟨C,cx,cardC,paid⟩ := boundary_closed_walk_support (free.mono_set xv) walk
    obtain rfl := eq_of_subset_of_card_le cx (by omega)
    exact paid x xm
  have one : OutEq 1 D X := EqualShellEscape.one_head (free.mono_set xv) (by omega) size.le minC
  have xy : Disjoint X Y := disjXY
  have row x (xm : x∈X) : (outN D Y x).card+1=r := by
    have split : (outN D (X∪Y) x).card=r := by rw [←outN_X_eq cut uv xm]; exact reg x (xv xm)
    rw [card_outN_union xy,one x xm] at split
    omega
  have out y (ym : y∈Y) : outN D V y⊆(X∪Y)∪Z := fun a am=>by
    rcases headY cut uv ym (outN_subset am) (mem_outN.mp am).2 with hit|az
    · exact mem_union_left _ hit
    · exact mem_union_right _ az
  have rank y (ym : y∈Y) := (reg y (yv ym)).ge
  obtain ⟨p,pm,full⟩ := full_outer_row (k:=2) (m:=2) free (by omega) xv yv zv size one
    (card_pos.mp (show 0<Y.card by omega)) (fun _ ym=>parY uv ym)
    (fun x xm=>by have := row x xm; rw [card_sdiff_of_subset outN_subset]; omega)
    (fun x xm=>by have := row x xm; omega) out rank (by omega) (by omega) (by omega)
  obtain ⟨x,xm,xp⟩ := parY uv pm
  have z2 (z) (zm : z∈Z) : z∈ball D V x 2 := ball_step (ball_of_adj (yv pm) xp) (zv zm) (mem_outN.mp (full zm)).2
  have early2 : X∪Y⊆ball D V u 2 := by
    intro a am
    rcases mem_union.mp am with h|h
    · exact ball_mono_radius (by decide : 1≤2) (X_B1 h)
    · exact (mem_N2.mp h).1
  apply cyclic_prefix_false free hq (by omega) fit xv yv xm one row xy
    (disjoint_left.mpr (fun _ e t=>(mem_N3.mp t).2 (early2 e))) ?_ zs ws
    (fun z zm=>ball_mono_radius (by decide : 2≤3) (z2 z zm)) ?_ (small x xm) out rank
  · refine disjoint_left.mpr ?_
    intro a m t
    apply (mem_sdiff.mp t).2
    rcases mem_union.mp m with h|h
    · exact ball_mono_radius (by decide : 2≤3) (early2 h)
    · exact (mem_N3.mp h).1
  · intro w wm
    obtain ⟨z,z3,zw⟩ := ball_succ_pred uv (mem_sdiff.mp wm).1 (mem_sdiff.mp wm).2
    have late : z∉ball D V u 2 := fun early=>(mem_sdiff.mp wm).2 (ball_step early (ball_subset (mem_sdiff.mp wm).1) zw)
    exact ball_step (z2 z (mem_N3.mpr ⟨z3,late⟩)) (ball_subset (mem_sdiff.mp wm).1) zw
#print axioms acyclic

end LeanCH.BR.CyclicFirstLayer

