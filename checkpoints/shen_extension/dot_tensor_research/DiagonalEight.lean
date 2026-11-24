import checkpoints.shen_extension.dot_tensor_research.SingleOmissionPacking
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7PackedEndpoint_20261121
import LeanCH.BR.BRHighTwoPredecessor

namespace LeanCH.BR.DiagonalEight
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion

/-- In a set of up to q+1 labels at least two rows have an external head:
otherwise delete one row and take a sink among the rest. -/
theorem two_exits {D V U q} (hf : QFree D V q) (hm : ∀v∈V,2≤(outN D V v).card)
    (uv : U⊆V) (lo : 2≤U.card) (hi : U.card≤q+1) :
    ∃P⊆U, P.card=2 ∧ ∀v∈P, ∃z∈outN D V v,z∉U := by
  classical
  let E := U.filter (fun v=>∃z∈outN D V v,z∉U)
  have count : 2≤E.card := by
    by_contra! h
    obtain ⟨a,au⟩ := card_pos.mp (by omega : 0<U.card)
    have singleton : ∃x∈U, E⊆{x} := by
      by_cases ne : E.Nonempty
      · obtain ⟨x,xe⟩ := ne
        exact ⟨x,(mem_filter.mp xe).1,fun z zm=>mem_singleton.mpr
          (card_le_one.mp (by omega : E.card≤1) z zm x xe)⟩
      · exact ⟨a,au,fun z zm=>(ne ⟨z,zm⟩).elim⟩
    obtain ⟨x,xu,xE⟩ := singleton
    have n := card_erase_of_mem xu
    obtain ⟨y,ym,sink⟩ := exists_sink (T:=U.erase x) (hf.mono_set ((erase_subset _ _).trans uv))
      (card_pos.mp (by omega)) (by omega)
    have yu := mem_of_mem_erase ym
    have sub : outN D V y⊆{x} := by
      intro z zm
      by_contra out
      have zx := fun e : z=x => out (mem_singleton.mpr e)
      by_cases zu : z∈U
      · exact sink z (mem_erase.mpr ⟨zx,zu⟩) (mem_outN.mp zm).2
      · exact (mem_erase.mp ym).1 (mem_singleton.mp (xE (mem_filter.mpr ⟨yu,z,zm,zu⟩)))
    have := card_le_card sub
    rw [card_singleton] at this
    have := hm y (uv yu)
    omega
  obtain ⟨P,pe,pc⟩ := exists_subset_card_eq count
  exact ⟨P,pe.trans (filter_subset _ _),pc,fun _ hp=>(mem_filter.mp (pe hp)).2⟩

private theorem forward {D V q k u z} (hf : QFree D V q) (hk : k+1≤q) (hu : u∈V)
    (hz : z∈outN D V u) : (ball D V z k).card+1≤(ball D V u (k+1)).card := by
  have edge := (mem_outN.mp hz).2
  have n : u∉ball D V z k := by
    intro m
    exact no_back_arc hf (mem_outN.mp hz).1 m hk edge
  have sub : insert u (ball D V z k)⊆ball D V u (k+1) := by
    intro x xm
    rcases mem_insert.mp xm with rfl|b
    · exact self_mem_ball hu
    · obtain ⟨xv,j,hj,p⟩ := mem_ball.mp b
      exact mem_ball.mpr ⟨xv,j+1,by omega,.step (mem_outN.mp hz).1 edge p⟩
  simpa only [card_insert_of_notMem n] using card_le_card sub

/-- A prefix with sixteen high rows and eight or nine other rows. -/
theorem dense_prefix {D V H} (hf : QFree D V 8) (hm : ∀v∈V,2≤(outN D V v).card)
    (sub : H⊆V) (nh : H.card=16) (hi : ∀v∈H,8≤(outN D V v).card)
    (n : V.card=24 ∨ V.card=25) : False := by
  classical
  let L := V\H
  have lv : L⊆V := sdiff_subset
  have lc : L.card+H.card=V.card := card_sdiff_add_card_eq_card sub
  have f := hf.mono_bound (by decide : 7≤8)
  have b1 (v) (vh : v∈H) : 9≤(ball D V v 1).card := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤8)) (sub vh)]; have := hi v vh; omega
  have b2 (v) (vh : v∈H) : 10≤(ball D V v 2).card := by
    have x := b1 v vh
    by_contra! sm
    have dim := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 1≤2))
    have m2 := minOut_prefix_erase (d:=2) hf (sub vh) (by decide : 1+1≤8) hm (by simp only [Nat.reduceAdd]; omega)
    rw [erase_ball_one_eq_outN hf (by decide) (sub vh)] at m2
    have d := hi v vh
    have b := corB (by decide : 1≤8) (hf.mono_set (outN_subset (D:=D) (W:=V) (y:=v))) m2
      (card_pos.mp (by omega))
    have e := card_B1 (hf.mono_bound (by decide : 4≤8)) (sub vh)
    omega
  obtain ⟨P,pL,np,exP⟩ := two_exits hf hm lv (by omega) (by omega)
  let L₁ := L\P
  have n1 : L₁.card+P.card=L.card := card_sdiff_add_card_eq_card pL
  have l₁ : L₁⊆V := sdiff_subset.trans lv
  obtain ⟨S,sL,ns,exS⟩ := two_exits hf hm l₁ (by omega) (by omega)
  let L₂ := L₁\S
  have n2 : L₂.card+S.card=L₁.card := card_sdiff_add_card_eq_card sL
  have l₂ : L₂⊆V := sdiff_subset.trans l₁
  obtain ⟨T,tL,nt,exT⟩ := two_exits hf hm l₂ (by omega) (by omega)
  have bP (v) (vp : v∈P) : 10≤(ball D V v 2).card ∧ 11≤(ball D V v 3).card ∧ 14≤(ball D V v 4).card := by
    obtain ⟨z,zm,zL⟩ := exP _ vp
    have zh : z∈H := by by_contra h; exact zL (mem_sdiff.mpr ⟨(mem_outN.mp zm).1,h⟩)
    have l := b1 z zh
    have m := b2 z zh
    have a := forward hf (by decide : 1+1≤8) (lv (pL vp)) zm
    have b := forward hf (by decide : 2+1≤8) (lv (pL vp)) zm
    simp only [Nat.reduceAdd] at a b
    exact ⟨by omega,by omega,high_two_predecessor_ball_four (by decide : 5≤7) f hm (lv (pL vp)) zm (hi _ zh)⟩
  have bS (v) (vs : v∈S) : 11≤(ball D V v 3).card ∧ 12≤(ball D V v 4).card := by
    obtain ⟨z,zm,zn⟩ := exS v vs
    have zp : z∈H ∨ z∈P := by by_contra! h; exact zn (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_outN.mp zm).1,h.1⟩,h.2⟩)
    have a := forward hf (by decide : 2+1≤8) (l₁ (sL vs)) zm
    have b := forward hf (by decide : 3+1≤8) (l₁ (sL vs)) zm
    simp only [Nat.reduceAdd] at a b
    rcases zp with h|p
    · have := b2 z h
      have := high_row_ball_three_min (by decide : 2≤2) (by decide : 2*2≤7+1) f hm (sub h) (hi z h)
      exact ⟨by omega,by omega⟩
    · obtain ⟨p2,p3,p4⟩ := bP z p
      exact ⟨by omega,by omega⟩
  have bT (v) (vt : v∈T) : 12≤(ball D V v 4).card := by
    obtain ⟨z,zm,zn⟩ := exT v vt
    have zp : z∈H ∨ z∈P ∨ z∈S := by by_contra! h; exact zn (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_outN.mp zm).1,h.1⟩,h.2.1⟩,h.2.2⟩)
    have b := forward hf (by decide : 3+1≤8) (l₂ (tL vt)) zm
    simp only [Nat.reduceAdd] at b
    rcases zp with h|p|s
    · have := high_row_ball_three_min (by decide : 2≤2) (by decide : 2*2≤7+1) f hm (sub h) (hi z h)
      omega
    · have := (bP z p).2.1; omega
    · have := (bS z s).1; omega
  let c := fun v=>(ball D V v 4).card
  have lower (U : Finset ℕ) (a : ℕ) (bounds : ∀v∈U,a≤c v) : U.card*a ≤ ∑v∈U,c v := by
    simpa only [sum_const_nat (fun _ _=>rfl)] using sum_le_sum bounds
  have hh := lower H 14 fun _ vh=>high_two_ball_four (by decide : 5≤7) f hm (sub vh) (hi _ vh)
  have hp := lower P 14 fun _ vp=>(bP _ vp).2.2
  have hs := lower S 12 fun _ vs=>(bS _ vs).2
  have ht := lower T 12 bT
  have hl := lower (L₂\T) 9 fun v vm=>ball_growth 8 (by decide) D V hf hm v (l₂ (mem_sdiff.mp vm).1) 4 (by decide)
  have h0 := sum_sdiff sub (f:=c)
  have h1 := sum_sdiff pL (f:=c)
  have h2 := sum_sdiff sL (f:=c)
  have h3 := sum_sdiff tL (f:=c)
  have nr := card_sdiff_add_card_eq_card tL
  change (∑v∈L,c v)+_= _ at h0
  change (∑v∈L₁,c v)+_= _ at h1
  change (∑v∈L₂,c v)+_= _ at h2
  have upper := incomparable_reach_identity hf (by decide : 4+4≤8)
  change _+2*(∑v∈V,c v)=_ at upper
  rcases n with n|n <;> rw [n] at upper <;> omega

theorem three25 {D V} (hf : QFree D V 8) (hm : ∀v∈V,8≤(outN D V v).card)
    {u} (hu : u∈V) : 25≤(ball D V u 3).card := by
  apply third_ball_ge_on_diagonal (by decide : 4≤8) (by decide : 8≤8) ?_ hf hm hu
  intro d lo hi F W ff deg ne
  by_cases seven : d=7
  · subst d; by_contra! sm; exact DotDegreeSevenQ8.eight_free_seven_order ff ne (by omega) deg
  by_cases six : d=6
  · subst d; exact BRq6.card_ge_forty_nine ff deg ne
  · exact BRq6.lower_order (by decide) lo (by omega) ff deg ne

private theorem two17 {D V} (hf : QFree D V 8) (hm : ∀v∈V,8≤(outN D V v).card)
    {u} (hu : u∈V) : 17≤(ball D V u 2).card :=
  card_ball_two_ge_twice (by decide : 2≤8) hf hm hu

/-- At a root with at most 32 vertices within four steps the only possible
third-ball size is 25, and its fourth ball has exactly 32. -/
theorem short_four {D V} (hf : QFree D V 8) (hm : ∀v∈V,8≤(outN D V v).card)
    {u} (hu : u∈V) (cap : (ball D V u 4).card≤32) :
    (ball D V u 3).card=25 ∧ (ball D V u 4).card=32 := by
  classical
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  let T := ball D V u 4 \ ball D V u 3
  have na := three25 hf hm hu
  have nb := two17 hf hm hu
  have uv : U⊆V := (erase_subset _ _).trans ball_subset
  have hU : H⊆U := erase_subset_erase u (ball_mono_radius (by decide : 2≤3))
  have dim : T.card+(ball D V u 3).card=(ball D V u 4).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have uc : U.card=(ball D V u 3).card-1 := card_erase_of_mem (self_mem_ball hu)
  have hc : H.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball hu)
  obtain ⟨J,jH,j16⟩ := exists_subset_card_eq (show 16≤H.card by omega)
  have ju := jH.trans hU
  have high (v) (jv : v∈J) : 8≤(outN D U v).card :=
    (hm v (uv (ju jv))).trans (card_le_card (outN_prefix_erase_root hf hu
      (by decide : 2+1≤8) (mem_of_mem_erase (jH jv))))
  have ff := hf.mono_set uv
  have rank (d) (pay : d+T.card≤8) := minOut_prefix_erase hf hu (by decide : 3+1≤8) hm pay
  by_contra! no
  by_cases small : U.card≤25
  · exact dense_prefix ff (rank 2 (by omega)) ju j16 high (by omega)
  have ne := card_pos.mp (show 0<U.card by omega)
  by_cases mid : U.card=26
  · have three := rank 3 (by omega)
    have low (v) (hv : v∈U) : 13≤(ball D U v 4).card :=
      ball_of_min (BRq3.ball_all 5 (by decide)) (ff.mono_bound (by decide)) three v hv
    have big (v) (hv : v∈J) : 14≤(ball D U v 4).card :=
      (high_row_ball_three_min (by decide : 2≤3) (by decide : 2*3≤7+1)
        (ff.mono_bound (by decide)) three (ju hv) (high _ hv)).trans (card_le_card
          (ball_mono_radius (by decide : 3≤4)))
    have up := incomparable_reach_identity ff (by decide : 4+4≤8)
    have s1 := sum_le_sum big
    have s2 := sum_le_sum (s:=U\J) (fun v hv=>low v (mem_sdiff.mp hv).1)
    have part := sum_sdiff ju (f:=fun v=>(ball D U v 4).card)
    have nL := card_sdiff_add_card_eq_card ju
    simp only [sum_const_nat (fun _ _=>rfl)] at s1 s2
    rw [mid] at up
    omega
  · have hyp := BRq6.lower_order (by decide : 5≤8) (by decide : 2≤4) (by decide : 4<6)
      ff (rank 4 (by omega)) ne
    omega

theorem fourth32 {D V} (hf : QFree D V 8) (hm : ∀v∈V,8≤(outN D V v).card)
    {u} (hu : u∈V) : 32≤(ball D V u 4).card := by
  by_contra! lo; have := (short_four hf hm hu lo.le).2; omega


theorem short_profile {D V} (hf : QFree D V 8) (ho : OutEq 8 D V)
    {u} (hu : u∈V) (cap : (ball D V u 4).card≤32) :
    (ball D V u 2).card=18 ∧ (ball D V u 3).card=25 ∧ (ball D V u 4).card=32 := by
  classical
  have hm : ∀ v∈V,8≤(outN D V v).card := fun v hv=>(ho v hv).ge
  obtain ⟨b3,b4⟩ := short_four hf hm hu cap
  refine ⟨?_,b3,b4⟩
  have b2 := two17 hf hm hu
  have b1 : (ball D V u 1).card=9 := by rw [card_B1 (hf.mono_bound (by decide : 4≤8)) hu,ho u hu]
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  have dimY : Y.card+(ball D V u 1).card=(ball D V u 2).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have dimZ : Z.card+(ball D V u 2).card=(ball D V u 3).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have dimT : T.card+(ball D V u 3).card=(ball D V u 4).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  by_contra! no
  by_cases eq : (ball D V u 2).card=17
  · have back := BRsub.equal_triple_layers_no_back (s:=8) (by decide)
        (hf.mono_bound (by decide : 8-1≤8)) hu hm (ho u hu)
        (show Y.card=8 by omega) (show Z.card=8 by omega) (show T.card≤8-1 by omega)
    have zv : Z⊆V := fun _ hx=>ball_subset (mem_sdiff.mp hx).1
    obtain ⟨z,zm,sink⟩ := exists_sink (T:=Z) (hf.mono_set zv) (card_pos.mp (show 0<Z.card by omega)) (show Z.card≤8 by omega)
    have inc : outN D V z⊆T := by
      intro x xm
      obtain ⟨xv,e⟩ := mem_outN.mp xm
      refine mem_sdiff.mpr ⟨ball_step (mem_sdiff.mp zm).1 xv e,?_⟩
      intro w
      by_cases b : x∈ball D V u 2
      · exact back z zm x b e
      · exact sink x (mem_sdiff.mpr ⟨w,b⟩) e
    have := card_le_card inc
    have := ho z (zv zm)
    omega
  let U := (ball D V u 2).erase u
  let H := outN D V u
  have uv : U⊆V := (erase_subset _ _).trans ball_subset
  have hv : H⊆U := by
    change outN D V u ⊆ (ball D V u 2).erase u
    rw [←erase_ball_one_eq_outN hf (by decide) hu]
    exact erase_subset_erase u (ball_mono_radius (by decide))
  have uc : U.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball hu)
  have h8 : H.card=8 := ho u hu
  have high (v) (vh : v∈H) : 8≤(outN D U v).card :=
    (hm v (uv (hv vh))).trans (card_le_card (outN_prefix_erase_root hf hu
      (by decide : 1+1≤8) ((mem_ball_one hu).mpr (Or.inr vh))))
  have ff := hf.mono_set uv
  by_cases e19 : (ball D V u 2).card=19
  · have rank := minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤8) hm (show 2+Z.card≤8 by omega)
    have hi (v) (vh : v∈H) : 14≤(ball D U v 4).card :=
      high_two_ball_four (by decide : 5≤7) (ff.mono_bound (by decide)) rank (hv vh) (high _ vh)
    have low (v) (vm : v∈U\H) : 9≤(ball D U v 4).card :=
      ball_growth 8 (by decide) D U ff rank v (mem_sdiff.mp vm).1 4 (by decide)
    have x := sum_le_sum hi
    have y := sum_le_sum low
    have k := card_sdiff_add_card_eq_card hv
    have p := sum_sdiff hv (f:=fun v=>(ball D U v 4).card)
    have up := incomparable_reach_identity ff (by decide : 4+4≤8)
    rw [show U.card=18 by omega] at up
    simp only [sum_const_nat (fun _ _=>rfl)] at x y
    omega
  · have rank := minOut_prefix_erase (d:=3) hf hu (by decide : 2+1≤8) hm (show 3+Z.card≤8 by omega)
    have bad := BRq6.lower_order (by decide : 5≤8) (by decide : 2≤3) (by decide : 3<6) ff rank
      (card_pos.mp (show 0<U.card by omega))
    omega


theorem short_to_tall {D V} (hf : QFree D V 8) (ho : OutEq 8 D V) {u} (hu : u∈V)
    (cap : (ball D V u 4).card≤32) :
    ∃v∈outN D V u, 33≤(ball D V v 4).card ∧
      ((ball D V v 2).card=17 ∨
      (SingleOmissionPacking.Sink D (outN D V u) v ∧ (ball D V v 2).card=18 ∧ 26≤(ball D V v 3).card)) := by
  classical
  obtain ⟨two,three,four⟩ := short_profile hf ho hu cap
  by_cases rich : ∀v∈outN D V u,18≤(ball D V v 2).card
  · obtain ⟨_,_,v,vm,sink,_,sz,inc⟩ := SingleOmissionPacking.recursive_successor
      (by decide : 4≤8) (by decide : 8≤8) (by decide : 7<8) hf ho hu two rich three
    have part := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
    have big : 26≤(ball D V v 3).card := by omega
    refine ⟨v,vm,?_,Or.inr ⟨sink,sz,big⟩⟩
    by_contra! small
    have := (short_profile hf ho (mem_outN.mp vm).1 (by omega)).2.1
    omega
  · push Not at rich
    obtain ⟨v,vm,small⟩ := rich
    have floor := two17 hf (fun j jm=>(ho j jm).ge) (mem_outN.mp vm).1
    refine ⟨v,vm,?_,Or.inl (by omega)⟩
    by_contra! h
    have := (short_profile hf ho (mem_outN.mp vm).1 (by omega)).1
    omega

theorem order_at_least_64 {D V} (hf : QFree D V 8) (hm : ∀v∈V,8≤(outN D V v).card)
    (ne : V.Nonempty) : 64≤V.card := by
  classical
  obtain ⟨F,sub,ho⟩ := exists_outEq hm
  have ff := qfree_sub sub hf
  have floor (v) (hv : v∈V) := fourth32 ff (fun j jm=>(ho j jm).ge) hv
  have size := card_ge_of_two_balls ff (by decide : 4+4≤8) floor floor ne
  by_contra! h
  have all := two_balls_boundary_cards ff (by decide : 4+4≤8) floor floor (by omega)
  obtain ⟨u,hu⟩ := ne
  obtain ⟨v,vm,tall,_⟩ := short_to_tall ff ho hu (all u hu).1.le
  have := (all v (mem_outN.mp vm).1).1
  omega

theorem half_short_on_64 {D V} (hf : QFree D V 8) (hm : ∀v∈V,8≤(outN D V v).card)
    (n : V.card=64) : 32≤(V.filter (fun v=>(ball D V v 4).card=32)).card := by
  classical
  let S := V.filter (fun v=>(ball D V v 4).card=32)
  have sub : S⊆V := filter_subset _ _
  have small (v) (vm : v∈S) : 32≤(ball D V v 4).card := (mem_filter.mp vm).2.ge
  have tall (v) (vm : v∈V\S) : 33≤(ball D V v 4).card := by
    have vv := (mem_sdiff.mp vm).1
    have lo := fourth32 hf hm vv
    by_contra! no
    exact (mem_sdiff.mp vm).2 (mem_filter.mpr ⟨vv,by omega⟩)
  have a := sum_le_sum small
  have b := sum_le_sum tall
  have part := sum_sdiff sub (f:=fun v=>(ball D V v 4).card)
  have sizes := card_sdiff_add_card_eq_card sub
  have up := incomparable_reach_identity hf (by decide : 4+4≤8)
  rw [n] at up
  simp only [sum_const_nat (fun _ _=>rfl)] at a b
  change 32≤S.card
  omega
#print axioms order_at_least_64
#print axioms short_to_tall
#print axioms half_short_on_64

/-- When at least half the vertices belong to S and each row of S has an exit,
either two rows share an exterior head, or both sides have equal size and each
row of S has exactly one exit. In the latter case deleting the exterior loses
exactly one head from each row of S. -/
theorem shared_exit_or_balanced {D : CH.Digraph} {V S : Finset ℕ} (sub : S⊆V)
    (half : V.card≤2*S.card) (esc : ∀i∈S,(outN D V i \ S).Nonempty) :
    (∃i∈S, ∃j∈S,i≠j ∧ ∃z∈outN D V i, z∈outN D V j ∧ z∉S) ∨
    (S.card=(V\S).card ∧ ∀i∈S,(outN D V i \ S).card=1 ∧
      (outN D S i).card+1=(outN D V i).card) := by
  classical
  let B := fun i=>outN D V i \ S
  by_cases hit : ∃i∈S, ∃j∈S,i≠j ∧ ∃z∈outN D V i,z∈outN D V j ∧ z∉S
  · exact Or.inl hit
  have dis : (S : Set ℕ).PairwiseDisjoint B := by
    intro i im j jm ne
    apply disjoint_left.mpr
    intro z zi zj
    exact hit ⟨i,im,j,jm,ne,z,(mem_sdiff.mp zi).1,(mem_sdiff.mp zj).1,(mem_sdiff.mp zi).2⟩
  have cover : S.biUnion B ⊆ V\S := by
    intro z zm
    obtain ⟨i,_,a⟩ := mem_biUnion.mp zm
    exact mem_sdiff.mpr ⟨(mem_outN.mp (mem_sdiff.mp a).1).1,(mem_sdiff.mp a).2⟩
  have up := card_le_card cover
  rw [card_biUnion dis] at up
  have row (i) (im : i∈S) : 1≤(B i).card := card_pos.mpr (esc i im)
  have lo := sum_le_sum row
  have part := card_sdiff_add_card_eq_card sub
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at lo
  have eq : (∑ _i∈S,(1:ℕ)) = ∑ i∈S,(B i).card := by
    simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one]
    omega
  have ones := (sum_eq_sum_iff_of_le row).mp eq
  refine Or.inr ⟨by omega,?_⟩
  intro i im
  have one := (ones i im).symm
  refine ⟨one,?_⟩
  have inside : outN D S i ⊆ outN D V i := fun j jm=>mem_outN.mpr
    ⟨sub (mem_outN.mp jm).1,(mem_outN.mp jm).2⟩
  have outside : outN D V i \ outN D S i = B i := by
    ext j
    simp only [B,mem_sdiff,mem_outN]
    tauto
  have ct := card_sdiff_add_card_eq_card inside
  rw [outside,one] at ct
  omega

theorem shared_tall_on_64 {D V} (hf : QFree D V 8) (ho : OutEq 8 D V) (n : V.card=64) :
    ∃u∈V, ∃v∈V, u≠v ∧ (ball D V u 4).card=32 ∧ (ball D V v 4).card=32 ∧
      ∃z∈outN D V u, z∈outN D V v ∧ 33≤(ball D V z 4).card := by
  classical
  let S := V.filter (fun i=>(ball D V i 4).card=32)
  have sub : S⊆V := filter_subset _ _
  have half : 32≤S.card := half_short_on_64 hf (fun j jm=>(ho j jm).ge) n
  have esc (i) (im : i∈S) : (outN D V i \ S).Nonempty := by
    obtain ⟨v,vm,big,_⟩ := short_to_tall hf ho (sub im) (mem_filter.mp im).2.le
    exact ⟨v,mem_sdiff.mpr ⟨vm,fun a=>by have := (mem_filter.mp (show v∈S from a)).2; omega⟩⟩
  rcases shared_exit_or_balanced sub (by omega) esc with hit|⟨bal,one⟩
  · obtain ⟨u,um,v,vm,ne,z,zu,zv,zs⟩ := hit
    refine ⟨u,sub um,v,sub vm,ne,(mem_filter.mp um).2,(mem_filter.mp vm).2,z,zu,zv,?_⟩
    have vv := (mem_outN.mp zu).1
    have lo := fourth32 hf (fun j m=>(ho j m).ge) vv
    by_contra! sm
    exact zs (mem_filter.mpr ⟨vv,by omega⟩)
  · have sizes := card_sdiff_add_card_eq_card sub
    have all (i) (im : i∈S) : 7≤(outN D S i).card := by
      have := (one i im).2
      have := ho i (sub im)
      omega
    exact False.elim (DotDegreeSevenQ8.eight_free_seven_order (hf.mono_set sub)
      (card_pos.mp (by omega)) (by omega) all)
#print axioms shared_exit_or_balanced
#print axioms shared_tall_on_64

/-- Literal cycle conclusion on the degree-eight strip below its top order. -/
theorem cycle_at_most_eight (D : CH.Digraph) {n : ℕ} (hn : 0<n) (cap : n≤63)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 8) :
    CH.HasDirectedCycleAtMost D n 8 := by
  by_contra none
  have floor := order_at_least_64 (qfree_of_noShort loopless none)
    (fun _ hv=>Compose.FloorSix.out_card degree (mem_range.mp hv)) (nonempty_range_iff.mpr (by omega))
  rw [card_range] at floor
  omega

open CHRuleCatalog in
/-- The closure applies again at any depth in the counterexample catalog. -/
theorem impossible_at_descendant {p c : Input} (bp : Bad p) (path : Relation.ReflTransGen Child p c)
    (degree : c.s=8) (cut : cutoff c=8) (order : c.n≤63) : False := by
  have bc := bad_descendant bp path
  have hn : 0<c.n := by have := bc.order; omega
  have cy := cycle_at_most_eight c.D hn order bc.loopless (by simpa only [degree] using bc.degree)
  exact bc.missing (by simpa only [cut] using cy)

#print axioms cycle_at_most_eight
#print axioms impossible_at_descendant

#print axioms short_profile
#print axioms fourth32
#print axioms two_exits
#print axioms dense_prefix
end LeanCH.BR.DiagonalEight
