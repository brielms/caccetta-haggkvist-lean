import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7Mixed_20261121
import LeanCH.BR.BRHighPairGrowth
import LeanCH.BR.BRHighTwoPredecessor

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45 BRsGen

private theorem twin_miss {D V q a b j} (hf : QFree D V q) (hj : j≤q) (ab : a≠b)
    (same : outN D V a = outN D V b) : b∉ball D V a j := by
  intro h
  obtain ⟨_,k,hk,w⟩ := mem_ball.mp h
  cases k with
  | zero => cases w; exact ab rfl
  | succ k =>
    cases w with
    | step xv e tail =>
      have xm : _∈outN D V a := mem_outN.mpr ⟨xv,e⟩
      rw [same] at xm
      exact hf b (k+1) (by omega) (by omega) (.step xv (mem_outN.mp xm).2 tail)

/-- A 21-label prefix with fourteen original degree-seven rows
and minimum degree two cannot be seven-free. -/
theorem fourteen_high_on_twenty_one {D V H} (hf : QFree D V 7)
    (hm : ∀ v∈V, 2≤(outN D V v).card) (n : V.card=21)
    (sub : H⊆V) (nh : H.card=14) (high : ∀ v∈H, 7≤(outN D V v).card) : False := by
  classical
  let L := V\H
  have l7 : L.card=7 := by have := card_sdiff_add_card_eq_card sub; change (V\H).card=7; omega
  let P := H.filter (fun v => outN D V v ⊆ L)
  have pv : P⊆V := (filter_subset _ _).trans sub
  have same (v) (hv : v∈P) : outN D V v=L :=
    eq_of_subset_of_card_le (mem_filter.mp hv).2 (by rw [l7]; exact high _ (mem_filter.mp hv).1)
  have six := hf.mono_bound (by decide : 6≤7)
  obtain ⟨y,yl,sink⟩ := exists_sink (T:=L) (hf.mono_set (sdiff_subset : L⊆V))
    (card_pos.mp (show 0<L.card by omega)) (show L.card≤7 by omega)
  have yv := (mem_sdiff.mp yl).1
  have yn := (mem_sdiff.mp yl).2
  obtain ⟨z,zy⟩ := card_pos.mp (by have := hm y yv; omega : 0<(outN D V y).card)
  have zh : z∈H := by
    by_contra h
    exact sink z (mem_sdiff.mpr ⟨(mem_outN.mp zy).1,h⟩) (mem_outN.mp zy).2
  have bonus := high_two_predecessor_ball_four (by decide : 5≤6) six hm yv zy (high _ zh)
  have low (v) (hv : v∈V) :
      16 + (if v∈H then 9 else 0) + (if v=y then 2 else 0) ≤
      (ball D V v 3).card+(ball D V v 4).card+(if v∈P then 1 else 0) := by
    have b3 := ball_growth 7 (by decide) D V hf hm v hv 3 (by decide)
    have b4 := ball_growth 7 (by decide) D V hf hm v hv 4 (by decide)
    by_cases mh : v∈H
    · have vy : v≠y := fun e => yn (e ▸ mh)
      have a := high_row_ball_three_min (by decide : 2≤2) (by decide : 2*2≤6+1)
        six hm hv (high _ mh)
      by_cases mp : v∈P
      · have b := high_two_ball_four (by decide : 5≤6) six hm hv (high _ mh)
        simp only [mh,mp,vy,ite_true,ite_false]; omega
      · have ex : ∃ z∈outN D V v,z∈H := by
          by_contra! no
          exact mp (mem_filter.mpr ⟨mh,fun z hz=>mem_sdiff.mpr ⟨(mem_outN.mp hz).1,no z hz⟩⟩)
        obtain ⟨w,wm,wh⟩ := ex
        have b := high_two_pair_ball_four (by decide : 5≤6) six hm hv (high _ mh) wm (high _ wh)
        simp only [mh,mp,vy,ite_true,ite_false]; omega
    · have mp : v∉P := fun h => mh (mem_filter.mp h).1
      by_cases eq : v=y
      · subst v; simp only [yn,mp,ite_false,ite_true]; omega
      · simp only [mh,mp,eq,ite_false]; omega
  have total := sum_le_sum low
  simp only [sum_add_distrib, sum_const_nat (fun _ _=>rfl),sum_ite_mem,
    inter_eq_right.mpr sub,inter_eq_right.mpr pv,sum_ite_eq',yv,ite_true] at total
  have cap (v) (hv : v∈V) :
      (ball D V v 3).card+(reverseBall D V v 4).card+
      (if v∈P ∧ 2≤P.card then 1 else 0) ≤22 := by
    have base := reverseBall_add_ball_le (v:=v) hf (by decide : 3+4≤7)
    split
    · rename_i ok
      obtain ⟨w,wm,ne⟩ := exists_mem_ne (s:=P) (a:=v) (by omega : 1<P.card)
      have eq := (same v ok.1).trans (same w wm).symm
      let C := (V\ball D V v 3) ∪ {v}
      have inC : w∈C := mem_union_left _ (mem_sdiff.mpr ⟨pv wm,
        twin_miss hf (by decide : 3≤7) ne.symm eq⟩)
      have absent : w∉reverseBall D V v 4 := fun m =>
        twin_miss hf (by decide : 4≤7) ne eq.symm (mem_filter.mp m).2
      have strict := card_lt_card (ssubset_iff_of_subset
        (reverseBall_subset_complement (v:=v) hf (by decide : 3+4≤7)) |>.mpr ⟨w,inC,absent⟩)
      have bound := card_union_le (V\ball D V v 3) {v}
      rw [card_sdiff_of_subset ball_subset,card_singleton] at bound
      have vb := card_le_card (ball_subset (D:=D) (W:=V) (u:=v) (k:=3))
      omega
    · omega
  have summed := sum_le_sum cap
  rw [sum_add_distrib,sum_add_distrib,sum_reverseBall_eq_sum_ball] at summed
  by_cases big : 2≤P.card
  · simp only [big,and_true,sum_ite_mem,inter_eq_right.mpr pv,sum_const_nat (fun _ _=>rfl)] at summed
    simp [n,nh] at total summed
    omega
  · simp only [big,and_false,ite_false,sum_const_nat (fun _ _=>rfl)] at summed
    simp [n,nh] at total summed
    omega

/-- At cutoff seven every root has at least 28 vertices in its inclusive four-ball. -/
theorem four_ball_ge28 {D V} (hf : QFree D V 7) (hm : ∀ v∈V,7≤(outN D V v).card)
    {u : ℕ} (hu : u∈V) : 28≤(ball D V u 4).card := by
  classical
  by_contra! small
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  let T := ball D V u 4 \ ball D V u 3
  have uv : U⊆V := (erase_subset _ _).trans ball_subset
  have sub : H⊆U := erase_subset_erase u (ball_mono_radius (by decide : 2≤3))
  have dim : T.card+(ball D V u 3).card=(ball D V u 4).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have three := floor_three hf hm u hu
  have two := floor_two hf hm u hu
  have uc : U.card=(ball D V u 3).card-1 := card_erase_of_mem (self_mem_ball hu)
  have hc : H.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball hu)
  have hn : 14≤H.card := by omega
  have ne : U.Nonempty := (card_pos.mp (show 0<H.card by omega)).mono sub
  have high (v) (hv : v∈H) : 7≤(outN D U v).card :=
    (hm v (uv (sub hv))).trans (card_le_card (outN_prefix_erase_root hf hu
      (by decide : 2+1≤7) (mem_of_mem_erase hv)))
  have f := hf.mono_set uv
  by_cases low : U.card=21
  · obtain ⟨J,jsub,j14⟩ := exists_subset_card_eq hn
    apply fourteen_high_on_twenty_one f _ low (jsub.trans sub) j14 (fun x hx=>high x (jsub hx))
    exact minOut_prefix_erase hf hu (by decide : 3+1≤7) hm (show 2+T.card≤7 by omega)
  by_cases mid : U.card=22
  · have d := minOut_prefix_erase hf hu (by decide : 3+1≤7) hm (show 3+T.card≤7 by omega)
    have reg := (dt_reg (by decide : 1≤7) (BRq3.ball_all 7 (by decide)) f d mid).1
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<H.card by omega)
    have r := reg v (sub hv)
    have h := high v hv
    omega
  · have d := minOut_prefix_erase hf hu (by decide : 3+1≤7) hm (show 4+T.card≤7 by omega)
    have e := BRq6.lower_order (by decide : 5≤7) (by decide : 2≤4) (by decide : 4<6) f d ne
    omega

/-- Handles the entire order-48 case, with the original minimum outdegree assumption. -/
theorem seven_free_min_seven_ge49 {D V} (hf : QFree D V 7)
    (hm : ∀v∈V,7≤(outN D V v).card) (ne : V.Nonempty) : 49≤V.card := by
  have h := card_ge_of_two_balls hf (by decide : 3+4≤7) (floor_three hf hm)
    (fun _ hv=>four_ball_ge28 hf hm hv) ne
  omega

theorem order49_exact_balls {D V} (hf : QFree D V 7)
    (hm : ∀v∈V,7≤(outN D V v).card) (n : V.card=49) (u) (hu : u∈V) :
    (ball D V u 3).card=22 ∧ (ball D V u 4).card=28 ∧
    reverseBall D V u 4=(V\ball D V u 3)∪{u} := by
  have fl := fun v (hv : v∈V)=>four_ball_ge28 hf hm hv
  have cc := two_balls_boundary_cards hf (by decide : 3+4≤7) (floor_three hf hm) fl (by omega) u hu
  exact ⟨cc.1,cc.2.1,two_balls_boundary_complement hf (by decide : 3+4≤7)
    (floor_three hf hm) fl (by omega) hu⟩

#print axioms fourteen_high_on_twenty_one
#print axioms four_ball_ge28
#print axioms seven_free_min_seven_ge49
#print axioms order49_exact_balls
end LeanCH.BR.DotDegreeSevenQ7
