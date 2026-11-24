import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import LeanCH.BR.BR96

namespace LeanCH.BR.DotDegreeSevenQ8
open Finset BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport
open DotFourthPrefixQuadratic DotClonePairCompletion
open scoped BigOperators

private abbrev Deg (D : CH.Digraph) (V : Finset ℕ) :=
  ∀ v ∈ V, 7 ≤ (outN D V v).card

private noncomputable abbrev Size (D : CH.Digraph) (V : Finset ℕ) (u k : ℕ) :=
  (ball D V u k).card

private abbrev Floor (k b : ℕ) :=
  ∀ {D : CH.Digraph} {V : Finset ℕ}, QFree D V 8 → Deg D V → ∀ u ∈ V, b ≤ Size D V u k

theorem floor_two : Floor 2 15 :=
  fun hf hm _ hu => card_ball_two_ge_twice (by decide : 2≤7) (hf.mono_bound (by decide)) hm hu

theorem floor_three : Floor 3 22 := by
  intro D V hf hm u hu
  apply third_ball_ge_on_diagonal (by decide : 4≤7) (by decide : 7≤8) ?_ hf hm hu
  intro d lo hi F W ff mm ww
  by_cases e : d=6
  · subst d
    exact ShenFourthStrip.previous_degree_order (a:=0) ff mm ww
  · exact BRq6.lower_order (by decide : 5≤8) lo (by omega) ff mm ww

private theorem order55 {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 8) (hm : Deg D V)
    (hne : V.Nonempty) : 55≤V.card := by
  have h := ShenFourthStrip.order_above_second (a:=0) hf hm hne
  omega

private theorem floor_four27 : Floor 4 27 := by
  intro D V hf hm u hu
  have h := ShenFourthStrip.radius_R_growth (a:=0) hf hm hu
  simp only [Size,Nat.reduceAdd] at *
  omega

private theorem dimensions {D : CH.Digraph} {V : Finset ℕ} {u i : ℕ} (hu : u∈V) :
    (layer D V (i+1) u).card + Size D V u i = Size D V u (i+1) ∧
    (shell D V (i+1) u).card + Size D V u (i+1) = Size D V u (i+2) ∧
    ((ball D V u (i+1)).erase u).card+1 = Size D V u (i+1) := by
  constructor
  · simpa only [layer,Nat.add_sub_cancel] using
      (card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show i≤i+1 by omega)))
  constructor
  · simpa only [shell,Nat.add_assoc] using
      (card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show i+1≤i+2 by omega)))
  · have hc := card_erase_of_mem (self_mem_ball (D:=D) (k:=i+1) hu)
    have hp := card_pos.mpr ⟨u,self_mem_ball (D:=D) (k:=i+1) hu⟩
    simp only [Size] at *
    omega

/-- Same concrete prefix, physical missing cells, and arithmetic on the genuine completed host.
The floor used in the collision inequality is universal, not capped by the original order. -/
private theorem packet {D : CH.Digraph} {V : Finset ℕ} {u k : ℕ}
    (hf : QFree D V 8) (hm : Deg D V) (hu : u∈V) (hk : k+2≤8)
    (ht : (shell D V (k+1) u).card<7) :
    ∃ N, 55≤N ∧
      N+holes D V (k+1) u ≤
        ((ball D V u (k+1)).erase u).card +
          (layer D V (k+1) u).card*(shell D V (k+1) u).card ∧
      ∀ b, Floor 4 b →
        10*N+2*N*b ≤ N*(N+1)+10*((ball D V u (k+1)).erase u).card+
          20*(layer D V (k+1) u).card := by
  let U := (ball D V u (k+1)).erase u
  let S := layer D V (k+1) u
  let g := fun a => 7-(outN D U a).card
  obtain ⟨hne,hr,hs,hzero,hbudget⟩ := prefix_gap_budget hf hm hu (by decide : 1≤7) hk ht
  have huV : U⊆V := (erase_subset _ _).trans ball_subset
  obtain ⟨F,W,f,p,hF,hd,hc,hn,hp,he,hB,hPr⟩ :=
    exists_deficiency_completion_bundles (d:=7) (hf.mono_set huV) hr
  change W.card=U.card+∑ a ∈ U,g a at hc
  change (∑ a ∈ U,g a)+holes D V (k+1) u ≤ S.card*(shell D V (k+1) u).card at hbudget
  have eq : ∑ a ∈ U,g a = ∑ a ∈ S,g a := by
    have h0 : ∑ a ∈ U \ S,g a=0 := sum_eq_zero hzero
    have hpart : (∑ a ∈ U \ S,g a)+(∑ a ∈ S,g a)=(∑ a ∈ U,g a) := sum_sdiff hs
    omega
  change ∃ N, 55≤N ∧ N+holes D V (k+1) u ≤ U.card+S.card*(shell D V (k+1) u).card ∧
    ∀ b, Floor 4 b → 10*N+2*N*b ≤ N*(N+1)+10*U.card+20*S.card
  refine ⟨W.card,order55 hF hd (hn hne),by omega,?_⟩
  intro b floor
  have main := joint_completion_pair_bound (r:=4) (B:=b) (hf.mono_set huV) hp he
    (by decide) (fun x hx => hB x (hs hx)) (fun x hx => hPr x (hs hx))
    (floor hF hd)
  change (∑ x ∈ S,g x*(g x+1))+2*W.card*b≤W.card*(W.card+1) at main
  have term (x : ℕ) : 10*g x≤g x*(g x+1)+20 := by
    by_cases h : g x≤8
    · interval_cases gx : g x <;> omega
    · have hmul := Nat.mul_le_mul_left (g x) (show 10≤g x+1 by omega)
      omega
  have sm := sum_le_sum (s:=S) (fun x _ => term x)
  rw [←Finset.mul_sum, sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at sm

  omega

/-- First replay: on any completed graph the older universal floor 27 applies. -/
theorem floor_four28 : Floor 4 28 := by
  intro D V hf hm u hu
  have h2 := floor_two hf hm u hu
  have h3 := floor_three hf hm u hu
  have h4 := floor_four27 hf hm u hu
  by_contra! low
  obtain ⟨hS,hT,hU⟩ := dimensions (i:=2) hu (D:=D)
  simp only [Size,Nat.reduceAdd] at *
  obtain ⟨N,hN,budget,pairs⟩ := packet hf hm hu (k:=2) (by decide) (by
    simp only [Nat.reduceAdd]
    omega)
  simp only [Nat.reduceAdd] at budget pairs
  have ar (T S X U H N : ℕ) (lo : 55≤N) (x : 22≤X)
      (t : T+X=27) (s : S+15≤X) (u : U+1=X)
      (b : N+H≤U+S*T) : X=22 ∧ S=7 ∧ N≤56 := by
    have ht : T≤5 := by omega
    interval_cases T <;> omega
  obtain ⟨hx,hc,hupper⟩ := ar _ _ _ _ _ _ hN h3 (by omega) (by omega) (by omega) budget
  have c := pairs 27 floor_four27

  interval_cases N <;> omega

private theorem floor_five33 : Floor 5 33 := by
  intro D V hf hm u hu
  have h := ShenFourthStrip.growth_step (a:=0) (k:=3) (g0:=0) (g1:=1) (g2:=3)
    hf hm hu (by decide)
    (by have := floor_three hf hm u hu; simp only [Size,Nat.reduceAdd] at *; omega)
    (by have := floor_four28 hf hm u hu; simp only [Size,Nat.reduceAdd] at *; omega)
    (by decide) (by decide) (by decide) (by decide)
  simp only [Size,Nat.reduceAdd] at *
  omega

private theorem full_cap {D : CH.Digraph} {V : Finset ℕ} {u k L b : ℕ}
    (hf : QFree D V 8) (hu : u∈V)
    (hk : k+1+L≤8) (hL : L+2≤8)
    (st : ∀ y∈V, ((ball D V u k).erase u).card < Size D V y k)
    (low : ∀ y∈V,b≤Size D V y L)
    (room : V.card≤((ball D V u (k+1)).erase u).card+b+1) :
    (fullColumns D V (k+1) u).card≤2 := by
  classical
  let U := (ball D V u (k+1)).erase u
  let C := fullColumns D V (k+1) u
  let K := V \ U
  have f := full_bank_avoids hf hu hk (fun y hy => st y (ball_subset (mem_of_mem_erase hy)))
  have cv : C⊆V := fun _ hy => shell_subset (mem_filter.mp hy).1
  have ck : C⊆K := fun y hy => f y hy (self_mem_ball (cv hy))
  have sz := card_sdiff_add_card_eq_card ((erase_subset u (ball D V u (k+1))).trans (ball_subset (D:=D)))
  change C.card≤2
  by_contra! more
  obtain ⟨A,sub,ac⟩ := exists_subset_card_eq (show 3≤C.card by omega)
  apply near_full_container_false hf hL (sub.trans cv) (sub.trans ck) (fun x hx => f x (sub hx)) ?_
    (by omega) (by omega)
  intro x hx
  have cnt := card_sdiff_add_card_eq_card (f x (sub hx))
  have l := low x (cv (sub hx))
  change b≤(ball D V x L).card at l
  change (K \ ball D V x L).card+(ball D V x L).card=K.card at cnt
  change K.card+U.card=V.card at sz
  change U.card+b+1≥V.card at room
  omega

theorem floor_five34_capped {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 8) (hm : Deg D V) (ord : V.card≤56) (u) (hu : u∈V) :
    34≤Size D V u 5 := by
  have h3 := floor_three hf hm u hu
  have h4 := floor_four28 hf hm u hu
  have h5 := floor_five33 hf hm u hu
  by_contra! low
  obtain ⟨hS,hT,hU⟩ := dimensions (i:=3) hu (D:=D)
  simp only [Size,Nat.reduceAdd] at *
  obtain ⟨N,hN,budget,_⟩ := packet hf hm hu (k:=3) (by decide) (by
    simp only [Nat.reduceAdd]
    omega)
  simp only [Nat.reduceAdd] at budget
  have ar (T S X Y U H N : ℕ) (lo : 55≤N) (x : 28≤X) (y : 22≤Y)
      (t : T+X=33) (s : S+Y=X) (u : U+1=X)
      (b : N+H≤U+S*T) : Y=22 ∧ T≥5-1 ∧ T≥H+3 ∧ U≥27 := by
    have ht : T≤5 := by omega
    interval_cases T <;> omega
  obtain ⟨hy,_,hc,hU27⟩ := ar _ _ _ _ _ _ _ hN h4 h3 (by omega) hS hU budget
  have cap := full_cap hf hu (k:=3) (L:=4) (b:=28) (by decide) (by decide) ?_
    (floor_four28 hf hm) (by simpa only [Nat.reduceAdd] using (show V.card≤((ball D V u 4).erase u).card+28+1 by omega))
  · have holes := full_columns_bound (D:=D) (V:=V) (R:=4) (u:=u)
    simp only [Nat.reduceAdd] at cap
    omega
  · intro y hy'
    have h := floor_three hf hm y hy'
    have hc := card_erase_of_mem (self_mem_ball (D:=D) (k:=3) hu)
    simp only [Size] at *
    omega

#print axioms floor_four28
#print axioms floor_five34_capped

private theorem bad_prefix_two {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 8) (hm : Deg D V) (hu : u∈V)
    (h2 : (ball D V u 2).card=16) (h3 : (ball D V u 3).card=22) : False := by
  let U := (ball D V u 2).erase u
  let X := outN D V u
  have sub : X⊆U := by
    change outN D V u⊆(ball D V u 2).erase u
    rw [←erase_ball_one_eq_outN hf (by decide : 1≤8) hu]
    exact erase_subset_erase u (ball_mono_radius (by decide))
  have hU : U.card≤8+7 := by
    change ((ball D V u 2).erase u).card≤8+7
    rw [card_erase_of_mem (self_mem_ball hu),h2]
  have nxt := (dimensions (D:=D) (i:=1) hu).2.1
  simp only [Size,Nat.reduceAdd] at nxt
  have min1 : ∀ v∈U, 1≤(outN D U v).card := by
    apply minOut_prefix_erase (d:=1) hf hu (by decide : 2+1≤8) hm
    change 1+(shell D V 2 u).card≤7
    omega
  have high (v) (hv : v∈X) : 7≤(outN D U v).card := by
    have h := outN_prefix_erase_root hf hu (by decide : 1+1≤8)
      ((mem_ball_one hu).mpr (Or.inr hv))
    exact (hm v (outN_subset hv)).trans (card_le_card h)
  have low := small_one_high_degree_count_of_le (by decide : 3≤7) (by decide : 7≤8)
    (hf.mono_set ((erase_subset u _).trans ball_subset)) hU min1 sub high
  exact (Nat.not_lt.mpr (hm u hu)) low

private theorem full_cap_one {D : CH.Digraph} {V : Finset ℕ} {u k L b : ℕ}
    (hf : QFree D V 8) (hu : u∈V) (hk : k+1+L≤8) (hL : L+1≤8)
    (st : ∀ y∈V, ((ball D V u k).erase u).card < (ball D V y k).card)
    (low : ∀ y∈V,b≤(ball D V y L).card)
    (room : V.card≤((ball D V u (k+1)).erase u).card+b) :
    (fullColumns D V (k+1) u).card≤1 := by
  classical
  let U := (ball D V u (k+1)).erase u
  let K := V \ U
  let C := fullColumns D V (k+1) u
  have f := full_bank_avoids hf hu hk (fun y hy => st y (ball_subset (mem_of_mem_erase hy)))
  have cv : C⊆V := fun _ hy => shell_subset (mem_filter.mp hy).1
  have sz : K.card+U.card=V.card :=
    card_sdiff_add_card_eq_card ((erase_subset u _).trans ball_subset)
  change V.card≤U.card+b at room
  have eq (x) (hx : x∈C) : ball D V x L=K :=
    eq_of_subset_of_card_le (f x hx) (by have := low x (cv hx); omega)
  apply card_le_one.mpr
  intro x hx y hy
  exact ball_root_injective_short hf hL (cv hx) (cv hy) ((eq x hx).trans (eq y hy).symm)

private theorem full_cap_zero {D : CH.Digraph} {V : Finset ℕ} {u k L b : ℕ}
    (hf : QFree D V 8) (hu : u∈V) (hk : k+1+L≤8)
    (st : ∀ y∈V, ((ball D V u k).erase u).card < (ball D V y k).card)
    (low : ∀ y∈V,b≤(ball D V y L).card)
    (room : V.card<((ball D V u (k+1)).erase u).card+b) :
    (fullColumns D V (k+1) u).card=0 := by
  classical
  by_contra! no
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<(fullColumns D V (k+1) u).card)
  have f := full_bank_avoids hf hu hk (fun y hy => st y (ball_subset (mem_of_mem_erase hy))) x hx
  have cnt := card_le_card f
  have sz := card_sdiff_add_card_eq_card
    ((erase_subset u (ball D V u (k+1))).trans (ball_subset (D:=D)))
  have lo := low x (shell_subset (mem_filter.mp hx).1)
  omega

theorem floor_four29_capped {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 8) (hm : Deg D V) (ord : V.card≤56) (u) (hu : u∈V) :
    29≤Size D V u 4 := by
  have h2 := floor_two hf hm u hu
  have h3 := floor_three hf hm u hu
  have h4 := floor_four28 hf hm u hu
  by_contra! low
  obtain ⟨hS,hT,hU⟩ := dimensions (i:=2) hu (D:=D)
  simp only [Size,Nat.reduceAdd] at *
  obtain ⟨N,hN,budget,pairs⟩ := packet hf hm hu (k:=2) (by decide) (by
    simp only [Nat.reduceAdd]; omega)
  simp only [Nat.reduceAdd] at budget pairs
  have out := pairs 28 floor_four28
  have hole := full_columns_bound (D:=D) (V:=V) (R:=3) (u:=u)
  have ar (T S X U H N : ℕ) (lo : 55≤N) (x : 22≤X)
      (t : T+X=28) (s : S+15≤X) (u : U+1=X)
      (b : N+H≤U+S*T) : X=22 ∨ X=23 ∨ X=24 := by
    have ht : T≤6 := by omega
    interval_cases T <;> omega
  have profiles := ar _ _ _ _ _ _ hN h3 (by omega) (by omega) hU budget
  have b2e : (ball D V u 2).card=15 := by
    by_contra! ne
    have y : 16≤(ball D V u 2).card := by omega
    rcases profiles with hx|hx|hx
    · have t : (shell D V 3 u).card=6 := by omega
      rw [t] at budget
      have hy : (ball D V u 2).card=16 := by omega
      exact bad_prefix_two hf hm hu hy hx
    · have t : (shell D V 3 u).card=5 := by omega
      rw [t] at budget
      have hupper : N≤57 := by omega
      interval_cases N <;> omega
    · have t : (shell D V 3 u).card=4 := by omega
      rw [t] at budget
      have hupper : N≤55 := by omega
      interval_cases N <;> omega
  have st (y) (hy : y∈V) : ((ball D V u 2).erase u).card < (ball D V y 2).card := by
    have hy2 := floor_two hf hm y hy
    have hc := card_erase_of_mem (self_mem_ball (D:=D) (k:=2) hu)
    simp only [Size] at *
    omega
  have fl (x) (hx : x∈V) : 34≤(ball D V x 5).card := floor_five34_capped hf hm ord x hx
  rcases profiles with hx|hx|hx
  · have t : (shell D V 3 u).card=6 := by omega
    rw [t] at budget hole
    have top := full_cap hf hu (k:=2) (L:=5) (b:=34) (by decide) (by decide) st fl
      (by simp only [Nat.reduceAdd]; omega)
    simp only [Nat.reduceAdd] at top
    have hupper : N≤59 := by omega
    interval_cases N <;> omega
  · have t : (shell D V 3 u).card=5 := by omega
    rw [t] at budget hole
    have top := full_cap_one hf hu (k:=2) (L:=5) (b:=34) (by decide) (by decide) st fl
      (by simp only [Nat.reduceAdd]; omega)
    simp only [Nat.reduceAdd] at top
    have hupper : N≤58 := by omega
    interval_cases N <;> omega
  · have t : (shell D V 3 u).card=4 := by omega
    rw [t] at budget hole
    have top := full_cap_zero hf hu (k:=2) (L:=5) (b:=34) (by decide) st fl
      (by simp only [Nat.reduceAdd]; omega)
    simp only [Nat.reduceAdd] at top
    have hupper : N≤55 := by omega
    interval_cases N <;> omega

/-- Entire cutoff-eight strip at minimum outdegree seven, via actual completed children. -/
theorem eight_free_seven_order {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 8) (hn : V.Nonempty) (ord : V.card≤56) (hm : Deg D V) : False := by
  have growth := floor_four29_capped hf hm ord
  have h := card_ge_of_two_balls (i:=4) (j:=4) hf (by decide) growth growth hn
  omega

theorem eight_seven_literal {n : ℕ} {D : CH.Digraph} (hn : 0<n) (ord : n≤56)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n 8 := by
  by_contra no
  exact eight_free_seven_order (qfree_of_noShort loop no)
    ⟨0,mem_range.mpr hn⟩ (by simpa only [card_range] using ord)
    (fun v hv => Compose.FloorSix.out_card degree (mem_range.mp hv))

#print axioms eight_seven_literal

end LeanCH.BR.DotDegreeSevenQ8
