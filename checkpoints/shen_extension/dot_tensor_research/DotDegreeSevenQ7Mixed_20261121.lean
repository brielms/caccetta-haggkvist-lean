import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ8_20261121
import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import checkpoints.shen_extension.FifthStrip
import LeanCH.BR.BR96

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45 BRsGen ShenFirstStrip DotTwoPassShellTransport
open DotFourthPrefixQuadratic DotClonePairCompletion
open scoped BigOperators

/-- Mixed-radius reach budget on one actual host. Charge known incomparable
pairs, not a product of two marginal estimates. -/
theorem mixed_incomparable_budget {D : CH.Digraph} {V : Finset ℕ} {q i j r a b : ℕ}
    (hf : QFree D V q) (hi : i≤r) (hj : j≤r) (hs : i+j≤q)
    (loi : ∀ x∈V, a≤(ball D V x i).card)
    (loj : ∀ x∈V, b≤(ball D V x j).card) :
    (orderedIncomparable D V r).card+V.card*a+V.card*b≤V.card*(V.card+1) := by
  classical
  have part (x) (hx : x∈V) :
      (V \ (ball D V x i ∪ reverseBall D V x j)).card+
        ((ball D V x i).card+(reverseBall D V x j).card)=V.card+1 := by
    let F := ball D V x i
    let I := reverseBall D V x j
    have hI : I⊆(V \ F) ∪ {x} := reverseBall_subset_complement hf hs
    have hmeet : F∩I={x} := by
      ext y
      constructor
      · intro m
        obtain ⟨f,g⟩ := mem_inter.mp m
        rcases mem_union.mp (hI g) with h | h
        · exact ((mem_sdiff.mp h).2 f).elim
        · exact h
      · intro m
        obtain rfl := mem_singleton.mp m
        exact mem_inter.mpr ⟨self_mem_ball hx,mem_filter.mpr ⟨hx,self_mem_ball hx⟩⟩
    have hsub : F∪I ⊆ V := union_subset ball_subset (filter_subset _ _)
    have h1 := card_sdiff_add_card_eq_card hsub
    have h2 := card_union_add_card_inter F I
    rw [hmeet,card_singleton] at h2
    change (V \ (F∪I)).card+(F.card+I.card)=V.card+1
    omega
  have mn (x) (hx : x∈V) :
      (V \ (ball D V x r ∪ reverseBall D V x r)) ⊆
      (V \ (ball D V x i ∪ reverseBall D V x j)) := by
    intro y hy
    obtain ⟨yv,yn⟩ := mem_sdiff.mp hy
    refine mem_sdiff.mpr ⟨yv,?_⟩
    intro yb
    apply yn
    rcases mem_union.mp yb with h|h
    · exact mem_union_left _ (ball_mono_radius hi h)
    · exact mem_union_right _ (mem_filter.mpr ⟨yv,ball_mono_radius hj (mem_filter.mp h).2⟩)
  have hc := sum_le_sum (s:=V) (fun x hx => card_le_card (mn x hx))
  rw [←incomparable_card_rows] at hc
  have eq := sum_congr (s₁:=V) rfl part
  rw [sum_add_distrib,sum_add_distrib,sum_reverseBall_eq_sum_ball,Finset.sum_const_nat (fun _ _ => rfl)] at eq
  have h1 := sum_le_sum loi
  have h2 := sum_le_sum loj
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at h1 h2
  omega

private abbrev Deg (D : CH.Digraph) (V : Finset ℕ) :=
  ∀ v∈V, 7≤(outN D V v).card

private abbrev Floor (r b : ℕ) :=
  ∀ {D : CH.Digraph} {V : Finset ℕ}, QFree D V 7 → Deg D V → ∀ v∈V,b≤(ball D V v r).card

theorem floor_two : Floor 2 15 :=
  fun hf hm _ hv => card_ball_two_ge_twice (by decide : 2≤7) hf hm hv

theorem floor_three : Floor 3 22 := by
  intro D V hf hm u hu
  apply third_ball_ge_on_diagonal (by decide : 4≤7) (by decide : 7≤7) ?_ hf hm hu
  intro d lo hi F W ff mm ww
  by_cases h : d=6
  · subst d
    exact BRq6.card_ge_forty_three ff mm ww
  · exact BRq6.lower_order (by decide : 5≤7) lo (by omega) ff mm ww

private theorem floor_four25 : Floor 4 25 := by
  intro D V hf hm u hu
  have h := (ShenFifthStrip.middle_growth (a:=0) hf hm hu).2.2
  simp only [Nat.reduceAdd] at h
  omega

private theorem order_of_floor {D : CH.Digraph} {V : Finset ℕ} {b : ℕ}
    (hf : QFree D V 7) (hm : Deg D V) (hn : V.Nonempty) (fl : Floor 4 b) :
    22+b≤V.card+1 :=
  card_ge_of_two_balls hf (by decide : 3+4≤7) (floor_three hf hm) (fl hf hm) hn

private theorem packet {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hm : Deg D V) (hu : u∈V)
    (ht : (shell D V 3 u).card<7) (b : ℕ) (fl : Floor 4 b) :
    ∃ N, 22+b≤N+1 ∧ N≤((ball D V u 3).erase u).card+
      (layer D V 3 u).card*(shell D V 3 u).card ∧
      10*N+(22+b)*N ≤ N*(N+1)+10*((ball D V u 3).erase u).card+20*(layer D V 3 u).card := by
  let U := (ball D V u 3).erase u
  let S := layer D V 3 u
  let g := fun a => 7-(outN D U a).card
  obtain ⟨hne,hr,hs,hzero,hbudget⟩ := prefix_gap_budget hf hm hu (by decide : 1≤7)
    (k:=2) (by decide) ht
  have huV : U⊆V := (erase_subset _ _).trans ball_subset
  obtain ⟨F,W,f,p,hF,hd,hc,hn,hp,he,hB,hPr⟩ :=
    exists_deficiency_completion_bundles (d:=7) (hf.mono_set huV) hr
  change W.card=U.card+∑ a ∈ U,g a at hc
  change (∑ a ∈ U,g a)+holes D V 3 u ≤ S.card*(shell D V 3 u).card at hbudget
  have eq : ∑ a ∈ U,g a = ∑ a ∈ S,g a := by
    have h0 : ∑ a ∈ U \ S,g a=0 := sum_eq_zero hzero
    have hpart : (∑ a ∈ U \ S,g a)+(∑ a ∈ S,g a)=(∑ a ∈ U,g a) := sum_sdiff hs
    omega
  have bundle := bundle_pairs_le_incomparable (r:=4) (hf.mono_set huV) hp he
    (by decide) (fun x hx => hB x (hs hx)) (fun x hx => hPr x (hs hx))
  change (∑ x ∈ S,g x*(g x+1))≤(orderedIncomparable F W 4).card at bundle
  have mixed := mixed_incomparable_budget hF (by decide : 3≤4) (by decide : 4≤4)
    (by decide : 3+4≤7) (floor_three hF hd) (fl hF hd)
  have t (x : ℕ) : 10*g x≤g x*(g x+1)+20 := by
    by_cases h : g x≤8
    · interval_cases gx : g x <;> omega
    · have hmul := Nat.mul_le_mul_left (g x) (show 10≤g x+1 by omega)
      omega
  have sm := sum_le_sum (s:=S) (fun x _ => t x)
  rw [←Finset.mul_sum, sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at sm
  change ∃ N, 22+b≤N+1 ∧ N≤U.card+S.card*(shell D V 3 u).card ∧
      10*N+(22+b)*N ≤ N*(N+1)+10*U.card+20*S.card
  refine ⟨W.card,order_of_floor hF hd (hn hne) fl,by omega,?_⟩
  rw [add_mul,mul_comm b]
  omega

private theorem dims {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hu : u∈V) :
    (layer D V 3 u).card+(ball D V u 2).card=(ball D V u 3).card ∧
    (shell D V 3 u).card+(ball D V u 3).card=(ball D V u 4).card ∧
    ((ball D V u 3).erase u).card+1=(ball D V u 3).card := by
  have h1 := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  have h2 := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  have h3 := card_erase_of_mem (self_mem_ball (D:=D) (k:=3) hu)
  have hp := card_pos.mpr ⟨u,self_mem_ball (D:=D) (k:=3) hu⟩
  exact ⟨h1,h2,by omega⟩

theorem floor_four26 : Floor 4 26 := by
  intro D V hf hm u hu
  have h2 := floor_two hf hm u hu
  have h3 := floor_three hf hm u hu
  have h4 := floor_four25 hf hm u hu
  by_contra! low
  obtain ⟨dS,dT,dU⟩ := dims (D:=D) hu
  obtain ⟨N,nlo,budget,_⟩ := packet hf hm hu (by omega) 25 floor_four25
  have ar (T S X U N : ℕ) (hn : 46≤N) (hx : 22≤X) (ht : T+X=25)
      (hs : S+15≤X) (hu : U+1=X) (b : N≤U+S*T) : False := by
    have hhi : T≤3 := by omega
    interval_cases T <;> omega
  exact ar _ _ _ _ _ (by omega) h3 (by omega) (by omega) dU budget

theorem floor_four27 : Floor 4 27 := by
  intro D V hf hm u hu
  have h2 := floor_two hf hm u hu
  have h3 := floor_three hf hm u hu
  have h4 := floor_four26 hf hm u hu
  by_contra! low
  obtain ⟨dS,dT,dU⟩ := dims (D:=D) hu
  obtain ⟨N,nlo,budget,collision⟩ := packet hf hm hu (by omega) 26 floor_four26
  have ar (T S X U N : ℕ) (hn : 47≤N) (hx : 22≤X) (ht : T+X=26)
      (hs : S+15≤X) (hu : U+1=X) (b : N≤U+S*T) : X=22 ∧ N≤49 := by
    have hhi : T≤4 := by omega
    interval_cases T <;> omega
  obtain ⟨hx,hN⟩ := ar _ _ _ _ _ (by omega) h3 (by omega) (by omega) dU budget
  have h47 : 47≤N := by omega
  interval_cases N <;> omega

theorem seven_free_min_seven_ge48 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : Deg D V) (hn : V.Nonempty) : 48≤V.card := by
  have h := order_of_floor hf hm hn floor_four27
  omega

#print axioms mixed_incomparable_budget
#print axioms seven_free_min_seven_ge48

/-- A tight radius-four root must contain an actual length-eight closed
walk inside its punctured radius-three prefix. Otherwise the recursive
completion crosses to the already closed cutoff-eight strip. -/
theorem tight_four_native_eight_walk {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hm : Deg D V) (hu : u∈V)
    (tight : (ball D V u 4).card=27) :
    ∃ x, Walk D ((ball D V u 3).erase u) x x 8 := by
  classical
  let U := (ball D V u 3).erase u
  let S := layer D V 3 u
  let T := shell D V 3 u
  have h2 := floor_two hf hm u hu
  have h3 := floor_three hf hm u hu
  obtain ⟨dS,dT,dU⟩ := dims (D:=D) hu
  have ht : T.card<7 := by
    change (shell D V 3 u).card<7
    omega
  obtain ⟨hne,hr,_,_,hbudget⟩ := prefix_gap_budget hf hm hu (by decide : 1≤7)
    (k:=2) (by decide) ht
  change (∑ a ∈ U, (7-(outN D U a).card))+holes D V 3 u ≤ S.card*T.card at hbudget
  by_contra no
  have sub : U⊆V := (erase_subset _ _).trans ball_subset
  have ff : QFree D U 8 := by
    intro x l lo hi w
    by_cases eq : l=8
    · subst l
      exact no ⟨x,w⟩
    · exact (hf.mono_set sub) x l lo (by omega) w
  obtain ⟨F,W,_,_,hF,hd,hc,hn,_,_,_,_⟩ :=
    exists_deficiency_completion_bundles (d:=7) ff hr
  have upper : W.card≤56 := by
    have ar (T S X U N : ℕ) (hx : 22≤X) (ht : T+X=27)
        (hs : S+15≤X) (hu : U+1=X) (b : N≤U+S*T) : N≤56 := by
      have hhi : T≤5 := by omega
      interval_cases T <;> omega
    exact ar T.card S.card _ U.card W.card h3 (by simpa only [T,tight] using dT)
      (by change (layer D V 3 u).card+15≤(ball D V u 3).card; omega)
      dU (by omega)
  exact DotDegreeSevenQ8.eight_free_seven_order hF (hn hne) upper hd

#print axioms tight_four_native_eight_walk

end LeanCH.BR.DotDegreeSevenQ7
