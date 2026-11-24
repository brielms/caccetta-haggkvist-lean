import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import LeanCH.BR.BR96

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion
open scoped BigOperators

private theorem high_ball_nine {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (hm : ∀ x∈V,2≤(outN D V x).card) (hu : u∈V)
    (high : 7≤(outN D V u).card) : 9≤(ball D V u 3).card := by
  by_contra! low
  have h1 : 8≤(ball D V u 1).card := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤6)) hu]
    omega
  have h12 := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show 1≤2 by decide))
  have h23 := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show 2≤3 by decide))
  have hs := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show 1≤2 by decide))
  let W := (ball D V u 1).erase u
  have cW : W.card=7 := by
    change ((ball D V u 1).erase u).card=7
    rw [card_erase_of_mem (self_mem_ball hu)]
    omega
  have dW : ∀ x∈W,2≤(outN D W x).card :=
    minOut_prefix_erase hf hu (by decide : 1+1≤6) hm (by simp only [Nat.reduceAdd]; omega)
  have h : 13≤W.card := BRq6.lower_order (by decide : 5≤6) (by decide : 2≤2) (by decide : 2<6)
    (hf.mono_set ((erase_subset u _).trans ball_subset)) dW (card_pos.mp (by omega))
  omega

private theorem many_high_14 {D : CH.Digraph} {U A : Finset ℕ}
    (hf : QFree D U 6) (hu : U.card=14) (ha : A.card=7) (sub : A⊆U)
    (hm : ∀ x∈U,2≤(outN D U x).card) (high : ∀ x∈A,7≤(outN D U x).card) : False := by
  have hA : ∑ x ∈ A, 9 ≤ ∑ x ∈ A,(ball D U x 3).card :=
    sum_le_sum fun x hx => high_ball_nine hf hm (sub hx) (high x hx)
  have outside : ∑ x ∈ U\A, 7 ≤ ∑ x ∈ U\A,(ball D U x 3).card := by
    apply sum_le_sum
    intro x hx
    exact ball_growth 6 (by decide) D U hf hm x (mem_sdiff.mp hx).1 3 (by decide)
  have eq := sum_sdiff sub (f:=fun x => (ball D U x 3).card)
  have cnt := card_sdiff_add_card_eq_card sub
  have bound := incomparable_reach_identity hf (by decide : 3+3≤6)
  simp [ha] at hA
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at outside
  rw [hu] at bound
  omega

private theorem exact_ball_three21 {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (ho : OutEq 7 D V) (hu : u∈V) : 21≤(ball D V u 3).card := by
  classical
  have hm (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  let A := (ball D V u 1).erase u
  let B := ball D V u 2 \ ball D V u 1
  let U := (ball D V u 2).erase u
  let T := ball D V u 3 \ ball D V u 2
  have ae : A=outN D V u := erase_ball_one_eq_outN hf (by decide : 1≤6) hu
  have ac : A.card=7 := by rw [ae,ho u hu]
  have aV : A⊆V := (erase_subset u _).trans ball_subset
  have aU : A⊆U := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
  have dB : B.card+(ball D V u 1).card=(ball D V u 2).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 1≤2))
  have dT : T.card+(ball D V u 2).card=(ball D V u 3).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 2≤3))
  have uV : U⊆V := (erase_subset u _).trans ball_subset
  have ub : U.card+1=(ball D V u 2).card := by
    change ((ball D V u 2).erase u).card+1=(ball D V u 2).card
    have h := card_erase_of_mem (self_mem_ball (D:=D) (k:=2) hu)
    have p := card_pos.mpr ⟨u,self_mem_ball (D:=D) (k:=2) hu⟩
    omega
  have h1 : (ball D V u 1).card=8 := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤6)) hu,ho u hu]
  have neA : A.Nonempty := card_pos.mp (by omega)
  have neU : U.Nonempty := neA.mono aU
  have b6 : 6≤B.card := by
    by_contra! small
    have rank : ∀ v∈A, 2≤(outN D A v).card :=
      minOut_prefix_erase (d:=2) hf hu (by decide : 1+1≤6) hm (by change 2+B.card≤7; omega)
    have lo := BRq6.lower_order (by decide : 5≤6) (by decide : 2≤2) (by decide : 2<6)
      (hf.mono_set aV) rank neA
    omega
  by_contra! low
  have bU : B⊆U := by
    intro x hx
    refine mem_erase.mpr ⟨?_,(mem_sdiff.mp hx).1⟩
    intro ex
    subst x
    exact (mem_sdiff.mp hx).2 (self_mem_ball hu)
  have union : A∪B=U := by
    ext x
    constructor
    · intro h
      rcases mem_union.mp h with h|h
      · exact aU h
      · exact bU h
    · intro h
      by_cases ear : x∈ball D V u 1
      · exact mem_union_left _ (mem_erase.mpr ⟨(mem_erase.mp h).1,ear⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_erase.mp h).2,ear⟩)
  have hiA (x) (hx : x∈A) : 7≤(outN D U x).card := by
    have h := outN_prefix_erase_root hf hu (by decide : 1+1≤6) (mem_of_mem_erase hx)
    exact (hm x (aV hx)).trans (card_le_card h)
  by_cases c14 : (ball D V u 2).card=14
  · have cap : B.card=6 := by omega
    have rankA : ∀ v∈A,1≤(outN D A v).card :=
      minOut_prefix_erase (d:=1) hf hu (by decide : 1+1≤6) hm (by change 1+B.card≤7; omega)
    obtain ⟨p,M,hp,_,sub,hMc,hM⟩ :=
      exists_minimal_cycle_support (by decide : 1≤6) (hf.mono_set aV) rankA neA
    have ca := card_le_card sub
    have eq : M=A := eq_of_subset_of_card_le sub (by omega)
    have dis : Disjoint A B := by
      apply disjoint_left.mpr
      exact fun x hx hy => (mem_sdiff.mp hy).2 (mem_of_mem_erase hx)
    have ab (x) (hx : x∈A) (y) (hy : y∈B) : D x y=true := by
      have sp := card_outN_union (D:=D) dis x
      rw [union] at sp
      have one : (outN D A x).card=1 := by rw [←eq]; exact hM x (eq.symm ▸ hx)
      have all : outN D B x=B := eq_of_subset_of_card_le outN_subset (by
        have h := hiA x hx
        omega)
      exact (mem_outN.mp (all.symm ▸ hy)).2
    have rankU : ∀ v∈U,1≤(outN D U v).card :=
      minOut_prefix_erase (d:=1) hf hu (by decide : 2+1≤6) hm (by change 1+T.card≤7; omega)
    have rankB (x) (hx : x∈B) : 1≤(outN D B x).card := by
      have sub : outN D U x⊆outN D B x := by
        intro y hy
        obtain ⟨hY,arc⟩ := mem_outN.mp hy
        rw [←union] at hY
        rcases mem_union.mp hY with hya | hyb
        · exact (hf x 2 (by decide) (by decide)
            (.step (aV hya) arc (.step (uV (bU hx)) (ab y hya x hx) (.refl x)))).elim
        · exact mem_outN.mpr ⟨hyb,arc⟩
      exact (rankU x (bU hx)).trans (card_le_card sub)
    obtain ⟨x,hx,sink⟩ := exists_sink (hf.mono_set (bU.trans uV)) (card_pos.mp (by omega)) (by omega)
    obtain ⟨y,hy⟩ := card_pos.mp (rankB x hx)
    exact sink y (outN_subset hy) (mem_outN.mp hy).2
  by_cases c15 : (ball D V u 2).card=15
  · exact many_high_14 (hf.mono_set uV) (by omega) ac aU
      (minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤6) hm (by change 2+T.card≤7; omega)) hiA
  by_cases c16 : (ball D V u 2).card=16
  · have rank : ∀ v∈U,3≤(outN D U v).card :=
      minOut_prefix_erase (d:=3) hf hu (by decide : 2+1≤6) hm (by change 3+T.card≤7; omega)
    have h := BRq6.lower_order (by decide : 5≤6) (by decide : 2≤3) (by decide : 3<6)
      (hf.mono_set uV) rank neU
    omega
  · have rank : ∀ v∈U,4≤(outN D U v).card :=
      minOut_prefix_erase (d:=4) hf hu (by decide : 2+1≤6) hm (by change 4+T.card≤7; omega)
    have h := BRq6.lower_order (by decide : 5≤6) (by decide : 2≤4) (by decide : 4<6)
      (hf.mono_set uV) rank neU
    omega

theorem floor_three21 {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hf : QFree D V 6)
    (hm : ∀ v∈V,7≤(outN D V v).card) (hu : u∈V) : 21≤(ball D V u 3).card := by
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  exact (exact_ball_three21 (qfree_sub sub hf) ho hu).trans
    (card_le_card (ball_sub sub))

theorem six_free_min_seven_ge41 {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 6)
    (hm : ∀ v∈V,7≤(outN D V v).card) (hn : V.Nonempty) : 41≤V.card := by
  have h := card_ge_of_two_balls (i:=3) (j:=3) hf (by decide)
    (fun _ hu => floor_three21 hf hm hu) (fun _ hu => floor_three21 hf hm hu) hn
  omega

#print axioms six_free_min_seven_ge41
end LeanCH.BR.DotDegreeSevenQ6
