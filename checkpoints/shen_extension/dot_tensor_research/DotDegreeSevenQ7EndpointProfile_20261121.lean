import LeanCH.BR.BRsubTripleLayers
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7Mixed_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion
open scoped BigOperators

private theorem high_three_eleven {D : CH.Digraph} {U : Finset ℕ} {x : ℕ}
    (hf : QFree D U 7) (hm : ∀ v∈U, 2 ≤ (outN D U v).card) (hx : x∈U)
    (high : (outN D U x).card=7) : 11≤(ball D U x 3).card := by
  have hx1 : (ball D U x 1).card=8 := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hx, high]
  have h12 := card_le_card (ball_mono_radius (D:=D) (W:=U) (u:=x) (by decide : 1≤2))
  have h23 := card_le_card (ball_mono_radius (D:=D) (W:=U) (u:=x) (by decide : 2≤3))
  have h2 : 10≤(ball D U x 2).card := by
    by_contra! low
    let W := (ball D U x 1).erase x
    have hs := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=U) (u:=x) (by decide : 1≤2))
    have rank : ∀ v∈W,1≤(outN D W v).card :=
      minOut_prefix_erase (d:=1) hf hx (by decide : 1+1≤7) hm (by simp only [Nat.reduceAdd]; omega)
    
    have e : W.card = (ball D U x 1).card - 1 := card_erase_of_mem (self_mem_ball hx)
    obtain ⟨a,ha,hsink⟩ := exists_sink (hf.mono_set (show W ⊆ U from (erase_subset x _).trans ball_subset))
      (card_pos.mp (by omega) : W.Nonempty) (by omega)
    obtain ⟨b,hb⟩ := card_pos.mp (show 0<(outN D W a).card from rank a ha)
    exact hsink b (mem_filter.mp hb).1 (mem_filter.mp hb).2
  by_contra! low
  let W := (ball D U x 2).erase x
  have hs := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=U) (u:=x) (by decide : 2≤3))
  have rank : ∀ v∈W,2≤(outN D W v).card :=
    minOut_prefix_erase (d:=2) hf hx (by decide : 2+1≤7) hm (by simp only [Nat.reduceAdd]; omega)
  
  have e : W.card = (ball D U x 2).card - 1 := card_erase_of_mem (self_mem_ball hx)
  have lower : 15 ≤ W.card := BRq6.lower_order (by decide : 5≤7) (by decide : 2≤2) (by decide : 2<6)
    (hf.mono_set (show W ⊆ U from (erase_subset x _).trans ball_subset)) rank (card_pos.mp (by omega) : W.Nonempty)
  omega

private theorem many_high_sixteen {D : CH.Digraph} {U A : Finset ℕ}
    (hf : QFree D U 7) (hu : U.card=16) (ha : A.card=7) (sub : A⊆U)
    (hm : ∀ x∈U,2≤(outN D U x).card) (high : ∀ x∈A,(outN D U x).card=7) : False := by
  have hA : ∑ x ∈ A, 11 ≤ ∑ x ∈ A,(ball D U x 3).card :=
    sum_le_sum fun x hx => high_three_eleven hf hm (sub hx) (high x hx)
  have outside : ∑ x ∈ U\A, 7 ≤ ∑ x ∈ U\A,(ball D U x 3).card := by
    apply sum_le_sum
    intro x hx
    exact ball_growth 7 (by decide) D U hf hm x (mem_sdiff.mp hx).1 3 (by decide)
  have eq := sum_sdiff sub (f:=fun x => (ball D U x 3).card)
  have cnt := card_sdiff_add_card_eq_card sub
  have bound := incomparable_reach_identity hf (by decide : 3+3≤7)
  simp [ha] at hA
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at outside
  rw [hu] at bound
  omega

theorem tight_three_cap_two {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u∈V)
    (eq : (ball D V u 3).card=22) : (ball D V u 2).card≤16 := by
  have hm (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  let A := (ball D V u 1).erase u
  let U := (ball D V u 2).erase u
  let T := ball D V u 3 \ ball D V u 2
  have ac : A.card=7 := by
    change ((ball D V u 1).erase u).card=7
    rw [erase_ball_one_eq_outN hf (by decide : 1≤7) hu,ho u hu]
  have aV : A⊆V := (erase_subset u _).trans ball_subset
  have aU : A⊆U := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
  have uV : U⊆V := (erase_subset u _).trans ball_subset
  have dT : T.card+(ball D V u 2).card=(ball D V u 3).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 2≤3))
  have ub : U.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball hu)
  have neU : U.Nonempty := card_pos.mp (by have h := card_le_card aU; omega)
  have hiA (x) (hx : x∈A) : (outN D U x).card=7 := by
    have h := outN_prefix_erase_root hf hu (by decide : 1+1≤7) (mem_of_mem_erase hx)
    have l : (outN D V x).card ≤ (outN D U x).card := card_le_card h
    have r := card_le_card (show outN D U x ⊆ outN D V x from fun z hz => mem_outN.mpr ⟨uV (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩)
    rw [ho x (aV hx)] at l r
    omega
  by_contra! low
  by_cases c17 : (ball D V u 2).card=17
  · exact many_high_sixteen (hf.mono_set uV) (by omega) ac aU
      (minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤7) hm (by change 2+T.card≤7; omega)) hiA
  · have rank : ∀ v∈U,3≤(outN D U v).card :=
      minOut_prefix_erase (d:=3) hf hu (by decide : 2+1≤7) hm (by change 3+T.card≤7; omega)
    have h := BRq6.lower_order (by decide : 5≤7) (by decide : 2≤3) (by decide : 3<6)
      (hf.mono_set uV) rank neU
    omega

/-- The exact radius-three/four pairing forces the second ball's unique size.
The short profile is excluded by the existing arbitrary-degree equal-layer
return theorem, instantiated one cutoff below the native source. -/
theorem paired_profile_two {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u∈V)
    (three : (ball D V u 3).card=22) (four : (ball D V u 4).card=28) :
    (ball D V u 2).card=16 := by
  have hm (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  have lo := floor_two hf hm u hu
  have hi := tight_three_cap_two hf ho hu three
  by_contra neq
  have two : (ball D V u 2).card=15 := by omega
  have one : (ball D V u 1).card=8 := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hu, ho u hu]
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  let W := ball D V u 4 \ ball D V u 3
  have nB : B.card=7 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    omega
  have nT : T.card=7 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at h
    omega
  have nW : W.card=6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
    change W.card+(ball D V u 3).card=(ball D V u 4).card at h
    omega
  have noback : ∀ z ∈ T, ∀ v ∈ ball D V u 2, ¬ D z v=true :=
    BRsub.equal_triple_layers_no_back (s:=7) (by decide)
      (hf.mono_bound (by decide : 7-1≤7)) hu hm (ho u hu) nB nT (by change W.card ≤ 7-1; omega)
  have tV : T⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  obtain ⟨z,hz,hsink⟩ := exists_sink (hf.mono_set tV)
    (card_pos.mp (by omega) : T.Nonempty) (by omega)
  have sub : outN D V z ⊆ W := by
    intro v hv
    obtain ⟨hvV,hzv⟩ := mem_outN.mp hv
    refine mem_sdiff.mpr ⟨ball_step (mem_sdiff.mp hz).1 hvV hzv,?_⟩
    intro v3
    by_cases v2 : v∈ball D V u 2
    · exact noback z hz v v2 hzv
    · exact hsink v (mem_sdiff.mpr ⟨v3,v2⟩) hzv
  have h := card_le_card sub
  rw [ho z (tV hz), nW] at h
  omega

#print axioms tight_three_cap_two
#print axioms paired_profile_two
end LeanCH.BR.DotDegreeSevenQ7



