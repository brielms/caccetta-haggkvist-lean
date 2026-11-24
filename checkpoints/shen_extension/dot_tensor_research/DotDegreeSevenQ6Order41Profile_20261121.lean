import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Growth_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenLowCutoffs_20261121

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


private theorem high_ball_ten {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (hm : ∀ x∈V,2≤(outN D V x).card) (hu : u∈V)
    (high : 7≤(outN D V u).card) : 10≤(ball D V u 3).card := by
  by_contra! low
  have nine := high_ball_nine hf hm hu high
  have h1 : 8≤(ball D V u 1).card := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤6)) hu]
    omega
  have h12 := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
  have h23 := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  have h2 : 9≤(ball D V u 2).card := by
    by_contra! lo
    let W := (ball D V u 1).erase u
    have hs := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    have rank := minOut_prefix_erase (d:=2) hf hu (by decide : 1+1≤6) hm
      (by simp only [Nat.reduceAdd]; omega)
    have e := card_erase_of_mem (self_mem_ball (D:=D) (k:=1) hu)
    change W.card=(ball D V u 1).card-1 at e
    have bound := BRq6.lower_order (by decide : 5≤6) (by decide : 2≤2) (by decide : 2<6)
      (hf.mono_set ((erase_subset u _).trans ball_subset)) rank
      (card_pos.mp (by omega) : W.Nonempty)
    change 13≤W.card at bound
    omega
  let U := (ball D V u 2).erase u
  have hs := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  have rank := minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤6) hm
    (by simp only [Nat.reduceAdd]; omega)
  have e := card_erase_of_mem (self_mem_ball (D:=D) (k:=2) hu)
  change U.card=(ball D V u 2).card-1 at e
  have bound := BRq6.lower_order (by decide : 5≤6) (by decide : 2≤2) (by decide : 2<6)
    (hf.mono_set ((erase_subset u _).trans ball_subset)) rank
    (card_pos.mp (by omega) : U.Nonempty)
  change 13≤U.card at bound
  omega

private theorem many_high_15 {D : CH.Digraph} {U A : Finset ℕ}
    (hf : QFree D U 6) (hu : U.card=15) (ha : A.card=7) (sub : A⊆U)
    (hm : ∀ x∈U,2≤(outN D U x).card) (high : ∀ x∈A,7≤(outN D U x).card) : False := by
  have hA : ∑ x ∈ A, 10 ≤ ∑ x ∈ A,(ball D U x 3).card :=
    sum_le_sum fun x hx => high_ball_ten hf hm (sub hx) (high x hx)
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

/-- Any minimal three-ball has second-ball size at most fifteen.
This is also usable at order 42, without an equality assumption. -/
theorem tight_three_cap_two {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (ho : OutEq 7 D V) (hu : u∈V)
    (eq : (ball D V u 3).card=21) : (ball D V u 2).card≤15 := by
  have hm (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  let A := (ball D V u 1).erase u
  let U := (ball D V u 2).erase u
  let T := ball D V u 3 \ ball D V u 2
  have ac : A.card=7 := by
    change ((ball D V u 1).erase u).card=7
    rw [erase_ball_one_eq_outN hf (by decide : 1≤6) hu,ho u hu]
  have aV : A⊆V := (erase_subset u _).trans ball_subset
  have aU : A⊆U := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
  have uV : U⊆V := (erase_subset u _).trans ball_subset
  have dT : T.card+(ball D V u 2).card=(ball D V u 3).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 2≤3))
  have ub : U.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball hu)
  have neU : U.Nonempty := card_pos.mp (by have h := card_le_card aU; omega)
  have hiA (x) (hx : x∈A) : 7≤(outN D U x).card := by
    have h := outN_prefix_erase_root hf hu (by decide : 1+1≤6) (mem_of_mem_erase hx)
    exact (hm x (aV hx)).trans (card_le_card h)
  by_contra! low
  by_cases c16 : (ball D V u 2).card=16
  · exact many_high_15 (hf.mono_set uV) (by omega) ac aU
      (minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤6) hm (by change 2+T.card≤7; omega)) hiA
  by_cases c17 : (ball D V u 2).card=17
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

theorem order41_three_complement {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (ho : OutEq 7 D V) (n : V.card=41) :
    ∀ v∈V, (ball D V v 3).card=21 ∧
      reverseBall D V v 3 = (V \ ball D V v 3) ∪ {v} := by
  have lo (v) (hv : v∈V) := floor_three21 hf (fun x hx => (ho x hx).ge) hv
  intro v hv
  exact ⟨(two_balls_boundary_cards hf (by decide : 3+3≤6) lo lo (by omega) v hv).1,
    two_balls_boundary_complement hf (by decide : 3+3≤6) lo lo (by omega) hv⟩

#print axioms tight_three_cap_two
#print axioms order41_three_complement
end LeanCH.BR.DotDegreeSevenQ6


