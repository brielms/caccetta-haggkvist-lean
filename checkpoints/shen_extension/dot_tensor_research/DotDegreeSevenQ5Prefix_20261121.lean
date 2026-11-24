import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenLowCutoffs_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators

private theorem full_radius_two {D : CH.Digraph} {U : Finset ℕ} {v : ℕ}
    (hf : QFree D U 5) (hv : v∈U) (hm : ∀ w∈U, 2≤(outN D U w).card)
    (hd : 7≤(outN D U v).card) : 9≤(ball D U v 2).card := by
  by_contra! lt
  have c1 : 8≤(ball D U v 1).card := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤5)) hv]
    omega
  have gap := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=U) (u:=v) (by decide : 1≤2))
  let P := (ball D U v 1).erase v
  have cp : P.card=(ball D U v 1).card-1 := card_erase_of_mem (self_mem_ball hv)
  have fp := hf.mono_set ((erase_subset v (ball D U v 1)).trans ball_subset)
  have dm : ∀ w∈P, 2≤(outN D P w).card :=
    minOut_prefix_erase (d:=2) hf hv (by decide : 1+1≤5) hm (by simp only [Nat.reduceAdd]; omega)
  have k := corB (U:=P) (by decide : 1≤5) fp dm (card_pos.mp (by omega))
  change 2*5+1≤P.card at k
  omega

private theorem full_radius_three {D : CH.Digraph} {U : Finset ℕ} {v : ℕ}
    (hf : QFree D U 5) (hv : v∈U) (hm : ∀ w∈U, 2≤(outN D U w).card)
    (hd : 7≤(outN D U v).card) : 10≤(ball D U v 3).card := by
  by_contra! lt
  have c2 := full_radius_two hf hv hm hd
  have gap := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=U) (u:=v) (by decide : 2≤3))
  let P := (ball D U v 2).erase v
  have cp : P.card=(ball D U v 2).card-1 := card_erase_of_mem (self_mem_ball hv)
  have fp := hf.mono_set ((erase_subset v (ball D U v 2)).trans ball_subset)
  have dm : ∀ w∈P, 2≤(outN D P w).card :=
    minOut_prefix_erase (d:=2) hf hv (by decide : 2+1≤5) hm (by simp only [Nat.reduceAdd]; omega)
  have k := corB (U:=P) (by decide : 1≤5) fp dm (card_pos.mp (by omega))
  change 2*5+1≤P.card at k
  omega

private theorem sum_mixed {D : CH.Digraph} {U : Finset ℕ}
    (hf : QFree D U 5) :
    (∑ v ∈ U, ((ball D U v 2).card+(ball D U v 3).card))≤U.card*(U.card+1) := by
  classical
  have localB (v) (hv : v∈U) : (ball D U v 2).card+(reverseBall D U v 3).card≤U.card+1 := by
    let F := ball D U v 2
    let I := reverseBall D U v 3
    have hI : I⊆(U \ F) ∪ {v} := reverseBall_subset_complement hf (by decide : 2+3≤5)
    have hmeet : F∩I={v} := by
      ext y
      constructor
      · intro m
        obtain ⟨f,g⟩ := mem_inter.mp m
        rcases mem_union.mp (hI g) with h | h
        · exact ((mem_sdiff.mp h).2 f).elim
        · exact h
      · intro m
        obtain rfl := mem_singleton.mp m
        exact mem_inter.mpr ⟨self_mem_ball hv,mem_filter.mpr ⟨hv,self_mem_ball hv⟩⟩
    have hsub : F∪I ⊆ U := union_subset ball_subset (filter_subset _ _)
    have h2 := card_union_add_card_inter F I
    rw [hmeet,card_singleton] at h2
    have h1 := card_le_card hsub
    change F.card+I.card≤U.card+1
    omega
  have agg := sum_le_sum localB
  rw [sum_add_distrib,sum_reverseBall_eq_sum_ball,Finset.sum_const_nat (fun _ _ => rfl)] at agg
  rw [sum_add_distrib]
  exact agg

/-- The 14-label degree-two punctured child cannot carry seven intact rows. -/
private theorem no_prefix_fourteen {D : CH.Digraph} {U A : Finset ℕ}
    (hf : QFree D U 5) (hU : U.card=14) (hA : A.card=7) (av : A⊆U)
    (hm : ∀ v∈U,2≤(outN D U v).card) (high : ∀ v∈A,7≤(outN D U v).card) : False := by
  let val := fun x => (ball D U x 2).card+(ball D U x 3).card
  have a (v) (hv : v∈A) : 19≤val v := by
    have c := full_radius_two hf (av hv) hm (high v hv)
    have d := full_radius_three hf (av hv) hm (high v hv)
    change 19≤(ball D U v 2).card+(ball D U v 3).card
    omega
  have b (v) (hv : v∈U\A) : 12≤val v := by
    have c := ball_growth 5 (by decide) D U hf hm v (mem_sdiff.mp hv).1 2 (by decide)
    have d := ball_growth 5 (by decide) D U hf hm v (mem_sdiff.mp hv).1 3 (by decide)
    change 12≤(ball D U v 2).card+(ball D U v 3).card
    omega
  have a' := sum_le_sum a
  have b' := sum_le_sum b
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at a' b'
  have split := sum_sdiff av (f:=val)
  have ct := card_sdiff_add_card_eq_card av
  have upper : (∑ v∈U,val v)≤U.card*(U.card+1) := sum_mixed hf
  rw [hU] at upper
  omega

/-- In the exact-degree-seven host, an extremal radius-three ball comes
with an extremal radius-two ball at the same root. -/
theorem tight_three_only_tight_two {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (h3 : (ball D V u 3).card=20) : (ball D V u 2).card=14 := by
  have hm : ∀ v∈V,7≤(outN D V v).card := fun v hv => (ho v hv).ge
  have b2 := floor_two14 (by decide) hf hm hu
  have gap := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  let A := (ball D V u 1).erase u
  let U := (ball D V u 2).erase u
  have av : A⊆U := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
  have uv : U⊆V := (erase_subset u _).trans ball_subset
  have ct : U.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball hu)
  have ac : A.card=7 := by
    change ((ball D V u 1).erase u).card=7
    rw [erase_ball_one_eq_outN hf (by decide : 1≤5) hu,ho u hu]
  have ne : U.Nonempty := card_pos.mp (by omega)
  by_contra! not14
  by_cases e : (ball D V u 2).card=15
  · apply no_prefix_fourteen (hf.mono_set uv) (by omega) ac av
    · apply minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤5) hm
      simp only [Nat.reduceAdd]
      omega
    · intro z hz
      exact (hm z (uv (av hz))).trans (card_le_card
        (outN_prefix_erase_root hf hu (by decide : 1+1≤5) (mem_of_mem_erase hz)))
  by_cases e' : (ball D V u 2).card=16
  · have d := minOut_prefix_erase (d:=3) hf hu (by decide : 2+1≤5) hm (by simp only [Nat.reduceAdd]; omega)
    have k := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤3) (by decide : 3<6)
      (hf.mono_set uv) d ne
    change 5*3+1≤U.card at k
    omega
  · have d := minOut_prefix_erase (d:=4) hf hu (by decide : 2+1≤5) hm (by simp only [Nat.reduceAdd]; omega)
    have k := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤4) (by decide : 4<6)
      (hf.mono_set uv) d ne
    change 5*4+1≤U.card at k
    omega

/-- Sum a labelled ledger with one unit for each bank row and one
additional unit for each escort, including their actual intersections. -/
theorem coherent_bank_budget {V L B A : Finset ℕ} {f : ℕ → ℕ} {d : ℕ}
    (hL : L ⊆ V) (hB : B ⊆ V) (hA : A ⊆ V)
    (charge : ∀ v ∈ V,
      34 + (if v ∈ V \ L then 1 else 0) + (if v ∈ B then 1 else 0) +
        (if v ∈ A then 1 else 0) ≤ f v)
    (hsum : (∑ v ∈ V, f v) ≤ 35 * V.card + d) :
    B.card + A.card ≤ L.card + d := by
  have agg := sum_le_sum charge
  have ind (W : Finset ℕ) (hW : W ⊆ V) :
      (∑ v ∈ V, if v ∈ W then (1 : ℕ) else 0) = W.card := by
    simp [sum_ite_mem, inter_eq_right.mpr hW]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib,
    ind _ sdiff_subset, ind _ hB, ind _ hA,
    Finset.sum_const_nat (fun _ _ => rfl)] at agg
  have cr := card_sdiff_add_card_eq_card hL
  omega

#print axioms coherent_bank_budget
#print axioms tight_three_only_tight_two
end LeanCH.BR.DotDegreeSevenLow


