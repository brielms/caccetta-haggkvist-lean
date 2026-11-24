import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ8_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7Mixed_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Growth_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators

private abbrev Deg (D : CH.Digraph) (V : Finset ℕ) :=
  ∀ v∈V, 7≤(outN D V v).card

theorem floor_two14 {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}
    (hq : 4≤q) (hf : QFree D V q) (hm : Deg D V) (hu : u∈V) : 14≤(ball D V u 2).card := by
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  have f := qfree_sub sub hf
  have dm : Deg G V := fun _ hv => (ho _ hv).ge
  have lo : 14≤(ball G V u 2).card := by
    by_contra! low
    have one : (ball G V u 1).card=8 := by
      rw [card_B1 (f.mono_bound hq) hu,ho u hu]
    have lc := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 1≤2))
    let A := (ball G V u 1).erase u
    have a : A.card=7 := by
      change ((ball G V u 1).erase u).card=7
      rw [card_erase_of_mem (self_mem_ball hu),one]
    have adj : ∀ v∈A,2≤(outN G A v).card :=
      minOut_prefix_erase (d:=2) f hu (by omega : 1+1≤q) dm (by
        simp only [Nat.reduceAdd]
        omega)
    have h := corB (U:=A) (by omega : 1≤q) (f.mono_set ((erase_subset u _).trans ball_subset))
      adj (card_pos.mp (by omega))
    change 2*q+1≤A.card at h
    omega
  exact lo.trans (card_le_card (ball_sub sub))

/-- Sum pressure for mixed radii on the same labels. -/
private theorem mixed_sum_upper {D : CH.Digraph} {U : Finset ℕ} {q i j : ℕ}
    (hf : QFree D U q) (hs : i+j≤q) :
    (∑ v ∈ U, ((ball D U v i).card+(ball D U v j).card))≤U.card*(U.card+1) := by
  classical
  have localB (v) (hv : v∈U) : (ball D U v i).card+(reverseBall D U v j).card≤U.card+1 := by
    let F := ball D U v i
    let I := reverseBall D U v j
    have hI : I⊆(U \ F) ∪ {v} := reverseBall_subset_complement hf hs
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

private theorem high_prefix13 {D : CH.Digraph} {U A : Finset ℕ}
    (hf : QFree D U 5) (hU : U.card=13) (hA : A.card=7) (av : A⊆U)
    (hm : ∀ v∈U,2≤(outN D U v).card) (high : ∀ v∈A,7≤(outN D U v).card) : False := by
  let val := fun x => (ball D U x 2).card+(ball D U x 3).card
  have a (v) (hv : v∈A) : 16≤val v := by
    have c : 8≤(ball D U v 1).card := by
      rw [card_B1 (hf.mono_bound (by decide : 4≤5)) (av hv)]
      have := high v hv
      omega
    have h2 := card_le_card (ball_mono_radius (D:=D) (W:=U) (u:=v) (by decide : 1≤2))
    have h3 := card_le_card (ball_mono_radius (D:=D) (W:=U) (u:=v) (by decide : 1≤3))
    change 16≤(ball D U v 2).card+(ball D U v 3).card
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
  have upper : (∑ v∈U,val v)≤U.card*(U.card+1) :=
    mixed_sum_upper hf (by decide : 2+3≤5)
  rw [hU] at upper
  omega

theorem floor_three20 {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hm : Deg D V) (hu : u∈V) : 20≤(ball D V u 3).card := by
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  have f := qfree_sub sub hf
  have dm : Deg G V := fun _ hv => (ho _ hv).ge
  have lo : 20≤(ball G V u 3).card := by
    by_contra! low
    have b2 := floor_two14 (by decide) f dm hu
    have gap := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 2≤3))
    let A := (ball G V u 1).erase u
    let U := (ball G V u 2).erase u
    have av : A⊆U := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
    have uv : U⊆V := (erase_subset u _).trans ball_subset
    have ct : U.card+1=(ball G V u 2).card := by
      change ((ball G V u 2).erase u).card+1=(ball G V u 2).card
      have e := card_erase_of_mem (self_mem_ball (D:=G) (k:=2) hu)
      omega
    have ac : A.card=7 := by
      change ((ball G V u 1).erase u).card=7
      rw [erase_ball_one_eq_outN f (by decide : 1≤5) hu,ho u hu]
    have ne : U.Nonempty := card_pos.mp (by omega)
    by_cases ec : (ball G V u 2).card=14
    · apply high_prefix13 (f.mono_set uv) (by omega) ac av
      · apply minOut_prefix_erase (d:=2) f hu (by decide : 2+1≤5) dm
        simp only [Nat.reduceAdd]
        omega
      · intro z hz
        exact (dm z (uv (av hz))).trans (card_le_card
          (outN_prefix_erase_root f hu (by decide : 1+1≤5) (mem_of_mem_erase hz)))
    by_cases ec' : (ball G V u 2).card=15
    · have deg3 := minOut_prefix_erase (d:=3) f hu (by decide : 2+1≤5) dm
          (by simp only [Nat.reduceAdd]; omega)
      have c := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤3) (by decide : 3<6)
        (f.mono_set uv) deg3 ne
      change 5*3+1≤U.card at c
      omega
    · have deg4 := minOut_prefix_erase (d:=4) f hu (by decide : 2+1≤5) dm
          (by simp only [Nat.reduceAdd]; omega)
      have c := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤4) (by decide : 4<6)
        (f.mono_set uv) deg4 ne
      change 5*4+1≤U.card at c
      omega
  exact lo.trans (card_le_card (ball_sub sub))

theorem four_free_ge27 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (hm : Deg D V) (ne : V.Nonempty) : 27≤V.card := by
  have f (v) (hv : v∈V) : 14≤(ball D V v 2).card := floor_two14 (by decide : 4≤4) hf hm hv
  have h := card_ge_of_two_balls (i:=2) (j:=2) hf (by decide) f f ne
  omega

theorem five_free_ge33 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hm : Deg D V) (ne : V.Nonempty) : 33≤V.card := by
  have h := card_ge_of_two_balls (i:=2) (j:=3) hf (by decide)
    (fun _ hv => floor_two14 (by decide : 4≤5) hf hm hv) (fun _ hv => floor_three20 hf hm hv) ne
  omega

/-- All four pending endpoints are forced onto actual first permissible
cycle witnesses. This is a reduction, not an endpoint exclusion. -/
theorem first_cycle_at_pending {q n : ℕ} {D : CH.Digraph}
    (hq : q=4 ∨ q=5 ∨ q=6 ∨ q=7) (ec : n=7*q)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n 7)
    (miss : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃ xs : List ℕ, CH.IsDirectedCycle D n xs ∧ xs.length=q+1 := by
  have hn : 0<n := by omega
  have ne : (range n).Nonempty := ⟨0,mem_range.mpr hn⟩
  have d : Deg D (range n) := fun _ hv => Compose.FloorSix.out_card hm (mem_range.mp hv)
  have next : CH.HasDirectedCycleAtMost D n (q+1) := by
    by_contra no
    have hf := qfree_of_noShort hl no
    rcases hq with h|h|h|h
    · rw [h] at hf
      have k := five_free_ge33 hf d ne
      rw [card_range] at k
      omega
    · rw [h] at hf
      have k := DotDegreeSevenQ6.six_free_min_seven_ge41 hf d ne
      rw [card_range] at k
      omega
    · rw [h] at hf
      have k := DotDegreeSevenQ7.seven_free_min_seven_ge48 hf d ne
      rw [card_range] at k
      omega
    · rw [h] at hf
      exact DotDegreeSevenQ8.eight_free_seven_order hf ne (by rw [card_range]; omega) d
  obtain ⟨xs,hcycle,hxs⟩ := next
  have lo : q<xs.length := by
    by_contra! less
    exact miss ⟨xs,hcycle,less⟩
  exact ⟨xs,hcycle,by omega⟩

#print axioms four_free_ge27
#print axioms five_free_ge33
#print axioms first_cycle_at_pending
end LeanCH.BR.DotDegreeSevenLow
