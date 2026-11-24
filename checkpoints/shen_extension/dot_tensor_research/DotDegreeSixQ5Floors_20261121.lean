
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixQ5Local_20261121

namespace LeanCH.BR.DotDegreeSix
open Finset BRq2 BRq3 BR45 BRsGen DotDegreeSevenLow
set_option maxHeartbeats 1000000

/-- The first two layers in the exact row host. -/
structure SixPrefix (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) where
  A : Finset ℕ := (ball D V u 1).erase u
  B : Finset ℕ := ball D V u 2 \ ball D V u 1
  T : Finset ℕ := ball D V u 3 \ ball D V u 2
  a_eq : A=(ball D V u 1).erase u
  b_eq : B=ball D V u 2 \ ball D V u 1
  t_eq : T=ball D V u 3 \ ball D V u 2
  aV : A⊆V
  bV : B⊆V
  tV : T⊆V
  ab : Disjoint A B
  at' : Disjoint (A∪B) T
  ca : A.card=6
  first : ∀ a∈A, outN D V a⊆A∪B
  second : ∀ b∈B, outN D V b⊆(A∪B)∪T
  two : (ball D V u 2).card=7+B.card
  three : (ball D V u 3).card=7+B.card+T.card

noncomputable def sixPrefix {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V) (hu : u∈V) : SixPrefix D V u := by
  let A := (ball D V u 1).erase u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  have eq2 : (ball D V u 2).erase u=A∪B := erase_ball_succ_eq_union (k:=1) hu
  have eq3 : (ball D V u 3).erase u=(A∪B)∪T := by rw [erase_ball_succ_eq_union (k:=2) hu,eq2]
  have cn : (ball D V u 1).card=7 := by rw [card_B1 (hf.mono_bound (by decide : 4≤5)) hu,ho u hu]
  have x := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
  have y := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  refine ⟨A,B,T,rfl,rfl,rfl,(erase_subset _ _).trans ball_subset,sdiff_subset.trans ball_subset,
    sdiff_subset.trans ball_subset,?_,?_,?_,?_,?_,?_,?_⟩
  · exact disjoint_left.mpr (fun _ a b => (mem_sdiff.mp b).2 (mem_of_mem_erase a))
  · rw [←eq2]
    exact disjoint_left.mpr (fun _ a b => (mem_sdiff.mp b).2 (mem_of_mem_erase a))
  · change ((ball D V u 1).erase u).card=6
    rw [card_erase_of_mem (self_mem_ball hu),cn]
  · intro a ha v hv
    rw [←eq2]
    exact (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 1+1≤5) (mem_of_mem_erase ha) hv)).1
  · intro b hb v hv
    rw [←eq3]
    exact (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 2+1≤5) (mem_sdiff.mp hb).1 hv)).1
  · change (ball D V u 2).card=7+(ball D V u 2 \ ball D V u 1).card
    omega
  · change (ball D V u 3).card=7+(ball D V u 2 \ ball D V u 1).card+(ball D V u 3 \ ball D V u 2).card
    omega

theorem prefix_keepA {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (ho : OutEq 6 D V) (P : SixPrefix D V u) :
    ∀ a∈P.A, 6≤(outN D (P.A∪P.B) a).card := by
  intro a aa
  have sub : outN D V a⊆outN D (P.A∪P.B) a := fun x hx =>
    mem_outN.mpr ⟨P.first a aa hx,(mem_outN.mp hx).2⟩
  simpa [ho a (P.aV aa)] using card_le_card sub

/-- With exactly five second-layer labels all first rows form a cycle, fully attached to the bank. -/
theorem five_spill {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V) (P : SixPrefix D V u) (cb : P.B.card=5) :
    OutEq 1 D P.A ∧ (∀ a∈P.A, ∀ b∈P.B, D a b=true) ∧ 6≤P.T.card := by
  have m (a) (aa : a∈P.A) : 1≤(outN D P.A a).card := by
    have sum := card_outN_union (D:=D) P.ab a
    have cap := card_le_card (outN_subset (D:=D) (W:=P.B) (y:=a))
    have h := prefix_keepA ho P a aa
    omega
  have cyc : OutEq 1 D P.A := by
    rcases six_acyclic_or_cycle (hf.mono_set P.aV) P.ca with ac | cy
    · obtain ⟨a,aa,stop⟩ := exists_sink ac (card_pos.mp (by rw [P.ca]; decide)) (by rw [P.ca])
      obtain ⟨x,hx⟩ := card_pos.mp (m a aa)
      exact (stop x (mem_outN.mp hx).1 (mem_outN.mp hx).2).elim
    · exact cy
  have full (a) (aa : a∈P.A) (b) (bb : b∈P.B) : D a b=true := by
    have sum := card_outN_union (D:=D) P.ab a
    have h := prefix_keepA ho P a aa
    rw [cyc a aa] at sum
    have eq : outN D P.B a=P.B := eq_of_subset_of_card_le outN_subset (by omega)
    exact (mem_outN.mp (eq.symm ▸ bb)).2
  obtain ⟨b,bb,stop⟩ := exists_sink (hf.mono_set P.bV) (card_pos.mp (by rw [cb]; decide)) (by rw [cb])
  have sub : outN D V b⊆P.T := by
    intro a ha
    rcases mem_union.mp (P.second b bb ha) with ab | ht
    · rcases mem_union.mp ab with aa | ab
      · exact (hf a 2 (by decide) (by decide)
          (.step (P.bV bb) (full a aa b bb) (.step (P.aV aa) (mem_outN.mp ha).2 (.refl _)))).elim
      · exact (stop a ab (mem_outN.mp ha).2).elim
    · exact ht
  exact ⟨cyc,full,by simpa [ho b (P.bV bb)] using card_le_card sub⟩

/-- The first floor from degree two, the second from degree three/four
    plus the matched-layer exclusion. -/
theorem cutoff_five_floor {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V) (hu : u∈V) :
    12≤(ball D V u 2).card ∧ 18≤(ball D V u 3).card := by
  have lo := floor_two12 (by decide : 4≤5) hf (fun v hv => (ho v hv).ge) hu
  refine ⟨lo,?_⟩
  let P := sixPrefix hf ho hu
  have t2 := P.two
  have t3 := P.three
  by_contra! bad
  by_cases b5 : P.B.card=5
  · have j := (five_spill hf ho P b5).2.2
    omega
  have hg (v) (hv : v∈V) : 6≤(outN D V v).card := (ho v hv).ge
  let W := (ball D V u 2).erase u
  have eq : W=P.A∪P.B := by rw [P.a_eq,P.b_eq]; exact erase_ball_succ_eq_union (k:=1) hu
  have wV : W⊆V := (erase_subset _ _).trans ball_subset
  have cw : W.card+1=(ball D V u 2).card := by
    change ((ball D V u 2).erase u).card+1=(ball D V u 2).card
    have h := card_erase_of_mem (self_mem_ball (D:=D) (k:=2) hu)
    omega
  have ne : W.Nonempty := card_pos.mp (by omega)
  have gap := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  change (ball D V u 3 \ ball D V u 2).card+(ball D V u 2).card=(ball D V u 3).card at gap
  by_cases b6 : P.B.card=6
  · by_cases t4 : P.T.card=4
    · have m := minOut_prefix_erase (d:=2) hf hu (by decide : 2+1≤5) hg (by simp only [Nat.reduceAdd]; rw [←P.t_eq]; omega)
      change ∀ v∈W, 2≤(outN D W v).card at m
      rw [eq] at m
      exact six_by_six_not_min_two (hf.mono_set (eq ▸ wV)) P.ca b6 P.ab (prefix_keepA ho P)
        (fun v hv => m v (mem_union_right _ hv))
    · have deg3 := minOut_prefix_erase (d:=3) hf hu (by decide : 2+1≤5) hg (by simp only [Nat.reduceAdd]; rw [←P.t_eq]; omega)
      have bound := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤3) (by decide : 3<6)
        (hf.mono_set wV) deg3 ne
      omega
  · by_cases w16 : W.card=16
    · have deg4 := minOut_prefix_erase (d:=4) hf hu (by decide : 2+1≤5) hg (by simp only [Nat.reduceAdd]; rw [←P.t_eq]; omega)
      have bound := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤4) (by decide : 4<6)
        (hf.mono_set wV) deg4 ne
      omega
    · have deg3 := minOut_prefix_erase (d:=3) hf hu (by decide : 2+1≤5) hg (by simp only [Nat.reduceAdd]; rw [←P.t_eq]; omega)
      have bound := BRq6.lower_order (by decide : 5≤5) (by decide : 2≤3) (by decide : 3<6)
        (hf.mono_set wV) deg3 ne
      omega

#print axioms cutoff_five_floor
end LeanCH.BR.DotDegreeSix


