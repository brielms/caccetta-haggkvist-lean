import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7Mixed_20261121

namespace LeanCH.BR.DotDegreeSevenQ7GrowthProof
open Finset BRq2 BRq3 BR45 DotTwoPassShellTransport DotFourthPrefixQuadratic
open scoped BigOperators

/-- Remaining supplier for the fourth floor: a short-host edge bound,
not a host-size or radius bound. Scaled by two to avoid division. -/
def FragmentBaseline : Prop :=
  ∀ (D : CH.Digraph) (H : Finset ℕ), QFree D H 7 → (H.card = 21 ∨ H.card = 22) →
    (∀ v∈H, 2 ≤ (outN D H v).card ∧ (outN D H v).card ≤ 7) →
    (∑ v ∈ H, (7-(outN D H v).card)) ≤ 35 →
    2*(∑ v ∈ H, (outN D H v).card) ≤ H.card*(H.card-11)

theorem floor_four_of_baseline (baseline : FragmentBaseline)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 7)
    (ho : OutEq 7 D V) {u : ℕ} (hu : u∈V) :
    28 ≤ (ball D V u 4).card := by
  classical
  let H := (ball D V u 3).erase u
  let A := (ball D V u 2).erase u
  let S := layer D V 3 u
  let T := shell D V 3 u
  let dm := fun v => (outN D H v).card
  have hm (v) (hv : v∈V) : 7 ≤ (outN D V v).card := (ho v hv).ge
  have third := DotDegreeSevenQ7.floor_three hf hm u hu
  have second := DotDegreeSevenQ7.floor_two hf hm u hu
  have hA : A ⊆ H := by
    intro v hv
    obtain ⟨hn,hb⟩ := mem_erase.mp hv
    exact mem_erase.mpr ⟨hn,ball_mono_radius (by decide : 2≤3) hb⟩
  have sub : H ⊆ V := (erase_subset _ _).trans ball_subset
  have ac : A.card+1 = (ball D V u 2).card := by
    have p := card_pos.mpr ⟨u,self_mem_ball (D:=D) (k:=2) hu⟩
    dsimp only [A]
    rw [card_erase_of_mem (self_mem_ball (D:=D) (k:=2) hu)]
    omega
  have hc : H.card+1 = (ball D V u 3).card := by
    have p := card_pos.mpr ⟨u,self_mem_ball (D:=D) (k:=3) hu⟩
    dsimp only [H]
    rw [card_erase_of_mem (self_mem_ball (D:=D) (k:=3) hu)]
    omega
  have st : S.card+(ball D V u 2).card=(ball D V u 3).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 2≤3))
  have tt : T.card+(ball D V u 3).card=(ball D V u 4).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 3≤4))
  by_contra! low
  obtain ⟨hne,_,_,_,budget⟩ := prefix_gap_budget hf hm hu (by decide : 1≤7)
    (k:=2) (by decide) (show T.card<7 by omega)
  change (∑ v ∈ H, (7-dm v))+_ ≤ S.card*T.card at budget
  have hr (d : ℕ) (hd : d+T.card≤7) (v) (hv : v ∈ H) : d ≤ dm v :=
    minOut_prefix_erase (d:=d) hf hu (by decide : 3+1≤7) hm hd v hv
  have hle : H.card≤22 := by
    by_contra! hi
    have b := BRq6.lower_order (q:=7) (d:=4) (by decide) (by decide) (by decide)
      (hf.mono_set sub) (hr 4 (by omega)) hne
    omega
  have mx (v) (hv : v ∈ H) : dm v≤7 :=
    (card_le_card (BR45.outN_mono sub v)).trans (ho v (sub hv)).le
  have exactA (v) (hv : v ∈ A) : dm v=7 := by
    have r := card_le_card (outN_prefix_erase_root hf hu (by decide : 2+1≤7)
      (mem_of_mem_erase hv))
    change _ ≤ dm v at r
    rw [ho v (sub (hA hv))] at r
    exact le_antisymm (mx v (hA hv)) r
  have sumA : (∑ v ∈ A,dm v)=A.card*7 := by
    rw [sum_congr rfl exactA]
    simp
  have split := sum_sdiff hA (f:=dm)
  have num : (H\A).card+A.card=H.card := card_sdiff_add_card_eq_card hA
  have ff := hf.mono_set sub
  have db : (∑ v ∈ H, (7-dm v))≤35 := by
    have ht : T.card≤5 := by omega
    interval_cases e : T.card <;>
      simp only [Nat.mul_zero, Nat.mul_succ] at budget <;> omega
  have edge := baseline D H ff (by omega) (fun v hv => ⟨hr 2 (by omega) v hv,mx v hv⟩) db
  change 2*(∑ v ∈ H, dm v) ≤ H.card*(H.card-11) at edge
  have sumLower (d : ℕ) (hd : d+T.card≤7) : (H\A).card*d ≤ ∑ v ∈ H\A,dm v := by
    simpa using sum_le_sum (s:=H\A) (fun v hv => hr d hd v (mem_sdiff.mp hv).1)
  rcases (by omega : H.card=21 ∨ H.card=22) with e | e
  · rw [e] at edge
    have z := sumLower 2 (by omega)
    omega
  · rw [e] at edge
    have z := sumLower 3 (by omega)
    omega

theorem order_of_baseline (baseline : FragmentBaseline)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 7)
    (ho : OutEq 7 D V) (hn : V.Nonempty) : 49≤V.card := by
  have h := card_ge_of_two_balls hf (by decide : 3+4≤7)
    (DotDegreeSevenQ7.floor_three hf fun v hv => (ho v hv).ge)
    (fun v hv => floor_four_of_baseline baseline hf ho hv) hn
  omega

theorem exact_pair_of_baseline (baseline : FragmentBaseline)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 7)
    (ho : OutEq 7 D V) (hn : V.card=49) {u : ℕ} (hu : u∈V) :
    reverseBall D V u 4 = (V \ ball D V u 3) ∪ {u} :=
  two_balls_boundary_complement hf (by decide : 3+4≤7)
    (DotDegreeSevenQ7.floor_three hf fun v hv => (ho v hv).ge)
    (fun v hv => floor_four_of_baseline baseline hf ho hv) (by omega) hu

#print axioms floor_four_of_baseline
#print axioms order_of_baseline
#print axioms exact_pair_of_baseline

/-- Local fragment supplier: each vertex needs only a mixed-radius
pair bound with its actual outdegree; the global baseline follows. -/
def FragmentLocalGrowth : Prop :=
  ∀ (D : CH.Digraph) (H : Finset ℕ), QFree D H 7 → (H.card = 21 ∨ H.card = 22) →
    (∀ v∈H, 2 ≤ (outN D H v).card ∧ (outN D H v).card ≤ 7) →
    (∑ v ∈ H, (7-(outN D H v).card)) ≤ 35 →
    ∀ v ∈ H, 2*(outN D H v).card+12 ≤ (ball D H v 3).card+(ball D H v 4).card

theorem fragmentBaseline_of_local (growth : FragmentLocalGrowth) : FragmentBaseline := by
  intro D H hf hH hm hdef
  have loc := growth D H hf hH hm hdef
  have h1 := sum_le_sum loc
  rw [sum_add_distrib, ←Finset.mul_sum, Finset.sum_const_nat (fun _ _ => rfl),
      sum_add_distrib] at h1
  have h2 := sum_le_sum (s:=H) (fun v _ =>
    reverseBall_add_ball_le (v:=v) hf (by decide : 3+4≤7))
  rw [sum_add_distrib, sum_reverseBall_eq_sum_ball,
      Finset.sum_const_nat (fun _ _ => rfl)] at h2
  rcases hH with e | e <;> rw [e] at h1 h2 ⊢ <;> omega

#print axioms fragmentBaseline_of_local
/-- The sole geometric fragment supplier used by the floor proof:
a 2- or 3-prefix of at most eleven nonroot labels cannot have a
singleton exit under the 35-deficit budget. -/
def NoSingletonFragment : Prop :=
  ∀ (D : CH.Digraph) (H : Finset ℕ), QFree D H 7 →
    (∀ v∈H, 2 ≤ (outN D H v).card ∧ (outN D H v).card ≤ 7) →
    (∑ v ∈ H, (7-(outN D H v).card)) ≤ 35 →
    ∀ u∈H, ∀ k, 2≤k → k≤3 → (ball D H u k).card≤12 →
      (ball D H u (k+1) \ ball D H u k).card ≠ 1

theorem localGrowth_of_noSingleton (supplier : NoSingletonFragment) : FragmentLocalGrowth := by
  intro D H hf _ hm hdef u hu
  let d := (outN D H u).card
  have dlo : 2 ≤ d := (hm u hu).1
  have dhi : d ≤ 7 := (hm u hu).2
  let X := (ball D H u 1).erase u
  have hx : X.card=d := by
    change ((ball D H u 1).erase u).card=d
    rw [erase_ball_one_eq_outN hf (by decide) hu]
  have hxH : X⊆H := (erase_subset _ _).trans ball_subset
  obtain ⟨v,hv,hsink⟩ := exists_sink (hf.mono_set hxH) (card_pos.mp (by omega)) (by omega)
  have vsub : outN D H v ⊆ ball D H u 2 \ ball D H u 1 := by
    intro x hxout
    obtain ⟨xh,e⟩ := mem_outN.mp hxout
    refine mem_sdiff.mpr ⟨ball_step (mem_of_mem_erase hv) xh e,?_⟩
    intro m
    by_cases r : x=u
    · subst x
      exact no_back_arc hf hu (mem_of_mem_erase hv) (by decide : 1+1≤7) e
    · exact hsink x (mem_erase.mpr ⟨r,m⟩) e
  have b1 : (ball D H u 1).card=d+1 := card_B1 (hf.mono_bound (by decide : 4≤7)) hu
  have b2 : d+3 ≤ (ball D H u 2).card := by
    have h := (hm v (hxH hv)).1.trans (card_le_card vsub)
    have h' := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=H) (u:=u) (by decide : 1≤2))
    omega
  have step (k : ℕ) :
      (ball D H u (k+1) \ ball D H u k).card+(ball D H u k).card =
        (ball D H u (k+1)).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have shell2 (k : ℕ) (kl : 2≤k) (ku : k≤3)
      (cap : (ball D H u k).card≤12) (pos : 2≤(ball D H u k).card) :
      2≤(ball D H u (k+1) \ ball D H u k).card := by
    have ns := supplier D H hf hm hdef u hu k kl ku cap
    by_contra! lo
    have z : (ball D H u (k+1) \ ball D H u k).card=0 := by omega
    have eq := card_erase_of_mem (self_mem_ball (D:=D) (k:=k) hu)
    have sub : (ball D H u k).erase u ⊆ H := (erase_subset _ _).trans ball_subset
    have min : ∀ w∈(ball D H u k).erase u,2≤(outN D ((ball D H u k).erase u) w).card :=
      minOut_prefix_erase hf hu (by omega) (fun v hv => (hm v hv).1) (by omega)
    have b := BRq6.lower_order (q:=7) (d:=2) (by decide) (by decide) (by decide)
      (hf.mono_set sub) min (card_pos.mp (by omega))
    omega
  have b3 : d+5≤(ball D H u 3).card := by
    by_contra! low
    have e := step 2
    simp only [Nat.reduceAdd] at e
    have g := shell2 2 (by decide) (by decide) (by omega) (by omega)
    simp only [Nat.reduceAdd] at g
    omega
  have b4 : d+7≤(ball D H u 4).card ∨ d+6≤(ball D H u 3).card := by
    by_contra! low
    have e := step 3
    simp only [Nat.reduceAdd] at e
    have g := shell2 3 (by decide) (by decide) (by omega) (by omega)
    simp only [Nat.reduceAdd] at g
    omega
  have b34 : (ball D H u 3).card≤(ball D H u 4).card :=
    card_le_card (ball_mono_radius (by decide))
  change 2*d+12 ≤ _
  omega

#print axioms localGrowth_of_noSingleton
end LeanCH.BR.DotDegreeSevenQ7GrowthProof





