import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssemblyFrames_20261121
namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

private theorem frame_two {D : CH.Digraph} {V : Finset ℕ} {u c s a : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (short : (ball D V u 2).card=14) (f : FullCycleFrame D V c u s a) :
    9+(ThirdLayer D V u).card≤(ball D V c 2).card := by
  classical
  let B := SecondBank D V u
  let T := ThirdLayer D V u
  let I := insert c (insert s (insert a B))
  obtain ⟨_,b6,_,_,_,_,_,_,_,_,_⟩ := six_bank_first_layer hf ho hu short
  change B.card=6 at b6
  have sv : s∈V := ball_subset (mem_of_mem_erase f.sA)
  have av : a∈V := ball_subset (mem_of_mem_erase f.aA)
  have sa : s∉B := fun h => (mem_sdiff.mp h).2 (mem_of_mem_erase f.sA)
  have aa : a∉B := fun h => (mem_sdiff.mp h).2 (mem_of_mem_erase f.aA)
  have cs : D c s=true := (mem_outN.mp (f.row.symm ▸ mem_insert_self s B)).2
  have cb : c∉B := by
    intro h
    have cc := (mem_outN.mp (f.row.symm ▸ mem_insert_of_mem h)).2
    exact hf c 1 (by decide) (by decide) (.step f.cV cc (.refl c))
  have cS : c≠s := by
    intro e
    subst s
    exact hf c 1 (by decide) (by decide) (.step f.cV cs (.refl c))
  have cb1 : B⊆ball D V c 1 := by
    intro b hb
    obtain ⟨bv,cb⟩ := mem_outN.mp (f.row.symm ▸ mem_insert_of_mem hb)
    exact mem_ball.mpr ⟨bv,1,by decide,.step bv cb (.refl b)⟩
  have hI : I⊆ball D V c 2 := by
    intro x hx
    simp only [I,mem_insert] at hx
    rcases hx with h|h|h|h
    · subst x
      exact mem_ball.mpr ⟨f.cV,0,by decide,.refl c⟩
    · subst x
      exact mem_ball.mpr ⟨sv,1,by decide,.step sv cs (.refl s)⟩
    · subst x
      exact mem_ball.mpr ⟨av,2,by decide,.step sv cs (.step av f.arc (.refl a))⟩
    · exact ball_mono_radius (by decide : 1≤2) (cb1 h)
  have hT : T⊆ball D V c 2 := by
    intro x hx
    change x∈ThirdLayer D V u at hx
    rw [short_spill_set hf ho hu short] at hx
    obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hx
    obtain ⟨xv,bx⟩ := mem_outN.mp (mem_sdiff.mp hx).1
    exact ball_step (cb1 hb) xv bx
  have cT : c∉T := by
    intro h
    change c∈ThirdLayer D V u at h
    rw [short_spill_set hf ho hu short] at h
    obtain ⟨b,hb,hx⟩ := mem_biUnion.mp h
    obtain ⟨_,bc⟩ := mem_outN.mp (mem_sdiff.mp hx).1
    obtain ⟨bv,cb⟩ := mem_outN.mp (f.row.symm ▸ mem_insert_of_mem hb)
    exact hf c 2 (by decide) (by decide) (.step bv cb (.step f.cV bc (.refl c)))
  have dis : Disjoint I T := disjoint_left.mpr (by
    intro x hx ht
    simp only [I,mem_insert] at hx
    rcases hx with h|h|h|h
    · subst x
      exact cT ht
    · subst x
      exact (mem_sdiff.mp ht).2 (ball_mono_radius (by decide : 1≤2) (mem_of_mem_erase f.sA))
    · subst x
      exact (mem_sdiff.mp ht).2 (ball_mono_radius (by decide : 1≤2) (mem_of_mem_erase f.aA))
    · exact (mem_sdiff.mp ht).2 (mem_sdiff.mp h).1)
  have ic : I.card=9 := by
    simp [I,card_insert_of_notMem,cb,sa,aa,cS,f.aS.symm,f.aC.symm,b6]
  have le := card_le_card (union_subset hI hT)
  rw [card_union_of_disjoint dis,ic] at le
  exact le

private theorem spill_card {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} :
    (ThirdLayer D V u).card+(ball D V u 2).card=(ball D V u 3).card :=
  card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 2≤3))

private theorem frame_score_of_spill {D : CH.Digraph} {V : Finset ℕ} {u c s a k : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (short : (ball D V u 2).card=14) (f : FullCycleFrame D V c u s a)
    (hk : 1≤k) (spill : 6+k≤(ThirdLayer D V u).card) :
    36+k≤mixedScore D V c := by
  have c2 := frame_two hf ho hu short f
  have c3 := floor_three20 hf (fun v hv => (ho v hv).ge) f.cV
  by_cases e : (ball D V c 3).card=20
  · have bad := tight_three_only_tight_two hf ho f.cV e
    omega
  · unfold mixedScore
    omega


/-- All short second balls are excluded at endpoint order, charging each
escort according to the number of distinct labelled banks it supports. -/
theorem no_short_at35 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hn : V.card=35) :
    ∀ u∈V, 15≤(ball D V u 2).card := by
  classical
  let B := SecondBank D V
  let L := V.filter (fun u => (ball D V u 2).card=14)
  let K := L.image B
  let roots (b : Finset ℕ) := L.filter (fun u => B u=b)
  have rsub : ∀ b∈K, roots b⊆V := fun _ _ _ m => (mem_filter.mp (mem_filter.mp m).1).1
  have rnon : ∀ b∈K, (roots b).Nonempty := by
    intro b hb
    obtain ⟨u,ul,eq⟩ := mem_image.mp hb
    exact ⟨u,mem_filter.mpr ⟨ul,eq⟩⟩
  let repr (b : Finset ℕ) := if hb : b∈K then (rnon b hb).choose else 0
  have req : ∀ b∈K, repr b∈roots b := by
    intro b hb
    simpa only [repr,dite_eq_left hb] using (rnon b hb).choose_spec
  have rB (b) (hb : b∈K) : B (repr b)=b := (mem_filter.mp (req b hb)).2
  have rV (b) (hb : b∈K) : repr b∈V := rsub b hb (req b hb)
  have rshort (b) (hb : b∈K) : (ball D V (repr b) 2).card=14 :=
    (mem_filter.mp (mem_filter.mp (req b hb)).1).2
  have frames : ∀ b∈K, ∃ P⊆V, P.card=4 ∧ ∀ c∈P, ∃ s a,
      FullCycleFrame D V c (repr b) s a ∧
        ((ball D V (repr b) 3).card=20 → 37≤mixedScore D V c) := by
    intro b hb
    exact short_four_scored_frames hf ho (rV b hb) (rshort b hb)
  let escorts (b : Finset ℕ) := if hb : b∈K then (frames b hb).choose else ∅
  have espect (b) (hb : b∈K) : escorts b⊆V ∧ (escorts b).card=4 ∧
      ∀ c∈escorts b, ∃ s a, FullCycleFrame D V c (repr b) s a ∧
        ((ball D V (repr b) 3).card=20 → 37≤mixedScore D V c) := by
    simpa only [escorts,dite_eq_left hb] using (frames b hb).choose_spec
  have hL : L=K.biUnion roots := by
    ext u
    constructor
    · intro hu
      exact mem_biUnion.mpr ⟨B u,mem_image_of_mem _ hu,mem_filter.mpr ⟨hu,rfl⟩⟩
    · intro h
      obtain ⟨b,_,m⟩ := mem_biUnion.mp h
      exact (mem_filter.mp m).1
  have ed : (↑K : Set (Finset ℕ)).PairwiseDisjoint roots := by
    intro b hb d hd ne
    exact disjoint_left.mpr (fun u ub ud =>
      ne ((mem_filter.mp ub).2.symm.trans (mem_filter.mp ud).2))
  have miss : ∀ b∈K, ∀ u∈roots b, (roots b).erase u⊆missingMixed D V u := by
    intro b hb u ub v vb
    obtain ⟨ne,vb⟩ := mem_erase.mp vb
    have uu := mem_filter.mp (mem_filter.mp ub).1
    have vv := mem_filter.mp (mem_filter.mp vb).1
    have eq := (mem_filter.mp ub).2.trans (mem_filter.mp vb).2.symm
    have a := same_short_bank_no_three hf ho uu.1 vv.1 ne.symm uu.2 vv.2 eq
    have d := same_short_bank_no_three hf ho vv.1 uu.1 ne vv.2 uu.2 eq.symm
    apply mem_sdiff.mpr ⟨vv.1,?_⟩
    intro m
    rcases mem_union.mp m with m|m
    · exact a (ball_mono_radius (by decide : 2≤3) m)
    · exact d (mem_filter.mp m).2
  have pay : ∀ c∈V, 36+(K.filter (fun b => c∈escorts b)).card ≤
      mixedScore D V c+(if c∈L then 2 else 0) := by
    intro c hc
    let I := K.filter (fun b => c∈escorts b)
    let J := I.image repr
    have jeq : J.card=I.card := card_image_of_injOn (by
      intro b hb d hd eq
      exact (rB b (mem_filter.mp hb).1).symm.trans
        ((congrArg B eq).trans (rB d (mem_filter.mp hd).1)))
    have native (u) (hu : u∈J) : u∈V ∧ (ball D V u 2).card=14 ∧
        ∃ s a, FullCycleFrame D V c u s a ∧
          ((ball D V u 3).card=20 → 37≤mixedScore D V c) := by
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hu
      obtain ⟨bk,ec⟩ := mem_filter.mp hb
      exact ⟨rV b bk,rshort b bk,(espect b bk).2.2 c ec⟩
    have inj : (↑J : Set ℕ).InjOn B := by
      intro u hu v hv eq
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hu
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hv
      rw [rB b (mem_filter.mp hb).1,rB d (mem_filter.mp hd).1] at eq
      rw [eq]
    have pick (u : ℕ) : ∃ s a, u∈J → FullCycleFrame D V c u s a := by
      by_cases hu : u∈J
      · obtain ⟨s,a,fr,_⟩ := (native u hu).2.2
        exact ⟨s,a,fun _ => fr⟩
      · exact ⟨0,0,fun h => (hu h).elim⟩
    choose s a fr using pick
    have marks := shared_marks_of_frames hf ho hc (fun u hu => (native u hu).1)
      (fun u hu => (native u hu).2.1) inj fr
    have ub : J.card≤7 := by
      calc
        J.card = (J.image s).card := (card_image_of_injOn marks.sInj).symm
        _ ≤ (outN D V c).card := card_le_card (by
          intro x hx
          obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
          exact marks.sMem u hu)
        _ = 7 := ho c hc
    change 36+I.card≤_
    rw [←jeq]
    by_cases j0 : J.card=0
    · have two := floor_two14 (by decide : 4≤5) hf (fun v hv => (ho v hv).ge) hc
      have three := floor_three20 hf (fun v hv => (ho v hv).ge) hc
      by_cases cl : c∈L
      · simp only [if_pos cl,j0,mixedScore]; omega
      · have cne : (ball D V c 2).card≠14 := fun e => cl (mem_filter.mpr ⟨hc,e⟩)
        by_cases t : (ball D V c 3).card=20
        · exact (cne (tight_three_only_tight_two hf ho hc t)).elim
        · simp only [if_neg cl,j0,mixedScore]; omega
    · have score : 36+J.card≤mixedScore D V c := by
        by_cases j1 : J.card=1
        · obtain ⟨u,hu⟩ := card_pos.mp (show 0<J.card by omega)
          obtain ⟨uv,us,s,a,f,tight⟩ := native u hu
          rw [j1]
          by_cases e : (ball D V u 3).card=20
          · exact tight e
          · have floor := floor_three20 hf (fun v hv => (ho v hv).ge) uv
            have sp := spill_card (D:=D) (V:=V) (u:=u)
            exact frame_score_of_spill hf ho uv us f (by decide : 1≤1) (by omega)
        · by_cases j7 : J.card=7
          · rw [j7]
            exact (sharedEscort_all_seven_score hf ho hc marks j7).1
          · obtain ⟨u,hu⟩ := card_pos.mp (show 0<J.card by omega)
            have sp := sharedEscort_thick_spill hf ho marks (by omega) (by omega) u hu
            exact frame_score_of_spill hf ho (native u hu).1 (native u hu).2.1 (fr u hu)
              (by omega) (by omega)
      exact score.trans (Nat.le_add_right _ _)
  have dead := no_short_banks_of_escort_certificate hf hn L roots escorts hL rsub rnon ed
    (fun b hb => (espect b hb).1) (fun b hb => (espect b hb).2.1) miss pay
  intro u hu
  have lower := floor_two14 (by decide : 4≤5) hf (fun v hv => (ho v hv).ge) hu
  by_contra! lt
  have ul : u∈L := mem_filter.mpr ⟨hu,by omega⟩
  have key : B u∈K := mem_image_of_mem _ ul
  rw [dead] at key
  exact notMem_empty _ key

#print axioms no_short_at35
end LeanCH.BR.DotDegreeSevenLow
