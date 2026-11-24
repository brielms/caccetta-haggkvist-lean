import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5SpillGeometry_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

noncomputable abbrev SecondBank (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  ball D V u 2 \ ball D V u 1

private theorem ball_mono_set {D : CH.Digraph} {B V : Finset ℕ} {u k : ℕ}
    (sub : B⊆V) : ball D B u k⊆ball D V u k := by
  intro x hx
  obtain ⟨xb,i,hi,w⟩ := mem_ball.mp hx
  exact mem_ball.mpr ⟨sub xb,i,hi,w.mono sub⟩

private theorem arc_mem {D : CH.Digraph} {V : Finset ℕ} {u v k : ℕ}
    (hv : v∈V) (he : D u v=true) (hk : 1≤k) : v∈ball D V u k :=
  mem_ball.mpr ⟨hv,1,hk,.step hv he (.refl v)⟩

private theorem next_mem {D : CH.Digraph} {V : Finset ℕ} {u v w k j : ℕ}
    (hv : v∈ball D V u k) (hw : w∈V) (he : D v w=true) (hk : k+1≤j) :
    w∈ball D V u j := ball_mono_radius hk (ball_step hv hw he)

/-- Each tight bank row supplies one unit, each of four concrete
first-layer companions supplies two. Both bounds are on the same host. -/
theorem tight_bank_charges {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e3 : (ball D V u 3).card=20) :
    let B := SecondBank D V u
    (∀ b∈B, 15≤(ball D V b 2).card ∧ 21≤(ball D V b 3).card) ∧
    ∃ P : Finset ℕ, P⊆V ∧ Disjoint B P ∧ P.card=4 ∧
      (∀ c∈P, ∀ b∈B, D c b=true) ∧
      (∀ c∈P, 15≤(ball D V c 2).card ∧ 22≤(ball D V c 3).card) := by
  have e2 := tight_three_only_tight_two hf ho hu e3
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  let T := ball D V u 3 \ ball D V u 2
  obtain ⟨cb,ct,one,_,full,t,tT,S,s6,sV,ts⟩ := tight_spill_geometry hf ho hu e3
  obtain ⟨_,_,M,P,mA,_,m1,pM,p4,pB,_⟩ := six_bank_first_layer hf ho hu e2
  change B.card=6 at cb
  change T.card=6 at ct
  change M⊆A at mA
  change OutEq 1 D B at one
  change t∈T at tT
  change (∀ b∈B, ∀ t∈T, D b t=true) at full
  change (∀ c∈P, ∀ b∈B, D c b=true) at pB
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have tv : T⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have sv : S⊆V := sV.trans sdiff_subset
  have a2 : A⊆ball D V u 2 :=
    (erase_subset _ _).trans (ball_mono_radius (by decide : 1≤2))
  have b2 : B⊆ball D V u 2 := sdiff_subset
  have avoidBT : Disjoint B T := disjoint_left.mpr
    (fun _ x y => (mem_sdiff.mp y).2 (b2 x))
  have avoidAB : Disjoint A B := disjoint_left.mpr
    (fun _ x y => (mem_sdiff.mp y).2 (mem_of_mem_erase x))
  have avoidA_B_T : Disjoint (A∪B) T := disjoint_left.mpr (by
    intro x h ht
    rcases mem_union.mp h with ha|hb
    · exact (mem_sdiff.mp ht).2 (a2 ha)
    · exact (mem_sdiff.mp ht).2 (b2 hb))
  have avoidABT_S : Disjoint ((A∪B)∪T) S := disjoint_left.mpr (by
    intro x h hs
    apply (mem_sdiff.mp (sV hs)).2
    rcases mem_union.mp h with hab|ht
    · apply ball_mono_radius (by decide : 2≤3)
      exact union_subset a2 b2 hab
    · exact (mem_sdiff.mp ht).1)
  have dr (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  constructor
  · intro b hb
    let I := ball D B b 2
    have ib : I⊆B := ball_subset
    have ie : I⊆ball D V b 2 := ball_mono_set bv
    have i3 : 3≤I.card := ball_one_growth (hf.mono_set bv) (fun v hv => (one v hv).ge) hb 2 (by decide)
    have te : T⊆ball D V b 2 := fun v hv => arc_mem (tv hv) (full b hb v hv) (by decide)
    have se : S⊆ball D V b 2 := fun v hv =>
      next_mem (arc_mem (tv tT) (full b hb t tT) (by decide : 1≤1))
        (sv hv) (ts v hv) (by decide)
    have iT : Disjoint I T := avoidBT.mono_left ib
    have iTS : Disjoint (I∪T) S :=
      avoidABT_S.mono_left (union_subset_union (ib.trans (subset_union_right)) (Subset.refl _))
    have cnt := card_le_card (union_subset (union_subset ie te) se)
    rw [card_union_of_disjoint iTS,card_union_of_disjoint iT,ct,s6] at cnt
    have e : 15≤(ball D V b 2).card := by omega
    have f := floor_three20 hf dr (bv hb)
    by_cases eq : (ball D V b 3).card=20
    · have bad := tight_three_only_tight_two hf ho (bv hb) eq
      omega
    · exact ⟨e,by omega⟩
  · refine ⟨P,pM.trans (mA.trans av),avoidAB.symm.mono_right (pM.trans mA),p4,pB,?_⟩
    intro c hc
    obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by omega)
    have bm : B⊆ball D V c 1 := fun x hx => arc_mem (bv hx) (pB c hc x hx) (by decide)
    have tm : T⊆ball D V c 2 := fun x hx =>
      next_mem (bm hb) (tv hx) (full b hb x hx) (by decide)
    have sm : S⊆ball D V c 3 := fun x hx =>
      next_mem (tm tT) (sv hx) (ts x hx) (by decide)
    have innerGrowth (k) (hk : k+1≤5) :
        k+1≤(ball D M c k).card :=
      ball_one_growth (hf.mono_set (mA.trans av)) (fun v hv => (m1 v hv).ge) (pM hc) k hk
    have cap (k) (hk : k+1≤5) (h2 : 2≤k) :
        k+13≤(ball D V c k).card := by
      let J := ball D M c k
      have ja : J⊆A := ball_subset.trans mA
      have kB : B⊆ball D V c k := bm.trans (ball_mono_radius (by omega))
      have kT : T⊆ball D V c k := tm.trans (ball_mono_radius h2)
      have je : J⊆ball D V c k := ball_mono_set (mA.trans av)
      have len := card_le_card (union_subset (union_subset je kB) kT)
      rw [card_union_of_disjoint (avoidA_B_T.mono_left (union_subset_union ja (Subset.refl _))),
        card_union_of_disjoint (avoidAB.mono_left ja),cb,ct] at len
      have jj : k+1≤J.card := innerGrowth k hk
      omega
    refine ⟨cap 2 (by decide) (by decide),?_⟩
    let J := ball D M c 3
    have ja : J⊆A := ball_subset.trans mA
    have kB : B⊆ball D V c 3 := bm.trans (ball_mono_radius (by decide))
    have kT : T⊆ball D V c 3 := tm.trans (ball_mono_radius (by decide))
    have je : J⊆ball D V c 3 := ball_mono_set (mA.trans av)
    have len := card_le_card (union_subset (union_subset (union_subset je kB) kT) sm)
    rw [card_union_of_disjoint (avoidABT_S.mono_left
          (union_subset_union (union_subset_union ja (Subset.refl _)) (Subset.refl _))),
      card_union_of_disjoint (avoidA_B_T.mono_left (union_subset_union ja (Subset.refl _))),
      card_union_of_disjoint (avoidAB.mono_left ja),cb,ct,s6] at len
    have jj : 4≤J.card := innerGrowth 3 (by decide)
    omega

#print axioms tight_bank_charges
end LeanCH.BR.DotDegreeSevenLow


