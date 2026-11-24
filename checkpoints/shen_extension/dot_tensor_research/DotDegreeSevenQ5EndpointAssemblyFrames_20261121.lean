import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortFrames_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortBudget_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortMultiplicityFull_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

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

private theorem tight_frame_score {D : CH.Digraph} {V M : Finset ℕ} {u c : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e3 : (ball D V u 3).card=20) (mA : M⊆(ball D V u 1).erase u)
    (m1 : OutEq 1 D M) (hc : c∈M) (pB : ∀ b∈SecondBank D V u, D c b=true) :
    37≤mixedScore D V c := by
  unfold mixedScore
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  let T := ball D V u 3 \ ball D V u 2
  obtain ⟨cb,ct,one,_,full,t,tT,S,s6,sV,ts⟩ := tight_spill_geometry hf ho hu e3
  change B.card=6 at cb
  change T.card=6 at ct
  change M⊆A at mA
  change OutEq 1 D B at one
  change t∈T at tT
  change (∀ b∈B, ∀ t∈T, D b t=true) at full
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

  obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by omega)
  have bm : B⊆ball D V c 1 := fun x hx => arc_mem (bv hx) (pB x hx) (by decide)
  have tm : T⊆ball D V c 2 := fun x hx =>
    next_mem (bm hb) (tv hx) (full b hb x hx) (by decide)
  have sm : S⊆ball D V c 3 := fun x hx =>
    next_mem (tm tT) (sv hx) (ts x hx) (by decide)
  have innerGrowth (k) (hk : k+1≤5) :
      k+1≤(ball D M c k).card :=
    ball_one_growth (hf.mono_set (mA.trans av)) (fun v hv => (m1 v hv).ge) hc k hk
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
  have c2 := cap 2 (by decide) (by decide)
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

theorem short_four_scored_frames {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e2 : (ball D V u 2).card=14) :
    ∃ P⊆V, P.card=4 ∧ ∀ c∈P, ∃ s a, FullCycleFrame D V c u s a ∧
        ((ball D V u 3).card=20 → 37≤mixedScore D V c) := by
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  obtain ⟨_,b6,M,P,mA,_,one,pM,p4,full,_⟩ := six_bank_first_layer hf ho hu e2
  have mV : M⊆V := mA.trans ((erase_subset _ _).trans ball_subset)
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  refine ⟨P,pM.trans mV,p4,?_⟩
  intro c hc
  have cM := pM hc
  have cV := mV cM
  obtain ⟨s,sm⟩ := card_pos.mp (by rw [one c cM]; decide : 0<(outN D M c).card)
  obtain ⟨sM,cs⟩ := mem_outN.mp sm
  obtain ⟨a,am⟩ := card_pos.mp (by rw [one s sM]; decide : 0<(outN D M s).card)
  obtain ⟨aM,sa⟩ := mem_outN.mp am
  have aS : a≠s := by
    intro e
    subst a
    exact hf s 1 (by decide) (by decide) (.step (mV sM) sa (.refl s))
  have aC : a≠c := by
    intro e
    subst a
    exact hf c 2 (by decide) (by decide) (.step (mV sM) cs (.step cV sa (.refl c)))
  have sB : s∉B := fun h => (mem_sdiff.mp h).2 (mem_of_mem_erase (mA sM))
  have inc : insert s B⊆outN D V c :=
    insert_subset (mem_outN.mpr ⟨mV sM,cs⟩) (fun b hb => mem_outN.mpr ⟨bv hb,full c hc b hb⟩)
  have row : outN D V c=insert s B :=
    (eq_of_subset_of_card_le inc (by rw [ho c cV,card_insert_of_notMem sB,b6])).symm
  exact ⟨s,a,⟨cV,mA sM,mA aM,aS,aC,row,sa⟩,fun e => tight_frame_score hf ho hu e mA one cM (full c hc)⟩

end LeanCH.BR.DotDegreeSevenLow