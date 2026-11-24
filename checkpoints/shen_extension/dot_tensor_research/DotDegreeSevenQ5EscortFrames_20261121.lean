import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortMultiplicity_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- The two successive labels of an actual full first-cycle row. -/
structure FullCycleFrame (D : CH.Digraph) (V : Finset ℕ) (c u s a : ℕ) : Prop where
  cV : c∈V
  sA : s∈(ball D V u 1).erase u
  aA : a∈(ball D V u 1).erase u
  aS : a≠s
  aC : a≠c
  row : outN D V c=insert s (SecondBank D V u)
  arc : D s a=true

/-- Four full first-cycle rows, each with its actual frame rather than
just a capacity score. -/
theorem short_four_frames {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e2 : (ball D V u 2).card=14) :
    ∃ P⊆V, P.card=4 ∧ ∀ c∈P, ∃ s a, FullCycleFrame D V c u s a := by
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
  exact ⟨s,a,cV,mA sM,mA aM,aS,aC,row,sa⟩

/-- Produce the multiplicity hypotheses from distinct native banks of
short roots, with recorded frame labels. -/
theorem shared_marks_of_frames {D : CH.Digraph} {V J : Finset ℕ} {c : ℕ} {s a : ℕ→ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hc : c∈V)
    (jV : J⊆V) (short : ∀ u∈J, (ball D V u 2).card=14)
    (inj : (↑J : Set ℕ).InjOn (SecondBank D V))
    (fr : ∀ u∈J, FullCycleFrame D V c u (s u) (a u)) :
    SharedEscortMarks D V (outN D V c) J s a (ThirdLayer D V) := by
  let X := outN D V c
  have av (u) : (ball D V u 1).erase u⊆V := (erase_subset _ _).trans ball_subset
  have row (u) (hu : u∈J) : X=insert (s u) (SecondBank D V u) := (fr u hu).row
  have bank (u) (hu : u∈J) : SecondBank D V u=X.erase (s u) := by
    have sn : s u∉SecondBank D V u :=
      fun m => (mem_sdiff.mp m).2 (mem_of_mem_erase (fr u hu).sA)
    rw [row u hu,erase_insert sn]
  have head (u) (hu : u∈J) (x) (hx : x∈SecondBank D V u) :
      outN D V x⊆SecondBank D V u∪ThirdLayer D V u := by
    intro y hy
    by_cases yB : y∈SecondBank D V u
    · exact mem_union_left _ yB
    · have m : y∈(SecondBank D V u).biUnion (fun z => outN D V z \ SecondBank D V u) :=
        mem_biUnion.mpr ⟨x,hx,mem_sdiff.mpr ⟨hy,yB⟩⟩
      rw [←short_spill_set hf ho (jV hu) (short u hu)] at m
      exact mem_union_right _ m
  have outside (u) (hu : u∈J) : a u∉X := by
    intro m
    rw [row u hu] at m
    rcases mem_insert.mp m with e|m
    · exact (fr u hu).aS e
    · exact (mem_sdiff.mp m).2 (mem_of_mem_erase (fr u hu).aA)
  have ins (u) (hu : u∈J) : s u∈X := by rw [row u hu]; exact mem_insert_self ..
  have injS : (↑J : Set ℕ).InjOn s := by
    intro i hi j hj e
    apply inj hi hj
    rw [bank i hi,bank j hj,e]
  refine ⟨outN_subset,ho c hc,ins,injS,?_,?_,outside,?_,?_,?_,?_⟩
  · intro i hi x xX e
    by_cases n : x=s i
    · subst x
      have sv := av i (fr i hi).sA
      exact hf (s i) 1 (by decide) (by decide) (.step sv e (.refl _))
    have xb : x∈SecondBank D V i := by
      rw [bank i hi]
      exact mem_erase.mpr ⟨n,xX⟩
    have h := head i hi x xb (mem_outN.mpr ⟨av i (fr i hi).sA,e⟩)
    rcases mem_union.mp h with q|q
    · exact (mem_sdiff.mp q).2 (mem_of_mem_erase (fr i hi).sA)
    · exact (mem_sdiff.mp q).2
        (ball_mono_radius (by decide : 1≤2) (mem_of_mem_erase (fr i hi).sA))
  · exact fun i hi => av i (fr i hi).aA
  · exact fun i hi => (fr i hi).arc
  · intro i hi m
    exact (mem_sdiff.mp m).2
      (ball_mono_radius (by decide : 1≤2) (mem_of_mem_erase (fr i hi).aA))
  · intro i hi j hj ne
    have sb : s i∈SecondBank D V j := by
      rw [bank j hj]
      exact mem_erase.mpr ⟨fun e => ne (injS hi hj e),ins i hi⟩
    rcases mem_union.mp (head j hj _ sb (mem_outN.mpr ⟨av i (fr i hi).aA,(fr i hi).arc⟩)) with m|m
    · exact (outside i hi (by rw [row j hj]; exact mem_insert_of_mem m)).elim
    · exact m
  · intro i hi x xx ne y hy
    have xb : x∈SecondBank D V i := by
      rw [bank i hi]
      exact mem_erase.mpr ⟨ne,xx⟩
    rcases mem_union.mp (head i hi x xb hy) with h|h
    · exact mem_union_left _ (by change y∈X; rw [row i hi]; exact mem_insert_of_mem h)
    · exact mem_union_right _ h

#print axioms short_four_frames
#print axioms shared_marks_of_frames
end LeanCH.BR.DotDegreeSevenLow

