import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4Multiplicity_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortFrames_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

noncomputable def spillQ4 (D : CH.Digraph) (V B : Finset ℕ) :=
  B.biUnion (fun b => outN D V b \ B)

structure GuardFrame (D : CH.Digraph) (V : Finset ℕ) (c u s a : ℕ)
    : Prop extends FullCycleFrame D V c u s a where
  cA : c∈(ball D V u 1).erase u
  noC : ∀ b∈SecondBank D V u, D b c≠true
  noS : ∀ b∈SecondBank D V u, D b s≠true
  noA : ∀ b∈SecondBank D V u, D b a≠true

theorem q4_shared_marks_of_frames {D : CH.Digraph} {V J : Finset ℕ} {c : ℕ} {s a : ℕ→ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (hc : c∈V)
    (jV : J⊆V) (short : ∀ u∈J, (ball D V u 2).card=14)
    (inj : (↑J : Set ℕ).InjOn (SecondBank D V))
    (fr : ∀ u∈J, GuardFrame D V c u (s u) (a u)) :
    SharedEscortMarks D V (outN D V c) J s a (fun u => spillQ4 D V (SecondBank D V u)) := by
  let X := outN D V c
  have av (u) : (ball D V u 1).erase u⊆V := (erase_subset _ _).trans ball_subset
  have row (u) (hu : u∈J) : X=insert (s u) (SecondBank D V u) := (fr u hu).row
  have bank (u) (hu : u∈J) : SecondBank D V u=X.erase (s u) := by
    have sn : s u∉SecondBank D V u :=
      fun m => (mem_sdiff.mp m).2 (mem_of_mem_erase (fr u hu).sA)
    rw [row u hu,erase_insert sn]
  have head (u) (hu : u∈J) (x) (hx : x∈SecondBank D V u) :
      outN D V x⊆SecondBank D V u∪spillQ4 D V (SecondBank D V u) := by
    intro y hy
    by_cases yB : y∈SecondBank D V u
    · exact mem_union_left _ yB
    · have m : y∈(SecondBank D V u).biUnion (fun z => outN D V z \ SecondBank D V u) :=
        mem_biUnion.mpr ⟨x,hx,mem_sdiff.mpr ⟨hy,yB⟩⟩
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
    exact (fr i hi).noS x xb e
  · exact fun i hi => av i (fr i hi).aA
  · exact fun i hi => (fr i hi).arc
  · intro i hi m
    obtain ⟨b,hb,ha⟩ := mem_biUnion.mp m
    exact (fr i hi).noA b hb (mem_outN.mp (mem_sdiff.mp ha).1).2
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


theorem q4_guarded_frame_gain {D : CH.Digraph} {V : Finset ℕ} {c u s a : ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (hu : u∈V)
    (short : (ball D V u 2).card=14)
    (F : GuardFrame D V c u s a) :
    9+(spillQ4 D V (SecondBank D V u)).card≤(ball D V c 2).card := by
  classical
  let B := SecondBank D V u
  let T := spillQ4 D V B
  let A := (ball D V u 1).erase u
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have b6 : B.card=6 := by
    have st := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    rw [card_B1 hf hu,ho u hu] at st
    change B.card+8=(ball D V u 2).card at st
    omega
  have bs : D c s=true := (mem_outN.mp (F.row.symm ▸ mem_insert_self s B)).2
  have sc : s≠c := by
    intro e
    subst s
    exact hf c 1 (by decide) (by decide) (.step F.cV bs (.refl c))
  let I : Finset ℕ := {c,s,a}
  have iA : I⊆A := by
    intro x hx
    simp only [I,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact F.cA
    · exact F.sA
    · exact F.aA
  have i3 : I.card=3 := by simp [I,Ne.symm sc,Ne.symm F.aC,Ne.symm F.aS]
  have ib : Disjoint I B := disjoint_left.mpr
    (fun _ hi hb => (mem_sdiff.mp hb).2 (mem_of_mem_erase (iA hi)))
  have it : Disjoint (I∪B) T := disjoint_left.mpr (by
    intro x hx ht
    obtain ⟨b,hb,hx'⟩ := mem_biUnion.mp ht
    have sx := (mem_sdiff.mp hx').2
    have ex := (mem_outN.mp (mem_sdiff.mp hx').1).2
    rcases mem_union.mp hx with hi|hB
    · simp only [I,mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl|rfl
      · exact F.noC b hb ex
      · exact F.noS b hb ex
      · exact F.noA b hb ex
    · exact sx hB)
  have ih : I⊆ball D V c 2 := by
    intro x hx
    simp only [I,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact self_mem_ball F.cV
    · exact mem_ball.mpr ⟨av F.sA,1,by decide,.step (av F.sA) bs (.refl _)⟩
    · exact mem_ball.mpr ⟨av F.aA,2,by decide,
        .step (av F.sA) bs (.step (av F.aA) F.arc (.refl _))⟩
  have full (b) (hb : b∈B) : D c b=true :=
    (mem_outN.mp (F.row.symm ▸ mem_insert_of_mem hb)).2
  have bh : B⊆ball D V c 2 := fun b hb =>
    mem_ball.mpr ⟨bv hb,1,by decide,.step (bv hb) (full b hb) (.refl b)⟩
  have th : T⊆ball D V c 2 := by
    intro x hx
    obtain ⟨b,hb,ht⟩ := mem_biUnion.mp hx
    obtain ⟨xv,bt⟩ := mem_outN.mp (mem_sdiff.mp ht).1
    exact mem_ball.mpr ⟨xv,2,by decide,.step (bv hb) (full b hb) (.step xv bt (.refl x))⟩
  have q := card_le_card (union_subset (union_subset ih bh) th)
  rw [card_union_of_disjoint it,card_union_of_disjoint ib,i3,b6] at q
  exact q

theorem q4_spill_at_least_six {D : CH.Digraph} {V B : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (bv : B⊆V) (b6 : B.card=6) :
    6≤(spillQ4 D V B).card := by
  by_contra! small
  let T := spillQ4 D V B
  have sub (b) (hb : b∈B) : outN D V b⊆outN D B b∪T := by
    intro x hx
    by_cases z : x∈B
    · exact mem_union_left _ (mem_outN.mpr ⟨z,(mem_outN.mp hx).2⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨b,hb,mem_sdiff.mpr ⟨hx,z⟩⟩)
  have dg (b) (hb : b∈B) : 2≤(outN D B b).card := by
    have q := (card_le_card (sub b hb)).trans (card_union_le _ _)
    rw [ho b (bv hb)] at q
    change T.card<6 at small
    omega
  have lo := corB (D:=D) (q:=4) (by decide) (hf.mono_set bv) dg
    (card_pos.mp (by omega))
  omega

#print axioms q4_shared_marks_of_frames
#print axioms q4_guarded_frame_gain
#print axioms q4_spill_at_least_six
end LeanCH.BR.DotDegreeSevenLow

