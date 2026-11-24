import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4GuardPayment_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

def LocalGuardQ4 (D : CH.Digraph) (A : Finset ℕ) (x : ℕ) : Prop :=
  ∃ y∈A, (outN D A y).card=1 ∧ ∃ k≤2, Walk D A x y k

def LocalTwoQ4 (D : CH.Digraph) (A : Finset ℕ) : Prop :=
  ∃ P⊆A, P.card=2 ∧ ∀ c∈P, (outN D A c).card=1 ∧
    ∃ s∈A, ∃ a∈A, D c s=true ∧ D s a=true ∧ LocalGuardQ4 D A s ∧ LocalGuardQ4 D A a

/-- Transport the two protected local frames on first-layer labels
to their actual second bank, preserving each source-label walk. -/
theorem q4_local_selection_to_frames {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V)
    (sel : ∀ A⊆V, A.card=7 → (∀ v∈A, 1≤(outN D A v).card) →
      LocalTwoQ4 D A) :
    ∀ u∈V, (ball D V u 2).card=14 →
      ∃ P⊆V, P.card=2 ∧ ∀ c∈P, ∃ s a, GuardFrame D V c u s a := by
  intro u hu short
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  let U := (ball D V u 2).erase u
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have join : A∪B=U := (erase_ball_succ_eq_union (k:=1) hu).symm
  have a7 : A.card=7 := by
    change ((ball D V u 1).erase u).card=7
    rw [erase_ball_one_eq_outN hf (by decide : 1≤4) hu,ho u hu]
  have b6 : B.card=6 := by
    have st := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    rw [card_B1 hf hu,ho u hu] at st
    change B.card+8=(ball D V u 2).card at st
    omega
  have ge (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  have minA : ∀ v∈A,1≤(outN D A v).card :=
    minOut_prefix_erase (d:=1) hf hu (by decide : 1+1≤4) ge (by change 1+B.card≤7; omega)
  have ab : Disjoint A B := disjoint_left.mpr
    (fun _ x y => (mem_sdiff.mp y).2 (mem_of_mem_erase x))
  have full (x) (hx : x∈A) (one : (outN D A x).card=1) : ∀ b∈B, D x b=true := by
    have keep := (ge x (av hx)).trans
      (card_le_card (outN_prefix_erase_root hf hu (by decide : 1+1≤4) (mem_of_mem_erase hx)))
    change 7≤(outN D U x).card at keep
    have sp := card_outN_union (D:=D) ab x
    rw [join] at sp
    have all : outN D B x=B := eq_of_subset_of_card_le outN_subset (by omega)
    exact fun b hb => (mem_outN.mp (all.symm ▸ hb)).2
  have no (x) (hx : x∈A) (g : LocalGuardQ4 D A x) (b) (hb : b∈B) : D b x≠true := by
    intro bt
    obtain ⟨y,hy,one,k,kk,w⟩ := g
    exact hf b (k+1+1) (by omega) (by omega)
      (.step (av hx) bt ((w.mono av).snoc (bv hb) (full y hy one b hb)))
  obtain ⟨P,pA,p2,prop⟩ := sel A av a7 minA
  refine ⟨P,pA.trans av,p2,?_⟩
  intro c cp
  have ca := pA cp
  obtain ⟨one,s,sa,a,aa,cs,ar,gs,ga⟩ := prop c cp
  have sB : s∉B := fun h => (mem_sdiff.mp h).2 (mem_of_mem_erase sa)
  have row : outN D V c=insert s B := by
    apply (eq_of_subset_of_card_le
      (insert_subset (mem_outN.mpr ⟨av sa,cs⟩)
        (fun b hb => mem_outN.mpr ⟨bv hb,full c ca one b hb⟩)) ?_).symm
    rw [ho c (av ca),card_insert_of_notMem sB,b6]
  have as' : a≠s := by
    intro e
    subst a
    exact hf s 1 (by decide) (by decide) (.step (av sa) ar (.refl s))
  have ac : a≠c := by
    intro e
    subst a
    exact hf c 2 (by decide) (by decide) (.step (av sa) cs (.step (av ca) ar (.refl c)))
  exact ⟨s,a,⟨av ca,sa,aa,as',ac,row,ar⟩,ca,
    no c ca ⟨c,ca,one,0,by decide,.refl c⟩,no s sa gs,no a aa ga⟩

#print axioms q4_local_selection_to_frames
end LeanCH.BR.DotDegreeSevenLow
