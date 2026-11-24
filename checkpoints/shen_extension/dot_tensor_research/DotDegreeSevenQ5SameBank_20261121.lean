import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Charges_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

noncomputable def ThirdLayer (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  ball D V u 3 \ ball D V u 2

/-- All heads of a short second bank outside the bank are exactly its
third layer, on the original labels. -/
theorem short_spill_set {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e2 : (ball D V u 2).card=14) :
    ThirdLayer D V u =
      (SecondBank D V u).biUnion (fun b => outN D V b \ SecondBank D V u) := by
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  let T := ThirdLayer D V u
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have tv : T⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,reach⟩ := six_bank_first_layer hf ho hu e2
  change (∀ a∈A, ∃ p∈A, ∃ i≤2, Walk D V a p i ∧ ∀ b∈B, D p b=true) at reach
  have noBA (b) (hb : b∈B) (a) (ha : a∈A) : D b a≠true := by
    intro ba
    obtain ⟨p,_,i,ib,walk,pb⟩ := reach a ha
    exact hf b (i+1+1) (by omega) (by omega)
      (Walk.step (av ha) ba (walk.snoc (bv hb) (pb b hb)))
  have keep (b) (hb : b∈B) : outN D V b ⊆ B∪T := by
    intro x hx
    obtain ⟨xv,bx⟩ := mem_outN.mp hx
    have edge : x∈ball D V u 3 := ball_step (mem_sdiff.mp hb).1 xv bx
    by_cases x2 : x∈ball D V u 2
    · have x1 : x∉ball D V u 1 := by
        intro hx1
        by_cases eq : x=u
        · subst x
          exact no_back_arc hf hu (mem_sdiff.mp hb).1 (by decide : 2+1≤5) bx
        · exact noBA b hb x (mem_erase.mpr ⟨eq,hx1⟩) bx
      exact mem_union_left _ (mem_sdiff.mpr ⟨x2,x1⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨edge,x2⟩)
  change T = B.biUnion (fun b => outN D V b \ B)
  ext x
  constructor
  · intro xT
    have ⟨_,k,k3,w⟩ := mem_ball.mp (mem_sdiff.mp xT).1
    have ek : k=3 := by
      by_contra n
      exact (mem_sdiff.mp xT).2 (mem_ball.mpr ⟨tv xT,k,by omega,w⟩)
    subst k
    obtain ⟨b,p,_,e⟩ := w.unsnoc
    have bV : b∈V := (p.end_mem_or).elim (fun h => h.symm ▸ hu) id
    have bb : b∈B := by
      refine mem_sdiff.mpr ⟨mem_ball.mpr ⟨bV,2,by decide,p⟩,?_⟩
      intro h
      exact (mem_sdiff.mp xT).2 (ball_step h (tv xT) e)
    exact mem_biUnion.mpr ⟨b,bb,mem_sdiff.mpr
      ⟨mem_outN.mpr ⟨tv xT,e⟩,fun xb => (mem_sdiff.mp xT).2 (mem_sdiff.mp xb).1⟩⟩
  · intro hx
    obtain ⟨b,bB,hx⟩ := mem_biUnion.mp hx
    exact (mem_union.mp (keep b bB (mem_sdiff.mp hx).1)).resolve_left (mem_sdiff.mp hx).2

/-- Two distinct short roots with the same six-label bank fail reach
in both directions through radius three (apply this theorem twice). -/
theorem same_short_bank_no_three {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V) (hv : v∈V) (ne : u≠v)
    (us : (ball D V u 2).card=14) (vs : (ball D V v 2).card=14)
    (eq : SecondBank D V u=SecondBank D V v) :
    v∉ball D V u 3 := by
  have no1 : v∉ball D V u 1 := by
    intro m
    have uv : D u v=true := (mem_outN.mp
      ((erase_ball_one_eq_outN hf (by decide : 1≤5) hu) ▸
        (mem_erase.mpr ⟨ne.symm,m⟩ : v∈(ball D V u 1).erase u))).2
    have sub : outN D V v ⊆ outN D V u := by
      intro x hx
      obtain ⟨xv,vx⟩ := mem_outN.mp hx
      have x2 : x∈ball D V u 2 := ball_step m xv vx
      have x1 : x∈ball D V u 1 := by
        by_contra n
        have xb : x∈SecondBank D V u := mem_sdiff.mpr ⟨x2,n⟩
        rw [eq] at xb
        exact (mem_sdiff.mp xb).2 ((mem_ball_one hv).mpr (Or.inr hx))
      have xx : x≠u := by
        intro e
        subst x
        exact hf u 2 (by decide) (by decide)
          (.step hv uv (.step hu vx (.refl u)))
      rw [←erase_ball_one_eq_outN hf (by decide : 1≤5) hu]
      exact mem_erase.mpr ⟨xx,x1⟩
    have equal : outN D V v=outN D V u :=
      eq_of_subset_of_card_le sub (by rw [ho u hu,ho v hv])
    have self : v∈outN D V v := equal ▸ mem_outN.mpr ⟨hv,uv⟩
    exact hf v 1 (by decide) (by decide) (.step hv (mem_outN.mp self).2 (.refl v))
  have no2 : v∉ball D V u 2 := by
    intro vv
    have b : v∈SecondBank D V u := mem_sdiff.mpr ⟨vv,no1⟩
    rw [eq] at b
    exact (mem_sdiff.mp b).2 (self_mem_ball hv)
  have eT : ThirdLayer D V u=ThirdLayer D V v := by
    rw [short_spill_set hf ho hu us,short_spill_set hf ho hv vs,eq]
  intro m
  have vT : v∈ThirdLayer D V u := mem_sdiff.mpr ⟨m,no2⟩
  rw [eT] at vT
  exact (mem_sdiff.mp vT).2 (self_mem_ball hv)

#print axioms short_spill_set
#print axioms same_short_bank_no_three
end LeanCH.BR.DotDegreeSevenLow

