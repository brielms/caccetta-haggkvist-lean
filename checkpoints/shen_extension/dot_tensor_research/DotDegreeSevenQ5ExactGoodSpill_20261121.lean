import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactLayers_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- The foreign seventh label cannot have a short return from any
member of a three-step cycle ball about one of its heads. -/
theorem exact_cycle_good_bank {D : CH.Digraph} {V C : Finset ℕ} {z p : ℕ}
    (hf : QFree D V 5) (cV : C⊆V) (zV : z∈V)
    (c6 : C.card=6) (one : OutEq 1 D C) (hp : p∈C) (e : D z p=true) :
    let G := C.filter (fun x => D x z≠true)
    G.Nonempty ∧ (∀ c∈C, ∃ g∈G, ∃ k≤2, Walk D V c g k) ∧ p∈G := by
  classical
  let G := C.filter (fun x => D x z≠true)
  change G.Nonempty ∧ (∀ c∈C, ∃ g∈G, ∃ k≤2, Walk D V c g k) ∧ p∈G
  have incl : ball D C p 3⊆G := by
    intro g hg
    obtain ⟨gc,k,hk,w⟩ := mem_ball.mp hg
    apply mem_filter.mpr
    refine ⟨gc,fun e' => ?_⟩
    have ww : Walk D V z z (k+2) :=
      (Walk.step (cV hp) e (w.mono cV)).append (.step zV e' (.refl z))
    exact hf z (k+2) (by omega) (by omega) ww
  have four : 4≤G.card := (ball_one_growth (hf.mono_set cV) (fun x hx => (one x hx).ge)
    hp 3 (by decide)).trans (card_le_card incl)
  have pG := incl (self_mem_ball hp)
  refine ⟨⟨p,pG⟩,?_,pG⟩
  intro c hc
  have low := ball_one_growth (hf.mono_set cV) (fun x hx => (one x hx).ge) hc 2 (by decide)
  by_contra hn
  push Not at hn
  have disj : Disjoint (ball D C c 2) G := disjoint_left.mpr (by
    intro g h hg
    obtain ⟨_,j,hj,w⟩ := mem_ball.mp h
    exact hn g hg j hj (w.mono cV))
  have sub : ball D C c 2∪G⊆C := union_subset ball_subset (filter_subset _ _)
  have bound := card_le_card sub
  rw [card_union_of_disjoint disj,c6] at bound
  omega

/-- The final propagation uses a full row and the absence of all
spill-to-bank arcs. No assumption on the spill's own rows is needed. -/
theorem exact_cycle_spill_excluded {D : CH.Digraph} {V C T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card≤35)
    (cap : ∀ v∈V, (ball D V v 2).card≤15) (cV : C⊆V) (tV : T⊆V)
    (one : OutEq 1 D C) (t6 : T.card=6) (ct : Disjoint C T)
    (no : ∀ t∈T, ∀ c∈C, D t c≠true) {b : ℕ} (hb : b∈C)
    (full : ∀ t∈T, D b t=true) : False := by
  classical
  let S := T.biUnion (fun x => outN D V x \ T)
  have sv : S⊆V := by
    intro a ha
    obtain ⟨_,_,hm⟩ := mem_biUnion.mp ha
    exact outN_subset (mem_sdiff.mp hm).1
  have ts : Disjoint T S := disjoint_left.mpr (by
    intro a at' as'
    obtain ⟨_,_,hm⟩ := mem_biUnion.mp as'
    exact (mem_sdiff.mp hm).2 at')
  have cs : Disjoint C S := disjoint_left.mpr (by
    intro a ac as'
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp as'
    exact no t ht a ac (mem_outN.mp (mem_sdiff.mp hm).1).2)
  let I := ball D C b 2
  have ib : I⊆C := ball_subset
  have iv : I⊆ball D V b 2 := by
    intro x hx
    obtain ⟨xc,i,hi,w⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨cV xc,i,hi,w.mono cV⟩
  have i3 : 3≤I.card := ball_one_growth (hf.mono_set cV)
    (fun v hv => (one v hv).ge) hb 2 (by decide)
  have tv : T⊆ball D V b 2 := fun t ht =>
    mem_ball.mpr ⟨tV ht,1,by decide,.step (tV ht) (full t ht) (.refl t)⟩
  have sb : S⊆ball D V b 2 := by
    intro x hx
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp hx
    obtain ⟨xv,e⟩ := mem_outN.mp (mem_sdiff.mp hm).1
    exact mem_ball.mpr ⟨xv,2,by decide,
      .step (tV ht) (full t ht) (.step xv e (.refl x))⟩
  have mx := card_le_card (union_subset (union_subset iv tv) sb)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨cs.mono_left ib,ts⟩),
    card_union_of_disjoint (ct.mono_left ib),t6] at mx
  have s6 : S.card≤6 := by have k := cap b (cV hb); omega
  apply exact_endpoint_no_supported_bank hf ho n cap tV sv ts
    (card_pos.mp (by omega)) t6.le s6
  intro t ht x hx
  by_cases h : x∈T
  · exact mem_union_left _ h
  · exact mem_union_right _ (mem_biUnion.mpr ⟨t,ht,mem_sdiff.mpr ⟨hx,h⟩⟩)

#print axioms exact_cycle_good_bank
#print axioms exact_cycle_spill_excluded

end LeanCH.BR.DotDegreeSevenLow

