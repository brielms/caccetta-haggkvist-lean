import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactSupport_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

def EndpointLayer1 (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) := outN D V u
noncomputable def EndpointLayer2 (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  ball D V u 2 \ ball D V u 1
noncomputable def EndpointLayer3 (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  ball D V u 3 \ ball D V u 2

theorem exact_endpoint_layer_cards {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (hc : (ball D V u 2).card=15 ∧ (ball D V u 3).card=21) :
    (EndpointLayer1 D V u).card=7 ∧ (EndpointLayer2 D V u).card=7 ∧
    (EndpointLayer3 D V u).card=6 := by
  have first : (ball D V u 1).card=8 := by
    have bf : ball D V u 1 = insert u (outN D V u) := by
      ext x
      rw [mem_ball_one hu,mem_insert]
    rw [bf,card_insert_of_notMem,ho u hu]
    exact fun h => loopfree hf (by decide) hu (mem_outN.mp h).2
  exact ⟨ho u hu, by
    unfold EndpointLayer2
    rw [card_sdiff_of_subset (ball_mono_radius (by decide : 1≤2)),hc.1,first],
    by
      unfold EndpointLayer3
      rw [card_sdiff_of_subset (ball_mono_radius (by decide : 2≤3)),hc.2,hc.1]⟩

theorem exact_endpoint_layer_out {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u∈V) :
    (∀ x∈EndpointLayer1 D V u, outN D V x⊆EndpointLayer1 D V u∪EndpointLayer2 D V u) ∧
    (∀ x∈EndpointLayer2 D V u, outN D V x⊆EndpointLayer1 D V u∪EndpointLayer2 D V u∪
      EndpointLayer3 D V u) := by
  have ret {x y k : ℕ} (hx : x∈ball D V u k) (hxy : y∈outN D V x) (hk : k≤2) :
      y≠u ∧ y∈ball D V u (k+1) := by
    obtain ⟨_,l,hl,w⟩ := mem_ball.mp hx
    obtain ⟨yv,e⟩ := mem_outN.mp hxy
    have w' := w.append (.step yv e (.refl y))
    refine ⟨fun he => ?_,mem_ball.mpr ⟨yv,l+1,by omega,w'⟩⟩
    subst y
    exact hf u (l+1) (by omega) (by omega) w'
  constructor
  · intro x hx y hy
    have h := ret (mem_ball_one hu |>.mpr (Or.inr hx)) hy (by decide)
    by_cases k : y∈ball D V u 1
    · exact mem_union_left _ ((mem_ball_one hu).mp k |>.resolve_left h.1)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨h.2,k⟩)
  · intro x hx y hy
    have h := ret (mem_sdiff.mp hx).1 hy (by decide)
    by_cases k : y∈ball D V u 2
    · apply mem_union_left
      by_cases a : y∈ball D V u 1
      · exact mem_union_left _ ((mem_ball_one hu).mp a |>.resolve_left h.1)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨k,a⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨h.2,k⟩)

theorem exact_endpoint_layer3_parent {D : CH.Digraph} {V : Finset ℕ} {u t : ℕ}
    (hu : u∈V) (ht : t∈EndpointLayer3 D V u) :
    ∃ b∈EndpointLayer2 D V u, D b t=true := by
  obtain ⟨b,hb,e⟩ := ball_succ_pred hu (mem_sdiff.mp ht).1 (mem_sdiff.mp ht).2
  refine ⟨b,mem_sdiff.mpr ⟨hb,fun h => ?_⟩,e⟩
  obtain ⟨_,k,hk,w⟩ := mem_ball.mp h
  have tv := ball_subset (mem_sdiff.mp ht).1
  exact (mem_sdiff.mp ht).2 (mem_ball.mpr ⟨tv,k+1,by omega,w.append (.step tv e (.refl t))⟩)

#print axioms exact_endpoint_layer_cards
#print axioms exact_endpoint_layer_out
#print axioms exact_endpoint_layer3_parent

end LeanCH.BR.DotDegreeSevenLow

