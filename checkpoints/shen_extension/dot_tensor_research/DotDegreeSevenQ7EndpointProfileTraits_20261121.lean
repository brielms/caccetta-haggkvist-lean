import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileUnique_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

/-- Any positive-length reachability in the forbidden range separates the endpoints' original rows. -/
theorem distinct_rows_of_reach {D : CH.Digraph} {V : Finset ℕ} {x y q k : ℕ}
    (hf : QFree D V q) (neq : x ≠ y) (hk : k ≤ q) (w : y ∈ ball D V x k) :
    outN D V x ≠ outN D V y := by
  intro eq
  obtain ⟨_,j,hj,w⟩ := mem_ball.mp w
  cases w with
  | refl => exact neq rfl
  | step hb hab wb =>
    have hc :=  (mem_outN.mp (eq ▸ mem_outN.mpr ⟨hb,hab⟩)).2
    exact hf y _ (by omega) (by omega) (.step hb hc wb)

/-- The registered endpoint constraints force two distinct sinks in every first layer. -/
theorem paired_profile_two_sinks {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u ∈ V)
    (b3 : ∀ x ∈ V, (ball D V x 3).card = 22)
    (b4 : ∀ x ∈ V, (ball D V x 4).card = 28) :
    ∃ a ∈ outN D V u, ∃ b ∈ outN D V u, a ≠ b ∧
      (∀ x ∈ outN D V u, ¬ D a x = true) ∧
      (∀ x ∈ outN D V u, ¬ D b x = true) := by
  classical
  have b2 x (hx : x∈V) := paired_profile_two hf ho hx (b3 x hx) (b4 x hx)
  have sub : outN D V u ⊆ V := fun _ hv => (mem_outN.mp hv).1
  have cards := ho u hu
  obtain ⟨a,ha,sa⟩ := exists_sink (hf.mono_set sub)
    (card_pos.mp (by omega)) (by omega)
  by_contra no
  apply paired_profile_no_unique_sink hf ho hu b2 b3 (b4 u hu) ha sa
  intro x hx sx
  by_contra neq
  exact no ⟨a,ha,x,hx,Ne.symm neq,sa,sx⟩

#print axioms distinct_rows_of_reach
#print axioms paired_profile_two_sinks
end LeanCH.BR.DotDegreeSevenQ7


