import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Prefix_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- At the order-35 endpoint with no radius-two shortfall, reach is
completely paired, not merely bounded in total. Both equalities refer to
the same graph and all its actual labels. -/
theorem saturated_mixed_endpoint {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) :
    ∀ v∈V,
      reverseBall D V v 3 = (V \ ball D V v 2) ∪ {v} ∧
      reverseBall D V v 2 = (V \ ball D V v 3) ∪ {v} := by
  have hm : ∀ v∈V, 7≤(outN D V v).card := fun _ hv => (ho _ hv).ge
  have lo (v) (hv : v∈V) : 21≤(ball D V v 3).card := by
    have b := floor_three20 hf hm hv
    by_contra! h
    have e : (ball D V v 3).card=20 := by omega
    have wrong := tight_three_only_tight_two hf ho hv e
    have a := noLow v hv
    omega
  intro v hv
  exact ⟨two_balls_boundary_complement hf (by decide : 2+3≤5) noLow lo (by omega) hv,
    two_balls_boundary_complement hf (by decide : 3+2≤5) lo noLow (by omega) hv⟩

/-- Identical rows cannot occur inside the exact labelled endpoint seam. -/
theorem saturated_mixed_endpoint_no_twins {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) {u v : ℕ}
    (hu : u∈V) (hv : v∈V) (ne : u≠v)
    (same : outN D V u=outN D V v) : False := by
  have no (a b : ℕ) (neq : a≠b) (j : ℕ) (hj : j≤3)
      (eq : outN D V a = outN D V b) (w : Walk D V a b j) : False := by
    cases j with
    | zero => cases w; exact neq rfl
    | succ k =>
      cases w with
      | step xV e tail =>
        have xN : _∈outN D V a := mem_outN.mpr ⟨xV,e⟩
        rw [eq] at xN
        exact hf b (k+1) (by omega) (by omega) (.step xV (mem_outN.mp xN).2 tail)
  by_cases h : v∈ball D V u 2
  · obtain ⟨_,j,hj,w⟩ := mem_ball.mp h
    exact no u v ne j (by omega) same w
  · have q : v∈(V \ ball D V u 2) ∪ {u} :=
      mem_union_left _ (mem_sdiff.mpr ⟨hv,h⟩)
    rw [←(saturated_mixed_endpoint hf ho n noLow u hu).1] at q
    obtain ⟨_,j,hj,w⟩ := mem_ball.mp (mem_filter.mp q).2
    exact no v u ne.symm j hj same.symm w

#print axioms saturated_mixed_endpoint
#print axioms saturated_mixed_endpoint_no_twins
end LeanCH.BR.DotDegreeSevenLow

