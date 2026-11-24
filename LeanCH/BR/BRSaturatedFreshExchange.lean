import LeanCH.BR.BRWeightedExtremalRectangle

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- A single same-tail or same-head exchange is an instance of the existing
cross-incidence union geometry. No actualness or distinctness assumptions. -/
theorem exchange_cross_incidence_of_shared_endpoint (D : CH.Digraph) (V : Finset ℕ)
    (h w i j : ℕ) (hshare : i=h ∨ j=w) :
    CrossIncidence D (insertArc (eraseArc D h w) i j) V := by
  intro a ha b hb c hc d hd hab hnab hcd hncd
  have hold : a=h ∧ b=w := by
    by_contra hh
    have he : eraseArc D h w a b=true := by simp [eraseArc,hh,hab]
    exact hnab (insertArc_mono _ i j a b he)
  have hnew : c=i ∧ d=j := by
    by_contra hh
    have he : eraseArc D h w c d=true := by simpa only [insertArc,hh,ite_false] using hcd
    exact hncd (eraseArc_sub D h w c d he)
  rcases hold with ⟨rfl,rfl⟩
  rcases hnew with ⟨rfl,rfl⟩
  exact hshare.elim (fun h=>Or.inl h.symm) (fun h=>Or.inr h.symm)

/-- Original saturation excludes shared endpoints for any genuinely fresh safe
one-cut completion. Only the new endpoints need membership hypotheses here;
the deleted edge need not be separately assumed present. -/
theorem saturated_fresh_exchange_endpoints {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (h w i j : ℕ) (hi : i∈V) (hj : j∈V) (hnew : ¬D i j=true)
    (hK : QFree (insertArc (eraseArc D h w) i j) V q) : i≠h ∧ j≠w := by
  have hno : ¬(i=h ∨ j=w) := by
    intro hh
    have hu := qfree_union_cross_incidence hf hK
      (exchange_cross_incidence_of_shared_endpoint D V h w i j hh)
    exact hnew (saturated_qfree_union_sub hq hsat hu i hi j hj (by simp [insertArc]))
  exact not_or.mp hno

end LeanCH.BR.WeightedSD
