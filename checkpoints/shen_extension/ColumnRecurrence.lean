import checkpoints.shen_extension.DistinctUnmatchedRows

namespace LeanCH.BR.Closure.ColumnBlockerEscape
open Finset BRq2 BRq3 BR45

noncomputable def unmatchedSet (D : CH.Digraph) (V : Finset ℕ) : Finset ℕ := by
  classical exact V.filter (Unmatched D V)

/-- Every arc of this relation links an incoming column to a matching row. -/
def Matches (D : CH.Digraph) (V : Finset ℕ) (a b : ℕ) : Prop :=
  outN D V b=inN D V a

/-- Any indefinitely renewable family of matching columns, including every
periodic orbit, receives arcs from unmatched columns on the original graph.
Three renewals prove the same lower bound for every period. -/
theorem recurrence {D V s X} (safe : QFree D V 3) (deg : ∀v∈V, s≤(outN D V v).card)
    (pos : 0<s) (order : V.card≤3*s) (sub : X⊆V)
    (renew : ∀a∈X, ∃ b∈X, Matches D V a b) :
    (∀a∈X, 3*s+1≤V.card+(inN D (unmatchedSet D V) a).card) ∧
    (3*s+1-V.card)*X.card ≤ ∑ z∈unmatchedSet D V, (outN D X z).card := by
  classical
  have per (a) (ax : a∈X) : 3*s+1≤V.card+(inN D (unmatchedSet D V) a).card := by
    obtain ⟨b,bx,ab⟩ := renew a ax
    obtain ⟨c,cx,bc⟩ := renew b bx
    obtain ⟨e,ex,ce⟩ := renew c cx
    obtain ⟨first,second⟩ := local_counts safe deg pos (sub ax) (sub bx) (sub cx) ab bc
      (show s≤(inN D V c).card by rw [←show outN D V e=inN D V c from ce]; exact deg e (sub ex))
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<(inN D V a ∩ inN D V c).card by omega)
    obtain ⟨count,un⟩ := second x hx
    have inc : inN D V a ∩ outN D V x ⊆ inN D (unmatchedSet D V) a := by
      intro z hz
      obtain ⟨zv,za⟩ := mem_inN.mp (mem_inter.mp hz).1
      exact mem_inN.mpr ⟨mem_filter.mpr ⟨zv,un z hz⟩,za⟩
    exact count.trans (Nat.add_le_add_left (card_le_card inc) _)
  refine ⟨per,?_⟩
  have lower (a) (ax:a∈X) : 3*s+1-V.card≤(inN D (unmatchedSet D V) a).card := by
    have := per a ax; omega
  have total := sum_le_sum lower
  rw [sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at total
  apply total.trans_eq
  simp only [inN,outN,card_filter]
  exact sum_comm

/-- Within two applications of the matching relation, all vertices are
accounted for by unmatched vertices and their original outgoing arcs. -/
theorem two_step_cover {D V s} (safe : QFree D V 3) (deg : ∀v∈V, s≤(outN D V v).card)
    (pos : 0<s) (order : V.card≤3*s) {a} (av : a∈V) :
    a∈unmatchedSet D V ∨ (∃ z∈unmatchedSet D V, D z a=true) ∨
    (∃ z∈unmatchedSet D V, Matches D V a z) ∨
    ∃ b∈V, ∃ z∈unmatchedSet D V, Matches D V a b ∧ Matches D V b z := by
  classical
  have next (v) (vv : v∈V) (no : v∉unmatchedSet D V) : ∃ w∈V, Matches D V v w := by
    by_contra none
    exact no (mem_filter.mpr ⟨vv,fun w wv hit => none ⟨w,wv,hit⟩⟩)
  by_cases au : a∈unmatchedSet D V
  · exact Or.inl au
  obtain ⟨b,bv,ab⟩ := next a av au
  by_cases bu : b∈unmatchedSet D V
  · exact Or.inr (Or.inr (Or.inl ⟨b,bu,ab⟩))
  obtain ⟨c,cv,bc⟩ := next b bv bu
  by_cases cu : c∈unmatchedSet D V
  · exact Or.inr (Or.inr (Or.inr ⟨b,bv,c,cu,ab,bc⟩))
  obtain ⟨e,ev,ce⟩ := next c cv cu
  obtain ⟨_,_,z,hz,un⟩ := local_unmatched safe deg pos order av bv cv ab bc
    (show s≤(inN D V c).card by rw [←show outN D V e=inN D V c from ce]; exact deg e ev)
  have za := mem_inN.mp (mem_inter.mp hz).1
  exact Or.inr (Or.inl ⟨z,mem_filter.mpr ⟨za.1,un⟩,za.2⟩)

#print axioms recurrence
#print axioms two_step_cover
end LeanCH.BR.Closure.ColumnBlockerEscape
