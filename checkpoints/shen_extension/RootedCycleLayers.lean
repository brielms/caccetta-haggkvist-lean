import checkpoints.shen_extension.ShortestCycleDescent

namespace LeanCH.BR.Closure.RootedCycleLayers
open Finset BRq2 BRq3 BR45 DeficitLevels ShortestCyclePeeling

/-- Absolute positions of vertices on all shortest closed walks based at h. -/
noncomputable def layer (D : CH.Digraph) (V : Finset ℕ) (q h j : ℕ) : Finset ℕ := by
  classical exact V.filter (fun x => Walk D V h x j ∧ Walk D V x h (q+1-j))

/-- On actual labels the q nonroot positions are disjoint. Thus a root
with s labels in every position suffices at the critical order. -/
theorem ledger {D V q h} (free : QFree D V q) (hv : h∈V) :
    (∑ j∈Icc 1 q, (layer D V q h j).card)+1≤V.card := by
  classical
  let L := layer D V q h
  have pair : (Icc 1 q : Set ℕ).PairwiseDisjoint L := by
    intro i hi j hj ne
    apply disjoint_left.mpr
    intro x xi xj
    obtain ⟨_,a,ar⟩ := mem_filter.mp xi
    obtain ⟨_,b,br⟩ := mem_filter.mp xj
    exact ne (aligned free (mem_Icc.mp hi).2 (mem_Icc.mp hj).2 a ar b br)
  have cut : (Icc 1 q).biUnion L⊆V.erase h := by
    intro x hx
    obtain ⟨j,hj,xj⟩ := mem_biUnion.mp hx
    obtain ⟨xv,walk,_⟩ := mem_filter.mp xj
    have range := mem_Icc.mp hj
    exact mem_erase.mpr ⟨fun e => free h j range.1 range.2 (e ▸ walk),xv⟩
  have le := card_le_card cut
  rw [card_biUnion (show (↑(Icc 1 q) : Set ℕ).PairwiseDisjoint L by simpa using pair)] at le
  have total := card_erase_add_one hv
  change (∑j∈Icc 1 q,(L j).card)+1≤V.card
  omega

theorem deficient_position {D V q h s} (free : QFree D V q) (hv : h∈V) (critical : V.card≤q*s) :
    ∃j∈Icc 1 q,(layer D V q h j).card<s := by
  by_contra! all
  have each := sum_le_sum all
  rw [sum_const_nat (fun _ _ => rfl)] at each
  simp only [Nat.card_Icc] at each
  have le := ledger free hv
  have eq : q+1-1=q := by omega
  rw [eq] at each
  omega

#print axioms ledger
#print axioms deficient_position
end LeanCH.BR.Closure.RootedCycleLayers
