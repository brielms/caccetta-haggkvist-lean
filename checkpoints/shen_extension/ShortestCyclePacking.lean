import checkpoints.shen_extension.CutoffDegreeRank

namespace LeanCH.BR.Closure.ShortestCyclePacking
open Finset BRq2 BRq3 BR45 DeficitLevels CutoffDegreeRank

/-- In a q-free graph these supports of size q+1 with one internal
successor per label are single induced directed cycles. -/
def Packing (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) (P : Finset (Finset ℕ)) : Prop :=
  (∀M∈P, M⊆V ∧ M.card=q+1 ∧ OutEq 1 D M) ∧ (P : Set (Finset ℕ)).PairwiseDisjoint id

/-- Greedy exhaustion on actual vertex labels. If the union of the
circuits were too small, crossing to cutoff q+1 would supply another
disjoint original circuit. -/
theorem packed {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card) :
    ∃P, Packing O.G O.V q P ∧ (q+1)*s < O.V.card+q*((q+1)*P.card) := by
  classical
  let families := O.V.powerset.powerset.filter (Packing O.G O.V q)
  have zero : ∅∈families := by simp [families,Packing]
  obtain ⟨P,ok,maximal⟩ := families.exists_max_image Finset.card ⟨∅,zero⟩
  obtain ⟨carrier,valid⟩ := mem_filter.mp ok
  refine ⟨P,valid,?_⟩
  let T := P.biUnion id
  have tv : T⊆O.V := by
    intro x hx
    obtain ⟨M,hm,xm⟩ := mem_biUnion.mp hx
    exact (valid.1 M hm).1 xm
  have count : T.card=(q+1)*P.card := by
    rw [show T=P.biUnion id from rfl,card_biUnion valid.2]
    change ∑ M∈P,M.card=(q+1)*P.card
    rw [sum_const_nat (fun M hm => (valid.1 M hm).2.1),Nat.mul_comm]
  by_contra! few
  have budget : q*T.card+O.V.card≤(q+1)*s := by rw [count,Nat.add_comm]; exact few
  obtain ⟨M,sub,sz,one⟩ := avoid_set O hb rank tv budget
  have dis {C} (hc : C∈P) : Disjoint M C := disjoint_left.mpr (fun x xm xc =>
    (mem_sdiff.mp (sub xm)).2 (mem_biUnion.mpr ⟨C,hc,xc⟩))
  have fresh : M∉P := by
    intro hm
    obtain ⟨x,xm⟩ := card_pos.mp (show 0<M.card by omega)
    exact disjoint_left.mp (dis hm) xm xm
  have more : insert M P∈families := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset (mem_powerset.mpr (sub.trans sdiff_subset))
      (mem_powerset.mp carrier)),?_,?_⟩
    · intro C hc
      rcases mem_insert.mp hc with rfl|hc
      · exact ⟨sub.trans sdiff_subset,sz,one⟩
      · exact valid.1 C hc
    · intro U hu C hc ne
      by_cases um : U=M
      · subst U
        exact dis ((mem_insert.mp hc).resolve_left ne.symm)
      have up := (mem_insert.mp hu).resolve_left um
      by_cases cm : C=M
      · subst C; exact (dis up).symm
      exact valid.2 up ((mem_insert.mp hc).resolve_left cm) ne
  have bigger := maximal _ more
  simp [card_insert_of_notMem fresh] at bigger

#print axioms packed
end LeanCH.BR.Closure.ShortestCyclePacking
