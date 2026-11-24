import checkpoints.shen_extension.GlobalFamilyDual

namespace LeanCH.BR.Closure.SparseParentDual
open Finset BRq2 BRq3 BR45 WeightedSD

theorem selected_parents {D : CH.Digraph} {V : Finset ℕ} {F : MarkedCyclePeeling.Family} {b} :
    inN (FirstPacketBarrier.graph D F) V b⊆inN D V b := by
  intro j js
  obtain ⟨jv,jb⟩ := mem_inN.mp js
  obtain ⟨C,hc⟩ := FirstPacketBarrier.active.mp jb
  exact mem_inN.mpr ⟨jv,(MarkedCyclePeeling.mem_col.mp hc).2.2.2⟩

/-- A labelled column in a subgraph pays through the root and its original parents.
The coefficient uses the actual number of parents in the subgraph. -/
theorem localized {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {F : MarkedCyclePeeling.Family}
    {b : ℕ} {π : ℕ→ℚ} {c : ℚ}
    (col : WeightedSD.col q (FirstPacketBarrier.graph D F) V π b=c) :
    let S := inN (FirstPacketBarrier.graph D F) V b
    ∃i∈insert b S, i∈insert b (inN D V b) ∧
      c≤(1+(q:ℚ)*(S.card:ℚ))*π i := by
  classical
  intro S
  have sub : S⊆inN D V b := selected_parents
  obtain ⟨i,hi,top⟩ := (insert b S).exists_max_image π (insert_nonempty b S)
  have bound := sum_le_sum (s:=S) (fun j h=>top j (mem_insert_of_mem h))
  have total : mass S π≤S.card*π i := by simpa [mass,nsmul_eq_mul] using bound
  have eq : π b+(q:ℚ)*mass S π=c := by
    simpa only [WeightedSD.col,inW,mass,S,inN,sum_filter] using col
  refine ⟨i,hi,(insert_subset_insert b sub) hi,?_⟩
  linarith only [eq,top b (mem_insert_self b S),mul_le_mul_of_nonneg_left total (Nat.cast_nonneg q)]

/-- Fewer than q original parents force a heavy reverse coordinate among those
specific labels, even when the column weight lives on the selected subgraph. -/
theorem obstruction {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {F : MarkedCyclePeeling.Family}
    {b : ℕ} {π : ℕ→ℚ} {c : ℚ} (hq : 2≤q) (high : 1<c)
    (pos : ∀j∈V,0≤π j) (bv : b∈V)
    (col : WeightedSD.col q (FirstPacketBarrier.graph D F) V π b=c)
    (few : (inN D V b).card<q) :
    ∃i∈insert b (inN D V b), 1<(q:ℚ)^2*π i := by
  classical
  let S := inN (FirstPacketBarrier.graph D F) V b
  obtain ⟨i,si,di,lo⟩ := localized col
  have sub : S⊆inN D V b := selected_parents
  have cnt := card_le_card sub
  have k : (S.card:ℚ)+1≤q := by exact_mod_cast (show S.card+1≤q by omega)
  have qt : (2:ℚ)≤q := by exact_mod_cast hq
  have coeff : 1+(q:ℚ)*S.card≤(q:ℚ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left k (Nat.cast_nonneg q),qt]
  have iv : i∈V := (insert_subset bv (filter_subset _ _)) di
  exact ⟨i,di,high.trans_le (lo.trans (mul_le_mul_of_nonneg_right coeff (pos i iv)))⟩

/-- At a two-parent root, one of the three named vertices carries a large
reverse coordinate. Both inequalities hold at the same vertex. -/
theorem pair {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {F : MarkedCyclePeeling.Family}
    {b p y : ℕ} {π : ℕ→ℚ} {c : ℚ} (hq : 3≤q) (high : 1<c)
    (pos : ∀j∈V,0≤π j) (bv : b∈V)
    (col : WeightedSD.col q (FirstPacketBarrier.graph D F) V π b=c)
    (parents : inN D V b={p,y}) :
    ∃i∈({b,p,y}:Finset ℕ), c≤(1+2*(q:ℚ))*π i ∧ 1<(q:ℚ)^2*π i := by
  obtain ⟨i,_,di,low⟩ := localized col
  have iv : i∈V := (insert_subset bv (filter_subset _ _)) di
  have sub : inN (FirstPacketBarrier.graph D F) V b ⊆ inN D V b := selected_parents
  have count := card_le_card sub
  rw [parents] at count di
  have bound := card_insert_le p ({y}:Finset ℕ)
  simp only [card_singleton] at bound
  have k : ((inN (FirstPacketBarrier.graph D F) V b).card:ℚ)≤2 := by exact_mod_cast count.trans bound
  have two : 1+2*(q:ℚ)≤(q:ℚ)^2 := by
    have qt : (3:ℚ)≤q := by exact_mod_cast hq
    nlinarith only [mul_nonneg (sub_nonneg.mpr qt) (show 0≤(q:ℚ) by positivity),qt]
  have L : c≤(1+2*(q:ℚ))*π i := low.trans (mul_le_mul_of_nonneg_right (by
    linarith only [mul_le_mul_of_nonneg_left k (Nat.cast_nonneg q)]) (pos i iv))
  exact ⟨i,di,L,high.trans_le (L.trans (mul_le_mul_of_nonneg_right two (pos i iv)))⟩

#print axioms pair
#print axioms localized
#print axioms obstruction
end LeanCH.BR.Closure.SparseParentDual
