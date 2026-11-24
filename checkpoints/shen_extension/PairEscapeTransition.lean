import checkpoints.shen_extension.MinimumPairEscape

namespace LeanCH.BR.Closure.PairEscapeTransition
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights MandatoryTwoStep
open MandatoryExcursion PuncturedDistance

/-- If the collecting row v still belongs to a shortest cycle through h,
it is strictly inside the forward arc from h to its mandatory mate t.
This uses the exact h-cycle of the common head, independently of the
near-shortest route from that head to its selected low-margin parent. -/
theorem interior {q n} (X : Model q n) (hq : 2≤q) {h t v y}
    (ht : h≠t) (hv : h∈X.V) (yv : y∈X.V) (vh : v≠h)
    (forward : Forces X.D X.V q h t) (hy : X.D h y=true) (vy : X.D v y=true)
    {C} (c : Cycle X.D X.V q C) (hc : h∈C) (vc : v∈C) :
    depth X.D X.V h v<depth X.D X.V h t := by
  obtain ⟨A,ca,ha,ya⟩ := edge_cycle X hq hv yv hy
  obtain ⟨pos,_,initial,_⟩ := segments (by omega : 1≤q) X.free ca ha (forward A ca ha)
  let d := span X.D X.V q h t
  let e := span X.D X.V q h v
  have edgePath : Walk X.D X.V v t d := by
    change Walk X.D A h t d at initial
    have dd : d=(d-1)+1 := by dsimp only [d]; omega
    rw [dd] at initial ⊢
    cases initial with
    | step zm hz tail =>
      obtain rfl := card_le_one.mp (ca.heads h ha).le _ (mem_outN.mpr ⟨zm,hz⟩) _ (mem_outN.mpr ⟨ya,hy⟩)
      exact .step yv vy (tail.mono ca.sub)
  obtain ⟨_,lim,prefixToV,rev⟩ := segments (by omega : 1≤q) X.free c hc vc
  change Walk X.D C h v e at prefixToV
  have maxE : e≤q := by
    by_contra! big
    have zero : q+1-span X.D X.V q h v=0 := by change q+1-e=0; omega
    rw [zero] at rev
    cases rev
    exact vh rfl
  suffices e<d by simpa [d,e,span,ht,vh.symm] using this
  by_contra! le
  obtain ⟨f,start,last,step⟩ := prefixToV.toFun
  have front := walk_between step (Nat.zero_le d) le
  rw [start,Nat.sub_zero] at front
  obtain ⟨_,_,old,_⟩ := segments (by omega : 1≤q) X.free c hc (forward C c hc)
  have hit : f d=t := ConsecutiveBlockerPool.same_end c hc front old
  have rest := walk_between step le le_rfl
  rw [hit,last] at rest
  exact X.free v (d+(e-d)) (by dsimp only [d,e] at *; omega) (by omega) (edgePath.append (rest.mono c.sub))

/-- A genuine two-parent transition whenever the old and new rows occur on
a common shortest cycle. Otherwise their shortest-cycle columns are disjoint.
Every possible old common cycle has the same strict distance decrease. -/
theorem transition {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tv : t∈X.V) (ht : h≠t) (forward : Forces X.D X.V q h t)
    (back : Forces X.D X.V q t h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) :
    ∃v∈X.V,∃y∈outN X.D X.V h, X.D v y=true ∧
      ∀B : Finset ℕ,(∀z∈B,Forces X.D X.V q z h) →
      ∃N,Cycle X.D (X.V\B) q N ∧ v∈N ∧ y∈N ∧
        ((∀C,Cycle X.D X.V q C → h∈C → v∉C) ∨
         (depth X.D X.V h v<depth X.D X.V h t ∧ ∃C,Cycle X.D X.V q C ∧
           h∈C ∧ t∈C ∧ v∈C ∧ PunctureCycleLoop.Step X.D C N)) := by
  obtain ⟨_,v,vt,_,cost,witness⟩ := MinimumPairEscape.all_heads X hq hv tv ht forward back minimum size
  have nonempty : (outN X.D (outN X.D X.V h) v).Nonempty := by
    by_contra no
    rw [not_nonempty_iff_eq_empty.mp no,sum_empty,Nat.mul_zero] at cost
    omega
  obtain ⟨y,yhit⟩ := nonempty
  obtain ⟨yh,vy⟩ := mem_outN.mp yhit
  have vout := mem_sdiff.mp (mem_sdiff.mp vt).1
  have ne : h≠v := fun eq => vout.2 (by rw [←eq]; exact mem_insert_self _ _)
  refine ⟨v,vout.1,y,yh,vy,?_⟩
  intro B mandatory
  obtain ⟨N,cn,vn,yn⟩ := witness B mandatory y yhit
  refine ⟨N,cn,vn,yn,?_⟩
  by_cases common : ∃C,Cycle X.D X.V q C ∧ h∈C ∧ v∈C
  · obtain ⟨C,c,hc,vc⟩ := common
    have hy := (mem_outN.mp yh).2
    have away : y∉C := fun yc => ne (card_le_one.mp (c.incoming y yc).le _
      (mem_inN.mpr ⟨hc,hy⟩) _ (mem_inN.mpr ⟨vc,vy⟩))
    exact Or.inr ⟨interior X hq ht hv (mem_outN.mp yh).1 ne.symm forward hy vy c hc vc,
      C,c,hc,forward C c hc,vc,y,mem_sdiff.mpr ⟨yn,away⟩,
      one_lt_card.mpr ⟨h,mem_inN.mpr ⟨hc,hy⟩,v,mem_inN.mpr ⟨vc,vy⟩,ne⟩⟩
  · exact Or.inl (fun C c hc vc => common ⟨C,c,hc,vc⟩)

#print axioms interior
#print axioms transition
end LeanCH.BR.Closure.PairEscapeTransition
