import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactCarriers_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- Every actual one- or two-step return into a one-miss bank propagates
to a second missed row, if each receiver has an internal successor.
Consequently any nonempty return bank produces the excluded spill. -/
theorem exact_no_cycle_bank_returns {D : CH.Digraph} {V A B T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card≤35)
    (cap : ∀ v∈V, (ball D V v 2).card≤15)
    (aV : A⊆V) (bV : B⊆V) (tV : T⊆V) (disj : Disjoint B T)
    (a7 : A.card≤7) (b7 : B.card=7) (t6 : T.card≤6)
    (hmiss : ∀ x∈A, (B \ outN D V x).card≤1)
    (succA : ∀ x∈A, ∃ y∈A, D x y=true)
    (keep : ∀ b∈B, outN D V b⊆A∪(B∪T)) :
    ∀ w∈B, ∀ x∈A, ∀ k, 0<k → k≤2 → ¬ Walk D V w x k := by
  classical
  let R := B.filter (fun w => ∃ x∈A, ∃ k, 0<k ∧ k≤2 ∧ Walk D V w x k)
  have witness (w) (hw : w∈R) : ∃ x∈A, ∃ y∈A, x≠y ∧ w∈B ∧
      w∉outN D V x ∧ w∉outN D V y := by
    obtain ⟨wb,x,xa,k,hk,hk2,wr⟩ := mem_filter.mp hw
    obtain ⟨y,ya,e⟩ := succA x xa
    refine ⟨x,xa,y,ya,fun h => ?_,wb,fun h => ?_,fun h => ?_⟩
    · subst y
      exact loopfree hf (by decide) (aV xa) e
    · exact hf w (k+1) (by omega) (by omega)
        (wr.append (.step (bV wb) (mem_outN.mp h).2 (.refl w)))
    · exact hf w (k+2) (by omega) (by omega)
        (wr.append (.step (aV ya) e (.step (bV wb) (mem_outN.mp h).2 (.refl w))))
  intro w wb x xa k hk h2 wr
  apply exact_no_nonempty_carrier_bank hf ho n cap bV tV disj a7 b7 t6 hmiss witness
  · intro v hv
    obtain ⟨_,y,hy,j,_,hj,wj⟩ := mem_filter.mp hv
    exact ⟨y,hy,aV hy,j,hj,wj⟩
  · intro v hv y hy
    rcases mem_union.mp (keep v (mem_sdiff.mp hv).1 hy) with h|h
    · exact ((mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,y,h,1,
        by decide,by decide,.step (aV h) (mem_outN.mp hy).2 (.refl y)⟩)).elim
    · exact h
  · exact ⟨w,mem_filter.mpr ⟨wb,x,xa,k,hk,h2,wr⟩⟩

#print axioms exact_no_cycle_bank_returns

end LeanCH.BR.DotDegreeSevenLow

