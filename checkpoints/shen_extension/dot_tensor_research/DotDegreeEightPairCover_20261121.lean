import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileCapstone_20261121

namespace LeanCH.BR.DotDegreeEight
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators
private theorem out_erase (D : CH.Digraph) (V : Finset ℕ) (v u : ℕ) :
    outN D (V.erase u) v = (outN D V v).erase u := by
  ext x
  simp only [mem_outN, mem_erase]
  tauto

private theorem keep_previous {D : CH.Digraph} {V : Finset ℕ} {a v d : ℕ}
    (h : d+1 ≤ (outN D V v).card) : d ≤ (outN D (V.erase a) v).card := by
  rw [out_erase]
  by_cases hv : a ∈ outN D V v
  · rw [card_erase_of_mem hv]; omega
  · rw [erase_eq_of_notMem hv]; omega

private theorem keep_previous_pair {D : CH.Digraph} {V : Finset ℕ} {a b v d : ℕ}
    (h : d+1 ≤ (outN D V v).card) (block : ¬ (D v a = true ∧ D v b = true)) :
    d ≤ (outN D ((V.erase a).erase b) v).card := by
  rcases not_and_or.mp block with ha | hb
  · rw [out_erase, out_erase, erase_eq_of_notMem (fun m => ha (mem_outN.mp m).2)]
    simpa [out_erase] using (keep_previous (a := b) h)
  · rw [out_erase, out_erase, erase_eq_of_notMem (fun m => hb (mem_outN.mp (mem_erase.mp m).2).2)]
    simpa [out_erase] using (keep_previous (a := a) h)

/-- At the first order outside the one-vertex transfer, either a pair
is deletable or every pair has a common parent in the actual host. -/
theorem pair_cover_of_endpoint {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (E : DotDegreeSeven.Endpoint q d) (hd : 0<d) (hq : 0<q)
    (hf : QFree D V q) (hs : V.card=q*d+2) (ho : OutEq (d+1) D V) :
    ∀ a∈V, ∀ b∈V, a≠b → ∃ x∈V, D x a=true ∧ D x b=true := by
  intro a ha b hb ne
  by_contra h
  let U := (V.erase a).erase b
  have uv : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have sz : U.card=q*d := by
    dsimp [U]
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm ne,hb⟩),card_erase_of_mem ha,hs]
    omega
  have min (x) (hx : x∈U) : d≤(outN D U x).card :=
    keep_previous_pair (ho x (uv hx)).ge (fun z => h ⟨x,uv hx,z⟩)
  exact E D U (hf.mono_set uv) (card_pos.mp (sz ▸ Nat.mul_pos hq hd)) sz min

theorem pair_cover_indegree_bill {D : CH.Digraph} {V : Finset ℕ} {d : ℕ}
    (ho : OutEq (d+1) D V)
    (pairs : ∀ a∈V, ∀ b∈V, a≠b → ∃ x∈V, D x a=true ∧ D x b=true) :
    ∀ a∈V, V.card-1 ≤ d*(inN D V a).card := by
  intro a aa
  let P := inN D V a
  have cover : V.erase a ⊆ P.biUnion (fun v => (outN D V v).erase a) := by
    intro b hb
    obtain ⟨x,xv,xa,xb⟩ := pairs a aa b (mem_erase.mp hb).2 (mem_erase.mp hb).1.symm
    exact mem_biUnion.mpr ⟨x,mem_inN.mpr ⟨xv,xa⟩,mem_erase.mpr ⟨(mem_erase.mp hb).1,
      mem_outN.mpr ⟨(mem_erase.mp hb).2,xb⟩⟩⟩
  have cnt := (card_le_card cover).trans card_biUnion_le
  have row (v) (hv : v∈P) : ((outN D V v).erase a).card=d := by
    have p := mem_inN.mp hv
    rw [card_erase_of_mem (mem_outN.mpr ⟨aa,p.2⟩),ho v p.1]
    omega
  rw [card_erase_of_mem aa,sum_congr rfl row,Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at cnt
  exact cnt

theorem diagonal_pair_cover_regular {D : CH.Digraph} {V : Finset ℕ} {d : ℕ}
    (hc : V.card=d*d+2) (ho : OutEq (d+1) D V)
    (pairs : ∀ a∈V, ∀ b∈V, a≠b → ∃ x∈V, D x a=true ∧ D x b=true) :
    ∀ a∈V, (inN D V a).card=d+1 := by
  have low (a) (aa : a∈V) : d+1≤(inN D V a).card := by
    have j := pair_cover_indegree_bill ho pairs a aa
    by_contra! h
    have hh := Nat.mul_le_mul_left d (show (inN D V a).card≤d by omega)
    rw [hc] at j
    omega
  have sum : (∑ a∈V,(inN D V a).card)=(∑ _a∈V,(d+1)) := by
    rw [←sum_out_in]
    exact sum_congr rfl ho
  exact fun a aa => ((sum_eq_sum_iff_of_le low).mp sum.symm a aa).symm

#print axioms pair_cover_of_endpoint
#print axioms pair_cover_indegree_bill
#print axioms diagonal_pair_cover_regular
end LeanCH.BR.DotDegreeEight

