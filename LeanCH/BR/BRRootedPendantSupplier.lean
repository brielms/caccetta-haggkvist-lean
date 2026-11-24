import LeanCH.BR.BRRootedPendantGeometry

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem pendant_absent_sink_bank_outUniform {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) {r : ℕ} (hno : ¬RootedPendant D V r) (hr : r∈V)
    (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (hclosed : ClosedBank D (outN D V r) S) : OutUniform D V S := by
  intro x hx y hy t ht htn
  by_cases hto : t∈outN D V r
  · have nx : ¬D x t=true := fun e=>htn (hclosed x hx t hto e)
    have ny : ¬D y t=true := fun e=>htn (hclosed y hy t hto e)
    exact (Bool.eq_false_iff.mpr nx).trans (Bool.eq_false_iff.mpr ny).symm
  · exact pendant_absent_strong_external_uniform hf hno hr ht hSO hst
      (fun e=>hto (mem_outN.mpr ⟨ht,e⟩)) x hx y hy

theorem pendant_absent_prime_out_sink {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) {r : ℕ} (hno : ¬RootedPendant D V r)
    (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S)
    (hr : r∈V) (hne : (outN D V r).Nonempty) :
    ∃ h∈outN D V r,∀ z∈outN D V r,¬D h z=true := by
  obtain ⟨S,hS,hSO,hclosed,hstrong⟩ := exists_closed_strong_bank D hne
  have hmodule := pendant_absent_sink_bank_outUniform hf hno hr hSO hstrong hclosed
  have hproper : S≠V := by
    intro e
    have hrr := hSO (e.symm ▸ hr)
    exact loopfree hf (by decide) hr (mem_outN.mp hrr).2
  have hc : S.card≤1 := by
    by_contra hn
    exact hprime S (hSO.trans outN_subset) (by omega) hproper hmodule
  obtain ⟨h,hh⟩ := hS
  refine ⟨h,hSO hh,?_⟩
  intro z hz ehz
  have hzS := hclosed h hh z hz ehz
  have ezh : z=h := Finset.card_le_one.mp hc z hzS h hh
  exact loopfree hf (by decide) (outN_subset (hSO hh)) (ezh ▸ ehz)

theorem rooted_pendant_of_no_out_sink {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S)
    {r : ℕ} (hr : r∈V) (hne : (outN D V r).Nonempty)
    (hnosink : ¬∃ h∈outN D V r,∀ z∈outN D V r,¬D h z=true) :
    RootedPendant D V r := by
  by_contra hn
  exact hnosink (pendant_absent_prime_out_sink hf hn hprime hr hne)

/-- The degree floor is needed only at possible sinks in this root's actual
out-neighborhood. There is no boundary-order equality in this master. -/
theorem rooted_pendant_of_local_degree_pressure {d : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S)
    {r : ℕ} (hr : r∈V) (hne : (outN D V r).Nonempty)
    (hmin : ∀ h∈outN D V r,d≤(outN D V h).card)
    (hsize : V.card≤(outN D V r).card+(inN D V r).card+d) : RootedPendant D V r := by
  apply rooted_pendant_of_no_out_sink hf hprime hr hne
  rintro ⟨h,hh,hs⟩
  have hc := out_sink_degree_sum hf hr hh hs
  have hd := hmin h hh
  omega

/-- Arbitrary degree, including zero. The order need only be at most 3d+1.
Both exceptional roots of a two-sided single-excess host meet this test. -/
theorem rooted_pendant_of_boundary_degree_pressure {d : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S)
    (hn : V.card≤3*d+1) (hmin : ∀ v∈V,d≤(outN D V v).card)
    {r : ℕ} (hr : r∈V) (hex : 2*d<(outN D V r).card+(inN D V r).card) :
    RootedPendant D V r := by
  by_cases hd : d=0
  · subst d
    have hcard : V.card≤1 := by simpa using hn
    have heq : ∀x∈V,x=r := fun x hx=>Finset.card_le_one.mp hcard x hx r hr
    have ho : outN D V r=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact loopfree hf (by decide) hr ((heq x (mem_outN.mp hx).1) ▸ (mem_outN.mp hx).2)
    have hi : inN D V r=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact loopfree hf (by decide) hr ((heq x (mem_inN.mp hx).1) ▸ (mem_inN.mp hx).2)
    simp only [ho,hi,card_empty,Nat.mul_zero,Nat.add_zero,lt_self_iff_false] at hex
  · have hne : (outN D V r).Nonempty := card_pos.mp
      (lt_of_lt_of_le (by omega : 0<d) (hmin r hr))
    exact rooted_pendant_of_local_degree_pressure hf hprime hr hne
      (fun h hh=>hmin h (outN_subset hh)) (by omega)

end LeanCH.BR.WeightedSD
