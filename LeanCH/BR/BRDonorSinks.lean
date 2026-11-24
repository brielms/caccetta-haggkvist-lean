import LeanCH.BR.BRDonorIncidence

/-! Actual closed strong banks, out-neighborhood sinks, and a minout boundary
count. Donor presence is a structural witness, not a paid shared-cut supplier. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem donor_sink_bank_outUniform {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) (hno : DonorAbsent D V)
    (hcase : Sat 3 D V ∨ QFree D V 4) {r : ℕ} (hr : r∈V)
    (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (hclosed : ClosedBank D (outN D V r) S) : OutUniform D V S := by
  intro x hx y hy t ht htn
  by_cases hto : t∈outN D V r
  · have nx : ¬D x t=true := fun e=>htn (hclosed x hx t hto e)
    have ny : ¬D y t=true := fun e=>htn (hclosed y hy t hto e)
    exact (Bool.eq_false_iff.mpr nx).trans (Bool.eq_false_iff.mpr ny).symm
  · exact donor_strong_external_uniform hf hno hcase hr ht hSO hst
      (fun e=>hto (mem_outN.mpr ⟨ht,e⟩)) x hx y hy

theorem donor_absent_prime_out_sink {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hno : DonorAbsent D V)
    (hcase : Sat 3 D V ∨ QFree D V 4)
    (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S)
    {r : ℕ} (hr : r∈V) (hne : (outN D V r).Nonempty) :
    ∃ h∈outN D V r,∀ z∈outN D V r,¬D h z=true := by
  obtain ⟨S,hS,hSO,hclosed,hstrong⟩ := exists_closed_strong_bank D hne
  have hmodule := donor_sink_bank_outUniform hf hno hcase hr hSO hstrong hclosed
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

theorem donor_absent_out_sinks {q : ℕ} (hq : 3≤q) {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hsat : Sat q D V) (hno : DonorAbsent D V)
    (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S) :
    ∀ r∈V,(outN D V r).Nonempty → ∃ h∈outN D V r,∀ z∈outN D V r,¬D h z=true := by
  intro r hr hne
  apply donor_absent_prime_out_sink (hf.mono_bound hq) hno ?_ hprime hr hne
  by_cases he : q=3
  · exact Or.inl (he ▸ hsat)
  · exact Or.inr (hf.mono_bound (by omega))

theorem donor_absent_out_sinks_no4 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (hno : DonorAbsent D V)
    (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S) :
    ∀ r∈V,(outN D V r).Nonempty → ∃ h∈outN D V r,∀ z∈outN D V r,¬D h z=true :=
  fun _ hr hne=>donor_absent_prime_out_sink (hf.mono_bound (by decide)) hno (Or.inr hf) hprime hr hne

/-- The three actual head/parent banks are disjoint and avoid the root. -/
theorem out_sink_degree_sum {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) {r h : ℕ} (hr : r∈V) (hh : h∈outN D V r)
    (hsink : ∀ z∈outN D V r,¬D h z=true) :
    (outN D V r).card+(inN D V r).card+(outN D V h).card+1≤V.card := by
  classical
  have hhV := outN_subset hh
  have erh := (mem_outN.mp hh).2
  have hOI : Disjoint (outN D V r) (inN D V r) := by
    apply disjoint_left.mpr
    intro z hz hi
    exact digonfree hf (by decide) hr (outN_subset hz) (mem_outN.mp hz).2 (mem_inN.mp hi).2
  have hH : Disjoint (outN D V r ∪ inN D V r) (outN D V h) := by
    apply disjoint_left.mpr
    intro z hz hh
    rcases mem_union.mp hz with hz|hz
    · exact hsink z hz (mem_outN.mp hh).2
    · exact donor_no_triangle hf hr hhV (outN_subset hh) erh (mem_outN.mp hh).2 (mem_inN.mp hz).2
  let P := (outN D V r ∪ inN D V r) ∪ outN D V h
  have hPV : P⊆V := union_subset (union_subset outN_subset (filter_subset _ _)) outN_subset
  have hrP : r∉P := by
    intro hp
    rcases mem_union.mp hp with hp|hp
    · rcases mem_union.mp hp with hp|hp
      · exact loopfree hf (by decide) hr (mem_outN.mp hp).2
      · exact loopfree hf (by decide) hr (mem_inN.mp hp).2
    · exact digonfree hf (by decide) hr hhV erh (mem_outN.mp hp).2
  have hcard := card_le_card (insert_subset hr hPV)
  rw [card_insert_of_notMem hrP] at hcard
  simpa only [P,card_union_of_disjoint hH,card_union_of_disjoint hOI] using hcard

/-- Only the degree floor is assumed. Once sinks are supplied, saturation,
primality, weights and induction play no role in the count. -/
theorem boundary_balance_of_out_sinks {d : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hn : V.card=3*d+1)
    (hmin : ∀ v∈V,d≤(outN D V v).card)
    (hsinks : ∀ r∈V,(outN D V r).Nonempty → ∃ h∈outN D V r,∀ z∈outN D V r,¬D h z=true) :
    ∀ v∈V,(outN D V v).card=d ∧ (inN D V v).card=d := by
  classical
  have hin : ∀ v∈V,(inN D V v).card≤d := by
    intro v hv
    by_cases hd : d=0
    · subst d
      have he : inN D V v=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro u hu
        have huv : u=v := Finset.card_le_one.mp (by omega : V.card≤1) u (mem_inN.mp hu).1 v hv
        exact loopfree hf (by decide) hv (huv ▸ (mem_inN.mp hu).2)
      simp [he]
    · obtain ⟨h,hh,hs⟩ := hsinks v hv (card_pos.mp (lt_of_lt_of_le (by omega : 0<d) (hmin v hv)))
      have hc := out_sink_degree_sum hf hv hh hs
      have hm := hmin v hv
      have hmh := hmin h (outN_subset hh)
      omega
  have hsum : ∑ v∈V,(outN D V v).card = ∑ v∈V,(inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hlo := sum_le_sum hmin
  have hhi := sum_le_sum hin
  have hiEq : (∑ v∈V,(inN D V v).card) = ∑ _v∈V,d := le_antisymm hhi (hsum ▸ hlo)
  have hoEq : (∑ _v∈V,d) = ∑ v∈V,(outN D V v).card := (hsum.trans hiEq).symm
  intro v hv
  exact ⟨((sum_eq_sum_iff_of_le hmin).mp hoEq v hv).symm,
    (sum_eq_sum_iff_of_le hin).mp hiEq v hv⟩

theorem donor_of_prime_boundary_excess {d : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hsat : Sat 3 D V)
    (hprime : ∀ S⊆V,2≤S.card→S≠V→¬OutUniform D V S)
    (hn : V.card=3*d+1) (hmin : ∀ v∈V,d≤(outN D V v).card)
    {h : ℕ} (hh : h∈V) (hexcess : d<(outN D V h).card) :
    ∃ z h t u,OriginalDonor D V z h t u := by
  classical
  by_contra hnone
  have hno : DonorAbsent D V := fun z h t u e=>hnone ⟨z,h,t,u,e⟩
  have hs := donor_absent_out_sinks le_rfl hf hsat hno hprime
  have heq := (boundary_balance_of_out_sinks hf hn hmin hs h hh).1
  omega

end LeanCH.BR.WeightedSD
