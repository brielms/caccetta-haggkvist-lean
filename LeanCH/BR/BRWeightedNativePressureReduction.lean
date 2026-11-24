import LeanCH.BR.BRWeightedNativePressureRepair

/-! Same-label reduction. Neither resulting branch is asserted impossible. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

def TwoSidedSingleExcess (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ r : ℕ, 2≤r ∧ V.card=q*r+1 ∧ ∃ h g : V,
    (outN D V h).card=r+1 ∧ (∀ i : V, i≠h → (outN D V i).card=r) ∧
    (inN D V g).card=r+1 ∧ (∀ i : V, i≠g → (inN D V i).card=r)

/-- The new native host has exactly the same labels, so the actual global
smaller-order induction hypothesis is unchanged. Reverse strictness uses
the original host's own dual; the repaired host uses its deletion's dual. -/
theorem native_pressure_reduction {q : ℕ} (hq : 3≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) (hcritical : ArcCritical q D V) (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, QFree E V q ∧ ArcCritical q E V ∧ StrictPositiveRows q E V ∧
      ((∃ w∈V, 1+q*(outN E V w).card<V.card) ∨
        (Sat q E V ∧ TwoSidedSingleExcess q E V)) := by
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hbad
  have hproper := hsmall.induced hf
  obtain ⟨a,p,c,hc,ha,hp,hm,hpm,hr,hpc⟩ :=
    strict_pair_of_proper_smallRow hproper hV z hz hzr
  have hs : StrictPositiveRows q D V :=
    ⟨a,ha,hm,fun x hx => by rw [hr x hx]; exact hc⟩
  obtain ⟨H,hH⟩ := strict_inverse_of_proper_smallRow hproper z hz hzr
  rcases arc_core_pressure_dichotomy hq hV hf hcritical hH with hn | ⟨r,hr1,h,hn,hdh,hout,hcol⟩
  · exact ⟨D,hf,hcritical,hs,Or.inl hn⟩
  have hr2 := qfree_single_excess_base_ge_two (by omega) hr1 hf h hn hdh hout
  have hrevcrit := arcCritical_reverse_of_commonInverse hcritical hH
  have hrevstrict := reverse_strict_of_pair hc hp hpm hpc
  rcases arc_core_pressure_dichotomy hq hV hf.reverse hrevcrit (commonInverse_reverse hH)
    with hneg | ⟨t,ht1,g,hnt,hdg,hin,hincol⟩
  · exact ⟨(fun x y => D y x),hf.reverse,hrevcrit,hrevstrict,Or.inl hneg⟩
  have hrt : t=r := by nlinarith
  subst t
  have hgin : (inN D V g).card=r+1 := hdg
  have hin' : ∀ i : V, i≠g → (inN D V i).card=r := hin
  by_cases hsat : Sat q D V
  · exact ⟨D,hf,hcritical,hs,Or.inr ⟨hsat,r,hr2,hn,h,g,hdh,hout,hgin,hin'⟩⟩
  obtain ⟨K,hKf,hKb,w,hw,hwd⟩ := single_excess_repair_negative_reverse
    (by omega) hf hH hr2 h g hn hdh hcol hin' hsat
  have hwd' : 1+q*(outN (fun x y => K y x) V w).card<V.card := hwd
  obtain ⟨E,_,hEf,hEc,hEs,hEw⟩ := native_core_below_degree hsmall hKf.reverse hKb hwd'
  exact ⟨E,hEf,hEc,hEs,Or.inl ⟨w,hw,hEw⟩⟩

/-- An arbitrary strict source can first be minimized on its existing label
set. No saturation or primeness is transferred through that minimization. -/
theorem strict_source_pressure_reduction {q : ℕ} (hq : 3≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, QFree E V q ∧ ArcCritical q E V ∧ StrictPositiveRows q E V ∧
      ((∃ w∈V, 1+q*(outN E V w).card<V.card) ∨
        (Sat q E V ∧ TwoSidedSingleExcess q E V)) := by
  obtain ⟨E,_,hEf,hEb,hEc⟩ := exists_arc_critical_subgraph hf hbad
  exact native_pressure_reduction hq hsmall hEf hEc hEb

end LeanCH.BR.WeightedSD
