import LeanCH.BR.BRWeightedExactRepairProfile
import LeanCH.BR.BRWeightedPressureFrontier

/-! Preserve the actual input on the saturated branch, and global arc minimum
on every negative output. No maximum-level claim is transferred through edits. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

/-- Same-label pressure reduction with no reminimization in the repair branch.
The positive alternative is literally D. -/
theorem NativeArcMinimum.negative_or_saturated_single_excess {q : ℕ} (hq : 3≤q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hmin : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card)
    (hH : CommonInverse (realMatrix q D V) H) :
    (∃E : CH.Digraph,NativeArcMinimum q E V ∧
      ∃w∈V,1+q*(outN E V w).card<V.card) ∨
    (Sat q D V ∧ TwoSidedSingleExcess q D V) := by
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hmin.bad
  rcases arc_core_pressure_dichotomy hq hV hmin.free hmin.critical hH
    with hneg|⟨r,hr1,h,hn,hdh,hout,hcol⟩
  · exact Or.inl ⟨D,hmin,hneg⟩
  have hr2 := qfree_single_excess_base_ge_two (by omega) hr1 hmin.free h hn hdh hout
  have hrev := hmin.reverse hsmall
  rcases arc_core_pressure_dichotomy hq hV hrev.free hrev.critical (commonInverse_reverse hH)
    with hneg|⟨s,hs1,g,hns,hdg,hin,hrow⟩
  · exact Or.inl ⟨(fun x y=>D y x),hrev,hneg⟩
  have hsr : s=r := by nlinarith
  subst s
  by_cases hsat : Sat q D V
  · exact Or.inr ⟨hsat,r,hr2,hn,h,g,hdh,hout,hdg,hin⟩
  obtain ⟨w,t,b,hhw,hwg,hwb,hnew,hEmin,hcount,houtE,hinE,hneg⟩ :=
    hmin.nonsaturated_single_excess_repair (by omega) hsmall hH hr2 h g hn hdh hout hdg hin hcol hsat
  exact Or.inl ⟨(fun x y=>insertArc (eraseArc D h w) t b y x),hEmin,w,w.property,hneg⟩

/-- Own normal form of ANY globally minimum competitor. Its arc count agrees
with the selected source, so the original maximum comparison bounds its level. -/
theorem NativeExtremal.minimum_normal_form_le {q : ℕ} {D E : CH.Digraph}
    {V : Finset ℕ} {cF : ℚ} (hF : NativeExtremal q D V cF)
    (hsmall : SmallerSmallRow q V.card) (hE : NativeArcMinimum q E V) :
    (arcSet E V).card=(arcSet D V).card ∧ ArcCritical q E V ∧
    ∃a p : ℕ→ℚ,∃c : ℚ,1<c ∧ c≤cF ∧
      (∀x∈V,0<a x) ∧ (∀x∈V,0<p x) ∧ mass V a=1 ∧ mass V p=1 ∧
      (∀x∈V,row q E V a x=c) ∧ (∀x∈V,col q E V p x=c) ∧
      ∃H : Matrix V V ℝ,CommonInverse (realMatrix q E V) H := by
  have hc : (arcSet E V).card=(arcSet D V).card :=
    le_antisymm (hE.arc_min D hF.free hF.bad) (hF.arc_min E hE.free hE.bad)
  obtain ⟨hcrit,a,p,c,hc1,ha,hp,hm,hpm,hr,hpc,H,hH⟩ := hE.normal_form hsmall
  exact ⟨hc,hcrit,a,p,c,hc1,hF.level_max E hE.free hE.bad hc a c hm hr,
    ha,hp,hm,hpm,hr,hpc,H,hH⟩

/-- BR narrowing is derived on the SAME selected source in the positive branch. -/
theorem NativeExtremal.focused_pressure_frontier {q : ℕ} (hq : 3≤q)
    {D : CH.Digraph} {V : Finset ℕ} {cF : ℚ} {H : Matrix V V ℝ}
    (hF : NativeExtremal q D V cF) (hsmall : SmallerSmallRow q V.card)
    (hH : CommonInverse (realMatrix q D V) H) :
    (∃E : CH.Digraph,NativeArcMinimum q E V ∧
      ∃w∈V,1+q*(outN E V w).card<V.card) ∨
    (Sat q D V ∧ ∃r : ℕ,NativePressureRegion q r ∧ V.card=q*r+1 ∧ ∃h g : V,
      (outN D V h).card=r+1 ∧ (∀i:V,i≠h→(outN D V i).card=r) ∧
      (inN D V g).card=r+1 ∧ (∀i:V,i≠g→(inN D V i).card=r)) := by
  rcases hF.arcMinimum.negative_or_saturated_single_excess hq hsmall hH with
    hneg|⟨hsat,r,hr,hn,h,g,hdh,hout,hdg,hin⟩
  · exact Or.inl hneg
  · exact Or.inr ⟨hsat,r,single_excess_pressure_region hq hr hF.free h hn hdh hout,
      hn,h,g,hdh,hout,hdg,hin⟩

end LeanCH.BR.WeightedSD
