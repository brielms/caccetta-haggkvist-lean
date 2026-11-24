import LeanCH.BR.BRSaturatedFreshExchange
import LeanCH.BR.BRWeightedFocusedPressure

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

/-- Delete the unique outgoing excess and genuinely add an arc. The uniform
deletion law proves badness directly, without an inverse, safety, saturation,
criticality, incoming profile, or source equalizer. -/
theorem single_excess_fresh_completion_bad {q d : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (B v i j : V)
    (hn : V.card=q*d+1) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B → (outN D V x).card=d)
    (hBv : D B v=true) (hnew : ¬D i j=true) :
    ¬SmallRow q (insertArc (eraseArc D B v) i j) V := by
  have hdel : ∀x∈V,(outN (eraseArc D B v) V x).card=d := by
    intro x hx
    have he := outdegree_erase_actual B v hBv x
    by_cases hh : x=B.val
    · rw [hh,hB] at he
      simp only [ite_true] at he
      rw [hh]
      omega
    · have hne : (⟨x,hx⟩:V)≠B := fun h=>hh (congrArg Subtype.val h)
      rw [hout ⟨x,hx⟩ hne] at he
      simpa only [hh,ite_false,add_zero] using he
  apply positive_feasible_extension_not_smallRow hq
    (fun x _ y _ he=>insertArc_mono (eraseArc D B v) i j x y he)
    (fun _=>1) (fun _ _=>by norm_num) ?_ i.property j.property
    (fun he=>hnew (eraseArc_sub D B v i j he)) (by simp [insertArc])
  intro x hx
  rw [row,outW_eq_mass]
  simp only [mass,sum_const,nsmul_eq_mul,mul_one]
  rw [hdel x hx,hn]
  push_cast; linarith

/-- The endpoint itself is globally minimum; no further arc minimization occurs.
Only outgoing degrees are prescribed; no incoming profile or inverse is needed. -/
theorem NativeArcMinimum.saturated_single_excess_completion {q d : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hmin : NativeArcMinimum q D V)
    (hsmall : SmallerSmallRow q V.card) (hsat : Sat q D V) (B v i j : V)
    (hn : V.card=q*d+1) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B → (outN D V x).card=d)
    (hBv : D B v=true) (hnew : ¬D i j=true)
    (hsafe : QFree (insertArc (eraseArc D B v) i j) V q) :
    let K := insertArc (eraseArc D B v) i j
    i≠B ∧ j≠v ∧ NativeArcMinimum q K V ∧ NativeArcMinimum q (fun x y=>K y x) V ∧
      (arcSet K V).card=(arcSet D V).card ∧
      (∀x:V,(outN K V x).card=d+(if x=i then 1 else 0)) := by
  dsimp only
  have hfresh : ¬eraseArc D B v i j=true := fun he=>hnew (eraseArc_sub D B v i j he)
  have hc := arcSet_exchange_card B v i j hBv hfresh
  have hm := hmin.same_count hsafe
    (single_excess_fresh_completion_bad hq B v i j hn hB hout hBv hnew) hc
  have he := saturated_fresh_exchange_endpoints (by omega) hmin.free hsat B v i j
    i.property j.property hnew hsafe
  refine ⟨(fun hh=>he.1 (congrArg Subtype.val hh)),
    (fun hh=>he.2 (congrArg Subtype.val hh)),hm,hm.reverse hsmall,hc,?_⟩
  intro x
  have hh := outdegree_exchange B v i j hBv hfresh x
  have heq (a b:V) : a.val=b.val ↔ a=b := Subtype.ext_iff.symm
  simp only [heq] at hh
  by_cases hx:x=B
  · subst x
    rw [hB] at hh
    simp only [ite_true] at hh
    omega
  · rw [hout x hx] at hh
    simpa only [hx,ite_false,add_zero] using hh

/-- An ordinary incoming degree at the removed head gives an ACTUAL negative
reverse endpoint, with its OWN positive pair, inverse and level comparison.
No distinguished incoming-excess label or distinctness of excess roots is needed. -/
theorem NativeExtremal.saturated_completion_negative {q d : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} {cF : ℚ} (hF : NativeExtremal q D V cF)
    (hsmall : SmallerSmallRow q V.card) (hsat : Sat q D V) (B v i j : V)
    (hn : V.card=q*d+1) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B → (outN D V x).card=d) (hvin : (inN D V v).card=d)
    (hBv : D B v=true) (hnew : ¬D i j=true)
    (hsafe : QFree (insertArc (eraseArc D B v) i j) V q) :
    let K := insertArc (eraseArc D B v) i j
    let E := fun x y=>K y x
    i≠B ∧ j≠v ∧ NativeArcMinimum q K V ∧ NativeArcMinimum q E V ∧
      (arcSet K V).card=(arcSet D V).card ∧ (arcSet E V).card=(arcSet D V).card ∧
      (outN E V v).card=d-1 ∧ 1+q*(outN E V v).card<V.card ∧
      ArcCritical q E V ∧ ∃a p:ℕ→ℚ,∃c:ℚ,1<c ∧ c≤cF ∧
        (∀x∈V,0<a x) ∧ (∀x∈V,0<p x) ∧ mass V a=1 ∧ mass V p=1 ∧
        (∀x∈V,row q E V a x=c) ∧ (∀x∈V,col q E V p x=c) ∧
        ∃H:Matrix V V ℝ,CommonInverse (realMatrix q E V) H := by
  dsimp only
  obtain ⟨hi,hj,hm,hmr,hc,_⟩ := hF.arcMinimum.saturated_single_excess_completion hq
    hsmall hsat B v i j hn hB hout hBv hnew hsafe
  have hfresh : ¬eraseArc D B v i j=true := fun he=>hnew (eraseArc_sub D B v i j he)
  have hdeg := indegree_exchange B v i j hBv hfresh v
  have hvj : v.val≠j.val := fun he=>hj (Subtype.ext he.symm)
  rw [hvin] at hdeg
  simp only [ite_true,hvj,ite_false,add_zero] at hdeg
  have he : (outN (fun x y=>insertArc (eraseArc D B v) i j y x) V v).card=d-1 := by
    change (inN (insertArc (eraseArc D B v) i j) V v).card=d-1
    omega
  have hneg : 1+q*(outN (fun x y=>insertArc (eraseArc D B v) i j y x) V v).card<V.card := by
    change 1+q*(inN (insertArc (eraseArc D B v) i j) V v).card<V.card
    rw [hn]
    nlinarith
  obtain ⟨hcr,hcrit,a,p,c,hc1,hcle,ha,hp,hma,hmp,hr,hpc,H,hH⟩ :=
    hF.minimum_normal_form_le hsmall hmr
  exact ⟨hi,hj,hm,hmr,hc,hcr,he,hneg,hcrit,a,p,c,hc1,hcle,ha,hp,hma,hmp,hr,hpc,H,hH⟩

end LeanCH.BR.WeightedSD
