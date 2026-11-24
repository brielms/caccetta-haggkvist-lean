import LeanCH.BR.BRWeightedCoherentCompletion
import LeanCH.BR.BRRootedPendantSupplier

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

theorem single_excess_arc_count {D : CH.Digraph} {V : Finset ℕ} {d : ℕ}
    (B : V) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B→(outN D V x).card=d) :
    (arcSet D V).card=V.card*d+1 := by
  rw [arc_count_outdegree]
  calc
    ∑x∈V,(outN D V x).card = ∑x∈V,(d+if x=B.val then 1 else 0) := by
      apply sum_congr rfl
      intro x hx
      by_cases he : x=B.val
      · subst x; simpa using hB
      · simp only [he,ite_false,add_zero]
        exact hout ⟨x,hx⟩ (fun e=>he (congrArg Subtype.val e))
    _ = V.card*d+1 := by simp [sum_add_distrib,B.property]

/-- The actual deletion at the two excess labels is regular in both directions. -/
theorem two_excess_deletion_regular {D : CH.Digraph} {V : Finset ℕ} {d : ℕ}
    (B G : V) (hBG : D B G=true) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B→(outN D V x).card=d) (hG : (inN D V G).card=d+1)
    (hin : ∀x:V,x≠G→(inN D V x).card=d) :
    (∀x:V,(outN (eraseArc D B G) V x).card=d) ∧
    (∀x:V,(inN (eraseArc D B G) V x).card=d) := by
  have outdel {E : CH.Digraph} (b g : V) (he : E b g=true)
      (hb : (outN E V b).card=d+1) (ho : ∀x:V,x≠b→(outN E V x).card=d) :
      ∀x:V,(outN (eraseArc E b g) V x).card=d := by
    intro x
    have hc := outdegree_erase_actual b g he x
    by_cases hx : x=b
    · subst x; rw [hb] at hc; simpa using hc
    · have hv : x.val≠b.val := fun e=>hx (Subtype.ext e)
      simpa only [ho x hx,hv,ite_false,add_zero] using hc
  refine ⟨outdel B G hBG hB hout,?_⟩
  intro x
  have he := outdel (E:=fun i j=>D j i) G B hBG hG hin x
  simpa only [eraseArc_reverse,outN,inN] using he

/-- No saturation or weights are needed to retain an actual negative minimum
endpoint from two coherent completions of the actual regular deletion. -/
theorem NativeArcMinimum.single_excess_coherent_negative {q d : ℕ} (hq : 2≤q)
    (hd : 1≤d) {D : CH.Digraph} {V : Finset ℕ}
    (hF : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card)
    (B G : V) (hn : V.card=q*d+1) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B→(outN D V x).card=d) (hG : (inN D V G).card=d+1)
    (hin : ∀x:V,x≠G→(inN D V x).card=d) (hBG : D B G=true)
    (i j k l : V) (h1 : ¬eraseArc D B G i j=true) (h2 : ¬eraseArc D B G k l=true)
    (hdist : i≠k ∨ j≠l) (hshare : i=k ∨ j=l)
    (hs1 : QFree (insertArc (eraseArc D B G) i j) V q)
    (hs2 : QFree (insertArc (eraseArc D B G) k l) V q) :
    ∃E : CH.Digraph,NativeArcMinimum q E V ∧ ∃w∈V,1+q*(outN E V w).card<V.card := by
  have hr := two_excess_deletion_regular B G hBG hB hout hG hin
  obtain ⟨w,_,_,hm,_,_,hneg⟩ := hF.coherent_regular_completion_negative hq hd hsmall hn
    (single_excess_arc_count B hB hout) hr.1 hr.2 i j k l h1 h2 hdist hshare hs1 hs2
  exact ⟨_,hm,w,w.property,hneg⟩

/-- Rooted In-pendant residual, on the SAME saturated source. The first branch
is an actual negative minimum graph, not an assumed exclusion of that branch. -/
theorem NativeExtremal.rooted_in_singleton_residual {d : ℕ} (hd : 1≤d)
    {D : CH.Digraph} {V : Finset ℕ} {cF : ℚ} (hF : NativeExtremal 3 D V cF)
    (hsmall : SmallerSmallRow 3 V.card) (hsat : Sat 3 D V) (B G : V)
    (hn : V.card=3*d+1) (hB : (outN D V B).card=d+1)
    (hout : ∀x:V,x≠B→(outN D V x).card=d) (hG : (inN D V G).card=d+1)
    (hin : ∀x:V,x≠G→(inN D V x).card=d) {h t p : ℕ}
    (hP : InducedInPendant D V B h t p) :
    (∃E : CH.Digraph,NativeArcMinimum 3 E V ∧ ∃w∈V,1+3*(outN E V w).card<V.card) ∨
    2≤(RelayFold.C D V B h t).card ∨
    (RelayFold.C D V B h t={G.val} ∧ RelayFold.X0 D V B h t={p} ∧ D G p=true ∧ B≠G) := by
  classical
  have f := hP.1
  have base : AdjacentRelay.Base D V B h t :=
    ⟨hF.free,f.root_mem,f.middle_mem,f.bottom_mem,f.rh,f.ru,f.hu,f.middle_bottom,f.root_bottom⟩
  have hp : p∈RelayFold.X0 D V B h t := RelayFold.mem_X0.mpr
    ⟨f.pendant_mem,hP.2.1,f.no_pendant_bottom,f.no_pendant_root⟩
  obtain ⟨c,hc,ecp⟩ := base.bank_nonempty_of_independent hsat hp f.no_root_pendant
  by_cases hc2 : 2≤(RelayFold.C D V B h t).card
  · exact Or.inr (Or.inl hc2)
  have hC : RelayFold.C D V B h t={c} := eq_singleton_iff_unique_mem.mpr
    ⟨hc,fun x hx=>card_le_one.mp (by omega) x hx c hc⟩
  let cV : V := ⟨c,(RelayFold.mem_C.mp hc).1⟩
  let pV : V := ⟨p,f.pendant_mem⟩
  have eBc : D B cV=true := (RelayFold.mem_C.mp hc).2.1
  have hsafe := (base.singleton_bank_completion hC hp).2
  by_cases hcG : cV=G
  · have hCG : RelayFold.C D V B h t={G.val} := by
      simpa only [show c=G.val from congrArg Subtype.val hcG] using hC
    have eBG : D B G=true := hcG ▸ eBc
    have eGp : D G p=true := by simpa only [show c=G.val from congrArg Subtype.val hcG] using ecp
    by_cases heq : RelayFold.X0 D V B h t={p}
    · exact Or.inr (Or.inr ⟨hCG,heq,eGp,fun eq=>
        loopfree hF.free (by decide) B.property (by simpa only [←eq] using eBG)⟩)
    · have hex : ∃e∈RelayFold.X0 D V B h t,e≠p := by
        by_contra hnex
        push Not at hnex
        exact heq (eq_singleton_iff_unique_mem.mpr ⟨hp,hnex⟩)
      obtain ⟨e,he,hep⟩ := hex
      let eV : V := ⟨e,(RelayFold.mem_X0.mp he).1⟩
      have hsP := (base.singleton_bank_completion hCG hp).2
      have hsE := (base.singleton_bank_completion hCG he).2
      left
      exact hF.arcMinimum.single_excess_coherent_negative (by decide) hd hsmall B G hn
        hB hout hG hin eBG pV B eV B
        (fun ee=>f.no_pendant_root (eraseArc_sub D B G p B ee))
        (fun ee=>(RelayFold.mem_X0.mp he).2.2.2 (eraseArc_sub D B G e B ee))
        (Or.inl (fun ee=>hep (congrArg Subtype.val ee).symm)) (Or.inr rfl) hsP hsE
  · obtain ⟨_,_,_,hm,_,_,_,hneg,_⟩ := hF.saturated_completion_negative (by decide)
      hsmall hsat B cV pV B hn hB hout (hin cV hcG) eBc f.no_pendant_root hsafe
    exact Or.inl ⟨_,hm,cV,cV.property,hneg⟩

end LeanCH.BR.WeightedSD
