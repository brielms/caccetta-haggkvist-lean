import checkpoints.shen_extension.ReceiverColumnBudget

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog AvoidedHeadQuota CompromiseQuotaTransfer

/-- Class counts yield a physical head covering the whole shell at the
same marked root as the undercharge and the exceptional return. -/
theorem full_at {D U q t} {law : ReceiverLaw} (witness : law.on D U) (free : QFree D U q)
    (cut : 3≤q) (reg : OutEq law.degree D U) (mult : law.degree=q*t+1)
    (boundary : Compose.Boundary.BoundaryRegular q t)
    (cost : law.degree*(law.shell+t-law.degree)<law.lowerCount*law.missing)
    (cover : law.shell+t≤law.degree+1) :
    ∃v∈U, let H:=outN D U v
           let Y:=ball D U v 2 \ ball D U v 1
           let X:=Y.filter fun z=>law.missing≤(H\inN D U z).card
           (inN D U v).card=law.parents ∧ Y.card=law.shell ∧
           (∑h∈H,(law.degree-(inN D U h).card))≤law.charge ∧
           law.lowerCount≤X.card ∧ X.card≤law.upperCount ∧
           ∃h∈H,law.degree≤(inN D U h).card ∧ ∃z∈X,D h z=true ∧ ∃b∈H,D z b=true ∧
           ∃g∈H, Y⊆outN D U g ∧ (outN D H g).card+Y.card=law.degree ∧ b≠g ∧ D b g≠true := by
  obtain ⟨v,vm,parents,sz,price,low,high,h,hm,heavy,z,zm,hz,b,bm,zb⟩ := physical witness
  let H:=outN D U v
  let Y:=ball D U v 2 \ ball D U v 1
  let X:=Y.filter fun z=>law.missing≤(H\inN D U z).card
  have cap : law.degree*(Y.card+t-law.degree)<X.card*law.missing := by
    change Y.card=law.shell at sz
    rw [sz]
    exact cost.trans_le (Nat.mul_le_mul_right _ low)
  obtain ⟨g,gm,light⟩ := light_head free (by omega) vm reg mult boundary (X:=X) (filter_subset ..)
    (fun a am=>(mem_filter.mp am).2) cap
  change (outN D H g).card<t at light
  have id := missing_count free (by omega) vm gm (reg g (mem_outN.mp gm).1)
  change (Y\outN D U g).card+law.degree=Y.card+(outN D H g).card at id
  change Y.card=law.shell at sz
  have empty : (Y\outN D U g).card=0 := by omega
  have full := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp empty)
  have gz := (mem_outN.mp (full (mem_filter.mp zm).1)).2
  have gv := (mem_outN.mp gm).1
  have bv := (mem_outN.mp bm).1
  have zv := ball_subset (mem_sdiff.mp (mem_filter.mp zm).1).1
  refine ⟨v,vm,parents,sz,price,low,high,h,hm,heavy,z,zm,hz,b,bm,zb,g,gm,full,(show (outN D H g).card+Y.card=law.degree by omega),?_,?_⟩
  · intro same; subst b; exact digonfree free (by omega) gv zv gz zb
  · intro bg
    exact free g 3 (by decide) cut (.step zv gz (.step bv zb (.step gv bg (.refl _))))

attribute [aesop safe forward (immediate := [witness,free,cut,reg,mult,boundary,cost,cover])
  (rule_sets := [CHGraphFamilies])] full_at
ch_family_split_result full_at
#print axioms full_at
end LeanCH.BR.LabelledCompromiseRecipe
