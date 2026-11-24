import checkpoints.shen_extension.ReceiverPrivatePacking

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 CHRuleCatalog AvoidedHeadQuota BoundaryTightParentReach

/-- On the SAME selected g, resolve the private-return theorem without
selecting another existential root. The original unbundled law remains
available to ordinary Lean applications. -/
theorem refine_sole {D V q v g} {law : ReceiverLaw}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1)
    (win : ParentWindow q law.degree (law.lowerCount*law.missing))
    (size : (ball D V v 2\ball D V v 1).card=law.shell)
    (many : law.lowerCount≤((ball D V v 2\ball D V v 1).filter
      fun z=>law.missing≤(outN D V v\inN D V z).card).card)
    (sole : ((outN D V v).filter fun a=>(ball D V v 2\ball D V v 1)⊆outN D V a)={g}) :
    let H:=outN D V v
    let Y:=ball D V v 2\ball D V v 1
    remote D H q ((law.degree-1)/q) g=outN D H g ∧
      ∀z∈Y,∀b∈H,D z b=true → D g b≠true →
        ∃a∈tight D H ((law.degree-1)/q) g,Walk D H b a (q-2) ∧ Y\outN D V a={z} := by
  obtain plural|⟨g',_,fg,table,paths⟩ := marked_reconstruction free vm reg fit one win size many
  · rw [sole,card_singleton] at plural
    omega
  · have same : g=g' := singleton_inj.mp (sole.symm.trans fg)
    exact same ▸ ⟨table,paths⟩

attribute [aesop safe forward (immediate := [free,vm,reg,fit,one,win,size,many,sole])
  (rule_sets := [CHGraphFamilies])] refine_sole
ch_family_split_result refine_sole
#print axioms refine_sole
end LeanCH.BR.LabelledCompromiseRecipe
