import checkpoints.shen_extension.ReceiverOneCover

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota

/-- A nonempty heavy bank fits in the actual internal slots of a single
full head. If it is empty the numerical bound still holds. -/
theorem bank_ceiling {D V q r t v} (free : QFree D V q) (cut : 3≤q)
    (vm : v∈V) (reg : OutEq r D V) (mult : r=q*t+1)
    (br : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2 \ ball D V v 1).card+t=r+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    let B:=H.filter fun b=>max 1 F.card<(inN D Y b).card
    B.card≤r-Y.card ∧ (B.Nonempty → ∃g∈F,B⊆outN D H g) := by
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let F:=H.filter fun g=>Y⊆outN D V g
  let B:=H.filter fun b=>max 1 F.card<(inN D Y b).card
  have take (live : B.Nonempty) : ∃g∈F,B⊆outN D H g :=
    one_cover free cut vm reg mult br one (filter_subset ..) live (fun _ bm=>(mem_filter.mp bm).2)
  refine ⟨?_,take⟩
  change B.card≤r-Y.card
  by_cases live : B.Nonempty
  · obtain ⟨g,gm,cover⟩ := take live
    have row := missing_count free (by omega) vm (mem_filter.mp gm).1 (reg g (outN_subset (mem_filter.mp gm).1))
    change (Y\outN D V g).card+r=Y.card+(outN D H g).card at row
    rw [sdiff_eq_empty_iff_subset.mpr (mem_filter.mp gm).2,card_empty] at row
    have := card_le_card cover
    omega
  · simp [not_nonempty_iff_eq_empty.mp live]

theorem marked_bank_ceiling {D V q} {law : ReceiverLaw} {v}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (size : (ball D V v 2 \ ball D V v 1).card=law.shell)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    let B:=H.filter fun b=>max 1 F.card<(inN D Y b).card
    B.card≤law.degree-law.shell ∧ (B.Nonempty → ∃g∈F,B⊆outN D H g) := by
  obtain ⟨cut,two,region,mult,_,_⟩ := fit
  have result := bank_ceiling free cut vm reg mult (WeightedSD.boundary_regular_outside_pressure_region cut two region)
    (size ▸ one)
  exact ⟨size ▸ result.1,result.2⟩

attribute [aesop safe forward (immediate := [free,cut,vm,reg,mult,br,one])
  (rule_sets := [CHGraphFamilies])] bank_ceiling
attribute [aesop safe forward (immediate := [free,vm,reg,size,fit,one])
  (rule_sets := [CHGraphFamilies])] marked_bank_ceiling
ch_family_split_result marked_bank_ceiling
#print axioms bank_ceiling
#print axioms marked_bank_ceiling
end LeanCH.BR.LabelledCompromiseRecipe
