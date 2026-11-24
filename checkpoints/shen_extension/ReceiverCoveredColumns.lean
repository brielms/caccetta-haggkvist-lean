import checkpoints.shen_extension.ReceiverFullBankCover

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota

/-- Keep the exact target bank first. Only the final numerical relaxation
counts each full row's internal slots, allowing arbitrary overlap. -/
theorem column_set {D : CH.Digraph} {H Y F : Finset ℕ} {d : ℕ}
    (cover : ∀b∈H,max 1 F.card<(inN D Y b).card → ∃g∈F,D g b=true)
    (slots : ∀g∈F,(outN D H g).card≤d) :
    let B:=H.filter fun b=>max 1 F.card<(inN D Y b).card
    B⊆F.biUnion (outN D H) ∧ B.card≤F.card*d := by
  classical
  let B:=H.filter fun b=>max 1 F.card<(inN D Y b).card
  have sub : B⊆F.biUnion (outN D H) := by
    intro b bm
    obtain ⟨bh,large⟩ := mem_filter.mp bm
    obtain ⟨g,gm,arc⟩ := cover b bh large
    exact mem_biUnion.mpr ⟨g,gm,mem_outN.mpr ⟨bh,arc⟩⟩
  have cap := sum_le_sum slots
  rw [sum_const_nat (fun _ _=>rfl)] at cap
  exact ⟨sub,(card_le_card sub).trans ((card_biUnion_le ..).trans cap)⟩

theorem marked_column_set {D V q} {law : ReceiverLaw} {v}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (size : (ball D V v 2 \ ball D V v 1).card=law.shell)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    let B:=H.filter fun b=>max 1 F.card<(inN D Y b).card
    B⊆F.biUnion (outN D H) ∧ B.card≤F.card*(law.degree-law.shell) := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let F:=H.filter fun g=>Y⊆outN D V g
  have cover := marked_full_bank_cover free vm reg size fit one
  apply column_set cover
  intro g gm
  change g∈F at gm
  obtain ⟨gh,full⟩ := mem_filter.mp gm
  have cut := fit.1
  have budget := missing_count free (by omega) vm gh (reg g (outN_subset gh))
  change (Y\outN D V g).card+law.degree=Y.card+(outN D H g).card at budget
  rw [sdiff_eq_empty_iff_subset.mpr full,card_empty] at budget
  change Y.card=law.shell at size
  change (outN D H g).card≤law.degree-law.shell
  omega

attribute [aesop safe forward (immediate := [free,vm,reg,size,fit,one])
  (rule_sets := [CHGraphFamilies])] marked_column_set
ch_family_split_result marked_column_set
#print axioms column_set
#print axioms marked_column_set
end LeanCH.BR.LabelledCompromiseRecipe
