import checkpoints.shen_extension.BoundaryQuotaLift

namespace LeanCH.BR.AvoidedHeadQuota
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog FragmentScoreEquality

/-- For any proposed target set, return the actual rows missing some
target, with a lower bound on how many distinct rows they comprise. -/
theorem missing_parents {D V H Y : _} {q r a d m : ℕ} (free : QFree D V q) (cut : 3≤q)
    (small : NoHost q a) (none : NoHost q d) (degree : ∀v∈V,r≤(outN D V v).card)
    (hv : H⊆V) (yv : Y⊆V) (live : Y.Nonempty) (size : Y.card≤q*a)
    (need : m+a≤Y.card+r+1) (pos : 0<m) (fit : m≤q*d) :
    ∃M⊆H, (∀h∈H,h∈M ↔ ∃y∈Y,D h y≠true) ∧ r+H.card+m<V.card+d+M.card := by
  classical
  let F := H.filter fun h=>∀y∈Y,D h y=true
  have fh : F⊆H := filter_subset ..
  have cap : r+F.card+m<V.card+d := by
    by_contra! room
    exact rectangle free cut small none degree (fh.trans hv) yv live size
      (fun h hm=>(mem_filter.mp hm).2) need pos fit room
  refine ⟨H\F,sdiff_subset,?_,?_⟩
  · intro h hm
    simp [F,hm]
  · have eq := card_sdiff_add_card_eq_card fh
    omega

/-- The first-shell row identity keeps the actual omitted second-shell
labels. Every omitted target costs one additional internal head. -/
theorem missing_count {D V q v h r} (free : QFree D V q) (cut : 2≤q) (vm : v∈V)
    (hm : h∈outN D V v) (exact : (outN D V h).card=r) :
    ((ball D V v 2 \ ball D V v 1) \ outN D V h).card+r =
      (ball D V v 2 \ ball D V v 1).card+(outN D (outN D V v) h).card := by
  classical
  let H := outN D V v
  let Y := ball D V v 2 \ ball D V v 1
  have dist : Disjoint H Y := disjoint_left.mpr fun z zm mem=>
    (mem_sdiff.mp mem).2 (ball_of_adj (mem_outN.mp zm).1 (mem_outN.mp zm).2)
  have hv : H⊆V := outN_subset
  have yv : Y⊆V := sdiff_subset.trans ball_subset
  have split : outN D V h=outN D H h∪outN D Y h := by
    ext z
    constructor
    · intro zm
      rcases SharedHeadSuppliers.layer_heads free cut vm hm zm with hz|yz
      · exact mem_union_left _ (mem_outN.mpr ⟨hz,(mem_outN.mp zm).2⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨yz,(mem_outN.mp zm).2⟩)
    · intro hz; exact (union_subset (outN_mono hv h) (outN_mono yv h)) hz
  have sd : Y \ outN D V h = Y \ outN D Y h := by
    ext z
    simp only [mem_sdiff,mem_outN]
    constructor
    · intro ⟨zm,off⟩; exact ⟨zm,fun p=>off ⟨yv zm,p.2⟩⟩
    · intro ⟨zm,off⟩; exact ⟨zm,fun p=>off ⟨zm,p.2⟩⟩
  change (Y \ outN D V h).card+r=Y.card+(outN D H h).card
  rw [sd,card_sdiff_of_subset outN_subset,←exact,split,card_union_of_disjoint (dist.mono outN_subset outN_subset)]
  have := card_le_card (show outN D Y h ⊆ Y from outN_subset)
  omega

attribute [aesop safe forward (immediate := [free,cut,small,none,degree,hv,yv,live,size,need,pos,fit])
  (rule_sets := [CHGraphFamilies])] missing_parents
attribute [aesop safe forward (immediate := [free,cut,vm,hm,exact])
  (rule_sets := [CHGraphFamilies])] missing_count
#print axioms missing_parents
#print axioms missing_count
end LeanCH.BR.AvoidedHeadQuota
