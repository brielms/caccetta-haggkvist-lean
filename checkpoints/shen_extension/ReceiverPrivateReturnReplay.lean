import checkpoints.shen_extension.ReceiverPrivateReturn

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45 BypassRepair LabelledCompromiseRecipe AvoidedHeadQuota

theorem ready_parent_window {D V q} {law : ReceiverLaw} (_packet : law.on D V)
    (_fit : FullWindow q law.degree law.shell law.missing law.lowerCount) :
    ParentWindow q law.degree (law.lowerCount*law.missing) →
    ParentWindow q law.degree (law.lowerCount*law.missing) := id

/-- Numerical hypotheses are separate from the root and all of its incidence
data. The exceptional-column count used here is at this very root v. -/
theorem marked_reconstruction {D V q v} {law : ReceiverLaw}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1)
    (win : ParentWindow q law.degree (law.lowerCount*law.missing))
    (size : (ball D V v 2\ball D V v 1).card=law.shell)
    (many : law.lowerCount≤((ball D V v 2\ball D V v 1).filter
      fun z=>law.missing≤(outN D V v\inN D V z).card).card) :
    let H:=outN D V v
    let Y:=ball D V v 2\ball D V v 1
    let F:=H.filter fun g=>Y⊆outN D V g
    (1<F.card) ∨ (∃g∈H,F={g} ∧ remote D H q ((law.degree-1)/q) g=outN D H g ∧
      ∀z∈Y,∀b∈H,D z b=true → D g b≠true →
        ∃a∈tight D H ((law.degree-1)/q) g,Walk D H b a (q-2) ∧ Y\outN D V a={z}) := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2\ball D V v 1
  let F:=H.filter fun g=>Y⊆outN D V g
  let X:=Y.filter fun z=>law.missing≤(H\inN D V z).card
  let t:=(law.degree-1)/q
  obtain ⟨cut,two,region,mult,overbook,_⟩ := fit
  have br := WeightedSD.boundary_regular_outside_pressure_region cut two region
  have cap : law.degree*(Y.card+t-law.degree)<X.card*law.missing := by
    change Y.card=law.shell at size
    rw [size]
    exact overbook.trans_le (Nat.mul_le_mul_right _ many)
  have mv : ∀z∈X,law.missing≤(H\inN D V z).card := fun _ m=>(mem_filter.mp m).2
  have floor : law.lowerCount*law.missing≤∑a∈H,(Y\outN D V a).card := by
    have cnt := sum_le_sum mv
    rw [sum_const_nat (fun _ _=>rfl)] at cnt
    have inc := sum_le_sum_of_subset (f:=fun z=>(H\inN D V z).card) (show X⊆Y from filter_subset ..)
    exact (Nat.mul_le_mul_right _ many).trans (cnt.trans (inc.trans
      (omitted_entries (D:=D) (show H⊆V from outN_subset) (show Y⊆V from sdiff_subset.trans ball_subset)).le))
  obtain ⟨g,gm,light⟩ := light_head free (by omega) vm reg mult br (X:=X) (filter_subset ..) mv cap
  change (outN D H g).card<t at light
  change Y.card=law.shell at size
  change law.shell+t=law.degree+1 at one
  have id := missing_count free (by omega) vm gm (reg g (outN_subset gm))
  change (Y\outN D V g).card+law.degree=Y.card+(outN D H g).card at id
  have full := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (show (Y\outN D V g).card=0 by omega))
  have fg : g∈F := mem_filter.mpr ⟨gm,full⟩
  by_cases manyFull : 1<F.card
  · exact Or.inl manyFull
  have sole : F={g} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr fg) (by simpa using Nat.le_of_not_gt manyFull)).symm
  have lower k (pos : 2≤k) (kt : k≤t) : NoHost q k ∧ LoneRow.NoNearHost q k := by
    have reduced : ¬WeightedSD.NativePressureRegion q k := by
      change ¬ WeightedSD.NativePressureRegion q t at region
      unfold WeightedSD.NativePressureRegion at *
      omega
    have regk := WeightedSD.boundary_regular_outside_pressure_region cut pos reduced
    have nohost := RetainedShortfall.host_of_regular (RootRegularBridge.inRegular_of_boundaryRegular (by omega) regk) (by omega)
    exact ⟨nohost,RootRegularBridge.near_of_boundaryRegular regk nohost (by omega) pos⟩
  obtain extra|⟨table,privateRows⟩ := receiver_fork free cut vm reg mult br lower (size ▸ one) gm full floor win
  · obtain ⟨a,am,ne,all⟩ := extra
    have af : a∈F := mem_filter.mpr ⟨am,all⟩
    exact False.elim (ne (mem_singleton.mp (sole ▸ af)))
  · exact Or.inr ⟨g,gm,sole,table,privateRows⟩

attribute [aesop safe forward (immediate := [_packet,_fit]) (rule_sets := [CHGraphFamilies])]
  ready_parent_window
ch_family_split_result marked_reconstruction
#print axioms ready_parent_window
#print axioms marked_reconstruction
end LeanCH.BR.BoundaryTightParentReach
