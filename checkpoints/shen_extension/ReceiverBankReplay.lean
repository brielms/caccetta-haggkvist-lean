import checkpoints.shen_extension.ReceiverReturnFork

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 CHRuleCatalog AvoidedHeadQuota

/-- Both alternatives retain the same chosen source, receiver and
marked physical return. In the sole-head case the statement applies to
every original return target, including the one named by the supplier. -/
theorem receiver_bank {D V q} {law : ReceiverLaw} (witness : law.on D V)
    (free : QFree D V q) (reg : OutEq law.degree D V)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1) :
    ∃v∈V,∃g∈outN D V v,∃h∈outN D V v,∃z∈ball D V v 2 \ ball D V v 1,∃b∈outN D V v,
      let H:=outN D V v
      let Y:=ball D V v 2 \ ball D V v 1
      (inN D V v).card=law.parents ∧ Y.card=law.shell ∧
      (∑a∈H,(law.degree-(inN D V a).card))≤law.charge ∧
      law.degree≤(inN D V h).card ∧ law.missing≤(H \ inN D V z).card ∧ D h z=true ∧ D z b=true ∧
      Y⊆outN D V g ∧ b≠g ∧ D b g≠true ∧
      ((∃a∈H,a≠g ∧ Y⊆outN D V a) ∨
        ∀z'∈Y,∀b'∈H,D z' b'=true → D g b'≠true → Walk D H b' g (q-1)) := by
  classical
  obtain ⟨cut,two,region,mult,cost,cover⟩ := fit
  have br := WeightedSD.boundary_regular_outside_pressure_region cut two region
  obtain ⟨v,vm,parents,sz,price,low,_,h,hm,heavy,z,zm,hz,b,bm,zb,g,gm,full,_,ne,off⟩ :=
    full_at witness free cut reg mult br cost cover
  let Y:=ball D V v 2 \ ball D V v 1
  let H:=outN D V v
  let X:=Y.filter fun s=>law.missing≤(H\inN D V s).card
  have cap : law.degree*(Y.card+(law.degree-1)/q-law.degree)<X.card*law.missing := by
    change Y.card=law.shell at sz
    rw [sz]
    exact cost.trans_le (Nat.mul_le_mul_right _ low)
  have excess := high_head free (by omega) vm reg (X:=X) (filter_subset ..) (fun s sm=>(mem_filter.mp sm).2) cap
  have fork := full_or_returns free (by omega) vm reg gm mult br (by rw [sz]; exact one) full excess
  obtain ⟨zy,miss⟩ := mem_filter.mp zm
  exact ⟨v,vm,g,gm,h,hm,z,zy,b,bm,parents,sz,price,heavy,miss,hz,zb,full,ne,off,fork⟩

-- Replay opens the receiver packet once, in ReceiverMarkedRoot. This theorem stays available to ordinary proofs.
#print axioms receiver_bank
end LeanCH.BR.LabelledCompromiseRecipe
