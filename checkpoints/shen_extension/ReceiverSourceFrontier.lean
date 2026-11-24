import checkpoints.shen_extension.ReceiverFullHead

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog AvoidedHeadQuota

@[ch_numeric_guard] def ReceiverWindow (n r degree score funded : ℕ) : Prop :=
  degree≤r ∧ degree≤funded ∧ n≤degree+score+1

instance {n r degree score funded} : Decidable (ReceiverWindow n r degree score funded) := by
  unfold ReceiverWindow; infer_instance

/-- On eligible inputs replay emits the actual source on the same labels.
Conversely a branch that rules out the receiver excludes this whole window. -/
theorem labelled_source {p : Input} (bad : Bad p)
    (win : ReceiverWindow p.n p.s currentReceiver.degree currentReceiver.scoreCap (spendingFloor (cutoff p))) :
    ReceiverOn p currentReceiver := source_receiver bad currentReceiver win.1 win.2.1 win.2.2

theorem absent_window {p : Input} (bad : Bad p) (absent : ¬ReceiverOn p currentReceiver) :
    ¬ReceiverWindow p.n p.s currentReceiver.degree currentReceiver.scoreCap (spendingFloor (cutoff p)) :=
  fun win=>absent (labelled_source bad win)

/-- Take the boundary quota directly from the head count. The established
boundary library supplies regularity whenever its regime is verified. -/
@[ch_numeric_guard] def FullWindow (q degree shell omitted count : ℕ) : Prop :=
  let t := (degree-1)/q
  3≤q ∧ 2≤t ∧ ¬WeightedSD.NativePressureRegion q t ∧ degree=q*t+1 ∧
    degree*(shell+t-degree)<count*omitted ∧ shell+t≤degree+1

instance {q d s k c} : Decidable (FullWindow q d s k c) := by
  unfold FullWindow WeightedSD.NativePressureRegion; infer_instance

/-- Two marks from independent old arguments must coexist at this one
root. The full head can see the exceptional target and that target returns to a head
which must miss the full head. -/
theorem full_receiver_source {E U q} {law : ReceiverLaw} (witness : law.on E U)
    (free : QFree E U q) (reg : OutEq law.degree E U)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount) :
    ∃v∈U,∃h∈outN E U v,∃g∈outN E U v,∃z∈ball E U v 2 \ ball E U v 1,∃b∈outN E U v,
      (inN E U v).card=law.parents ∧ (ball E U v 2 \ ball E U v 1).card=law.shell ∧
      (∑a∈outN E U v,(law.degree-(inN E U a).card))≤law.charge ∧
      law.degree≤(inN E U h).card ∧ law.missing≤(outN E U v \ inN E U z).card ∧
      E h z=true ∧ E z b=true ∧ (ball E U v 2 \ ball E U v 1)⊆outN E U g ∧
      b≠g ∧ E b g≠true := by
  obtain ⟨cut,two,region,mult,cost,cover⟩ := fit
  obtain ⟨v,vm,parents,sz,price,_,_,h,hm,heavy,z,zm,hz,b,bm,zb,g,gm,full,_,ne,off⟩ :=
    full_at witness free cut reg mult (WeightedSD.boundary_regular_outside_pressure_region cut two region) cost cover
  obtain ⟨zy,miss⟩ := mem_filter.mp zm
  exact ⟨v,vm,h,hm,g,gm,z,zy,b,bm,parents,sz,price,heavy,miss,hz,zb,full,ne,off⟩

attribute [aesop safe forward (immediate := [bad,win]) (rule_sets := [CHGraphFamilies])] labelled_source
attribute [aesop safe forward (immediate := [bad,absent]) (rule_sets := [CHGraphFamilies])] absent_window
-- Replay opens the receiver packet once, in ReceiverMarkedRoot. This theorem stays available to ordinary proofs.
#print axioms labelled_source
#print axioms absent_window
#print axioms full_receiver_source
end LeanCH.BR.LabelledCompromiseRecipe
