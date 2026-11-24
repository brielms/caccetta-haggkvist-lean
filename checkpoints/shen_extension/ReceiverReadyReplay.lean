import checkpoints.shen_extension.ReceiverBankReplay

namespace LeanCH.BR.LabelledCompromiseRecipe
open CHRuleCatalog BRq2 BRq3 AvoidedHeadQuota

/-- Public conditionals let a numerical or symbolic child supply its
own certificates. The worklist returns each computed premise to the
ordinary labelled rules. -/
theorem ready_source {p : Input} (bad : Bad p) :
    ReceiverWindow p.n p.s currentReceiver.degree currentReceiver.scoreCap (spendingFloor (cutoff p)) →
    ReceiverOn p currentReceiver := labelled_source bad

theorem ready_full {D U q} {law : ReceiverLaw} (witness : law.on D U)
    (free : QFree D U q) (reg : OutEq law.degree D U) :
    FullWindow q law.degree law.shell law.missing law.lowerCount →
      ∃v∈U,∃g∈outN D U v,(ball D U v 2 \ ball D U v 1)⊆outN D U g := by
  intro fit
  obtain ⟨v,vm,_,_,g,gm,_,_,_,_,_,_,_,_,_,_,_,full,_,_⟩ := full_receiver_source witness free reg fit
  exact ⟨v,vm,g,gm,full⟩

@[ch_numeric_guard] def UnitShell (q d s : ℕ) : Prop := s+(d-1)/q=d+1
instance {q d s} : Decidable (UnitShell q d s) := by unfold UnitShell; infer_instance

theorem ready_unit {D U q} {law : ReceiverLaw} (_witness : law.on D U)
    (_fit : FullWindow q law.degree law.shell law.missing law.lowerCount) :
    UnitShell q law.degree law.shell → law.shell+(law.degree-1)/q=law.degree+1 := id

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] ready_source
-- Replay opens the receiver packet once, in ReceiverMarkedRoot. This theorem stays available to ordinary proofs.
attribute [aesop safe forward (immediate := [_witness,_fit]) (rule_sets := [CHGraphFamilies])] ready_unit
#print axioms ready_source
#print axioms ready_full
#print axioms ready_unit
end LeanCH.BR.LabelledCompromiseRecipe
