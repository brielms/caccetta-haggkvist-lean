import checkpoints.shen_extension.CHForwardCatalog
import checkpoints.shen_extension.CHFamilyDeclarations
import checkpoints.shen_extension.LateTargetReach

namespace LeanCH.BR.HeadSlotRules
open Finset BRq2 BRq3

/-- A row with r heads and at most z outside T has at least r-z heads
in T. The output names the entire actual head set on this carrier. -/
@[aesop safe forward (immediate := [degree,outside]) (rule_sets := [CHGraphFamilies])]
theorem retained {D : CH.Digraph} {V T : Finset ℕ} {a r z : ℕ}
    (degree : r≤(outN D V a).card) (outside : (outN D V a\T).card≤z) :
    r-z≤((outN D V a)∩T).card := by
  have count := card_sdiff_add_card_inter (outN D V a) T
  omega

attribute [aesop safe forward (immediate := [first,choice,targets,need])
  (rule_sets := [CHGraphFamilies])] SATBoundaryPilot.late_target
ch_family_split_result SATBoundaryPilot.late_target

#print axioms retained
end LeanCH.BR.HeadSlotRules
