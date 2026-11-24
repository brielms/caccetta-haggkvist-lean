import checkpoints.shen_extension.MarkedRepairReplayTest

/-! Replay regression: a recipe that fails must be tried again as soon as a
later rule supplies what it was missing.

In the second case below the recipes `late` and `both` name hypotheses that
do not exist yet, and `gate` names one with the wrong statement. They fail
on the first pass. A typed rule then derives `Enabled`, the trigger recipe
binds `ev`, and `late` and `both` must now succeed. `gate` must stay failed. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
namespace LeanCH.BR.WakeAfterPremiseTest
open CHRuleCatalog CHFamilyWorklist CHContextCatalog MarkedRepairReplayTest

structure Late (p : Input) : Prop where
  source : Enabled p

structure Both (p : Input) : Prop where
  late : Late p

theorem wakes {n r q} {D : CH.Digraph} (_cut : q=CH.ceilDiv n r) {x y : ℕ}
    (_bad : Bad ⟨n,r,D⟩) (_m : Mark ⟨n,r,D⟩ x y) (_ready : Ready ⟨n,r,D⟩ x y)
    (en : x=y → Enabled ⟨n,r,D⟩) : Both ⟨n,r,D⟩ := by
  with_ch_root_catalog
    ch_on_fact hit of Mark => have produced := ruleA hit (by assumption)
    by_cases side : x=y
    · have gate := en side
      ch_on_fact hit of Enabled => have ev := hit
      have late := Late.mk ev
      have both := Both.mk late
      exact both
    · replay_ch_families
      check_goal_count 1
      replay_ch_families
      check_goal_count 1
      assumption

#print axioms wakes
end LeanCH.BR.WakeAfterPremiseTest
