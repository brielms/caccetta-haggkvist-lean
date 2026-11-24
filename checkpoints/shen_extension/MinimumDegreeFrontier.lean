import checkpoints.shen_extension.MinimalPowerDescent
import checkpoints.shen_extension.RetainedRadiusLayers

namespace LeanCH.BR.MinimumDegreeFrontier
open CHRuleCatalog BypassDegreeDescent

/-- Numerical projection of the two generic rules on a selected least input.
    The first projection is unconditional on minimality. -/
@[aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
theorem direct {p : Input} (bad : Bad p) : p.s=8 →
    (cutoff p=5 ∧ 39≤p.n ∧ p.n≤40) ∨ (cutoff p=6 ∧ 45≤p.n ∧ p.n≤48) ∨
    (cutoff p=7 ∧ 52≤p.n ∧ p.n≤56) ∨ (cutoff p=8 ∧ p.n=64) ∨
    (cutoff p=9 ∧ p.n=72) ∨ (cutoff p=10 ∧ p.n=80) := by
  intro eight
  have prior := GuardedDegreeFrontier.any_input bad eight
  have floor := RetainedRadiusLayers.direct_window bad
  unfold GuardedDegreeFrontier.Direct at prior
  omega

@[aesop safe forward (immediate := [bad,least,reduced,loss]) (rule_sets := [CHGraphFamilies])]
theorem terminal {p : Input} (bad : Bad p) (least : MinimalChild p)
    (reduced : ReducedCutoff p.n p.s) (loss : ¬OneLossCutoffDescent.Window p.n p.s (cutoff p)) :
    p.s=8 → (cutoff p=5 ∧ 39≤p.n ∧ p.n≤40) ∨ (cutoff p=6 ∧ 46≤p.n ∧ p.n≤48) ∨
      (cutoff p=7 ∧ 52≤p.n ∧ p.n≤56) := by
  intro eight
  have prior := GuardedDegreeFrontier.any_recursive_input bad reduced loss eight
  have guard := MinimalPowerDescent.no_triple bad least
  unfold GuardedDegreeFrontier.Terminal at prior
  omega

#print axioms direct
#print axioms terminal
end LeanCH.BR.MinimumDegreeFrontier
