import checkpoints.shen_extension.ProjectedQuotaTransfer
import checkpoints.shen_extension.MinimumDegreeFrontier
import checkpoints.shen_extension.ShellBankFrontier
import checkpoints.shen_extension.SinkDepthCover
import checkpoints.shen_extension.SymbolicQuotaSweep

namespace LeanCH.BR.ProjectedQuotaTransfer
open CHRuleCatalog LowShellCycleSelection

/-- Check a finite disjunction of cutoff and order ranges against the registered
order floor and the two computable exclusion windows. All endpoints come
from the producer's conclusion. A surviving order leaves a Lean goal. -/
macro "check_quota_ranges" p:ident bad:ident degree:ident region:ident : tactic =>
  `(tactic| (
    have floorBound := ShellBankFrontier.native_order $p $bad
    have sinkBound := SinkDepthCover.exclude $bad
    have contactBound := outside_search $bad
    have degreeEq := $degree
    have alternatives := $region
    rw [degreeEq] at floorBound sinkBound contactBound
    generalize orderEq : Input.n $p = order at alternatives floorBound sinkBound contactBound
    repeat' (have isChoice : _ ∨ _ := alternatives; clear isChoice; rcases alternatives with alternatives | alternatives)
    all_goals obtain ⟨cut,extent⟩ := alternatives
    all_goals rw [cut] at floorBound sinkBound contactBound
    all_goals clear orderEq
    all_goals try (have pair : _ ∧ _ := extent; clear pair; obtain ⟨lower,upper⟩ := extent)
    all_goals first | subst order | interval_cases order
    all_goals first | (revert floorBound; decide) | exact sinkBound (by decide) | exact contactBound (by decide)
  ))

/-- Older downstream interface types retain this elaborated index. -/
private abbrev projectionIndex {d : ℕ} {P : Input → Prop} (_ : ∀{p : Input},Bad p → p.s=d → P p) := d

private abbrev literalDegree {d : ℕ} (_ : ∀ (n : ℕ) (D : CH.Digraph), 0 < n →
    CH.Loopless D n → CH.MinOutdegreeAtLeast D n d →
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n d)) := d

/-- Certify the successor of the previously solved degree by checking the
symbolic cutoff sweep. The implicit degree comes from the prior certificate;
the proof at the successor uses only the sweep and its triangle bound. -/
theorem from_recorded_projection : ClosedQuota (literalDegree DotDegreeSeven.ch_degree_seven + 1) :=
  SymbolicQuotaSweep.certify (fun p bad _ => SymbolicQuotaSweep.trianglePrefix.property p bad)
    (by decide) (by decide)

private abbrev quotaIndex {d : ℕ} (_ : ClosedQuota d) := d

/-- On each actual input, including descendants, use the completed
projection with the generic quota-transfer rule. -/
theorem replay_completed_quota {p : Input} (bad : Bad p) :
    quotaIndex from_recorded_projection≤p.s →
      quotaIndex from_recorded_projection*cutoff p+p.s<p.n+quotaIndex from_recorded_projection :=
  extend_quota bad from_recorded_projection

theorem replay_completed_floor {p : Input} (bad : Bad p) :
    quotaIndex from_recorded_projection+1≤p.s := by
  have lower := (remaining_from_run p bad).2.1
  rcases VerifiedDegreeFrontier.cycle_or_remaining p.D bad.order lower bad.loopless bad.degree with closed|prior
  · exact (bad.missing closed).elim
  · exact next_degree bad from_recorded_projection prior.floor

theorem replay_completed_window {p : Input} (bad : Bad p) :
    ¬QuotaWindow p.n p.s (cutoff p) (quotaIndex from_recorded_projection) :=
  quota_window_missed bad from_recorded_projection

/-- This guard only reads the degree. It can close a symbolic order. -/
@[ch_numeric_guard] def BelowQuota (r floor : ℕ) := r<floor
instance {r floor} : Decidable (BelowQuota r floor) := by unfold BelowQuota; infer_instance

theorem replay_completed_prefix {p : Input} (bad : Bad p) :
    ¬BelowQuota p.s (quotaIndex from_recorded_projection+1) :=
  Nat.not_lt_of_ge (replay_completed_floor bad)

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] replay_completed_quota replay_completed_floor replay_completed_window replay_completed_prefix
#print axioms replay_completed_prefix
#print axioms replay_completed_floor
#print axioms replay_completed_window
#print axioms from_recorded_projection
#print axioms replay_completed_quota
end LeanCH.BR.ProjectedQuotaTransfer
