import checkpoints.shen_extension.FragmentTransitionCatalog
import checkpoints.shen_extension.BoundaryQuotaLift
import checkpoints.shen_extension.DistinctReceiverBudget
import checkpoints.shen_extension.SharedBankOrderTransfer
import checkpoints.shen_extension.SingleExitProfile
import checkpoints.shen_extension.RenewedPrefixWitness
import checkpoints.shen_extension.OpposedPowerRows
import checkpoints.shen_extension.CompromiseQuotaReplay
import checkpoints.shen_extension.SymbolicQuotaSweep
import checkpoints.shen_extension.WideQuotaWindow
import checkpoints.shen_extension.ShapeClimb
import checkpoints.shen_extension.ShapeClimbAt
import checkpoints.shen_extension.ShapeClimbAt3
import checkpoints.shen_extension.FourthStripTopAll
import checkpoints.shen_extension.FifthStripAll

/-!
# Generic exclusion rules behind the coverage map

`rule n r q` names the first checked exclusion whose numeric window holds at
order `n`, degree `r` and cutoff `q`. Every window is stated in free `n`, `r`
and `q`; no rule mentions a particular degree beyond the completed prefix
supplied by the capstone's own replay. `zero_on_bad` shows that a
hypothetical counterexample meets none of them, so a nonzero cell is a
Caccetta–Häggkvist bound (`ch_of_rule`).
-/

namespace LeanCH.BR.CoverageRules
open CHRuleCatalog ProjectedQuotaTransfer

/-- Each nonzero output names a particular checked exclusion on this input. The three
climb bounds at the true degree are arguments, so a caller can compute them once per
`(q, r)`; `rule` supplies them. -/
def ruleWith (b3 b b3' : ℕ) (n r q : ℕ) : Nat :=
  if r ≤ 8 then 1
  else if q = 3 ∧ r ≤ 9 then 2
  else if QuotaWindow n r q 8 then 3
  else if 2*r-6 < q ∨ (q = 2*r-6 ∧ (11 < r ∨ n < q*r)) then 4
  else if 7 ≤ r ∧ q = 2*r-7 ∧ n+4 ≤ q*r then 5
  else if 9 ≤ r ∧ q = 2*r-6 ∧ 0 < n ∧ n ≤ q*r then 30
  else if 11 ≤ r ∧ q = 2*r-7 ∧ 0 < n ∧ n+1 ≤ q*r then 31
  else if n < ShellBankFrontier.orderFloor q r then 6
  else if SinkDepthCover.Fits n r q then 7
  else if LowShellCycleSelection.searchedWindow n r q then 8
  else if n < FifthStripLedger.orderFloor q r then 9
  else if PeelWindow n r q projectionFloor then 10
  else if InheritedProfileWindow.Fits n r q completedLibrary.ranks then 11
  else if MixedBankWindow n r q projectionFloor then 12
  else if FragmentScoreEquality.FlatWindow n r q projectionFloor then 13
  else if FragmentScoreEquality.HeadWindow n r q projectionFloor then 14
  else if FragmentScoreEquality.LowerHeadWindow n r q projectionFloor then 15
  else if FragmentScoreEquality.HeadQuota n r q projectionFloor then 16
  else if DistinctReceiverBudget.FifthTransfer n r q then 17
  else if SharedBankOrderTransfer.Window n r q projectionFloor then 18
  else if FragmentScoreEquality.FourthWindow n r q projectionFloor then 19
  else if AvoidedHeadQuota.LiftWindow n r q (AvoidedHeadQuota.spendingFloor q) then 20
  else if AvoidedHeadQuota.BoundaryWindow n r q (AvoidedHeadQuota.spendingFloor q) then 21
  else if SymbolicQuotaSweep.Covers SymbolicQuotaSweep.trianglePrefix.val r q then 22
  else if SingleExitProfile.Window n r q projectionFloor then 23
  else if RecursivePrefixBudget.Window n r q projectionFloor then 24
  else if RenewedPrefixWitness.Window n r q projectionFloor then 25
  else if WideQuotaWindow.Window n r q projectionFloor then 26
  else if ShapeClimb.Window n r q projectionFloor then 27
  else if ShapeClimbAt3.WindowGWith b3 n r q projectionFloor then 28
  else if ShapeClimbAt.WindowGWith b n r q projectionFloor then 29
  else if ShapeClimbAt3.WindowGWith b3' n r q projectionFloor then 32
  else 0

/-- The reach climb up to seven degrees above the closed prefix, used by rule 32 below the
fifth strip (`q ≤ 2r - 8`). -/
def reachBound32 (q r : ℕ) : ℕ :=
  if q + 8 ≤ 2*r then ShapeClimbAt3.guardedBoundAt3 q r projectionFloor 7 else 0

/-- The reach climb up to one degree above the closed prefix, the committed-checker climb
up to two above it, and the reach climb again up to seven above it below the fifth strip
(rule 32; the map evaluates it with `ShapeClimbFast.guardedBoundAt3F`, proved equal). -/
def rule (n r q : ℕ) : Nat :=
  ruleWith (ShapeClimbAt3.guardedBoundAt3 q r projectionFloor 1)
    (ShapeClimbAt.guardedBoundAt q r projectionFloor 2) (reachBound32 q r) n r q

theorem zero_on_bad (p : Input) (bad : Bad p) : rule p.n p.s (cutoff p) = 0 := by
  have floor : 9 ≤ p.s := replay_completed_floor bad
  have triangle : cutoff p = 3 → 10 ≤ p.s := CompromiseQuotaTransfer.any_triangle_degree bad
  have quota : ¬QuotaWindow p.n p.s (cutoff p) 8 := replay_completed_window bad
  have region := (remaining_from_run p bad).2.2
  have strip : ¬(2*p.s-6 < cutoff p ∨ (cutoff p = 2*p.s-6 ∧ (11 < p.s ∨ p.n < cutoff p*p.s))) := by
    rcases region with ⟨_,_,_,top⟩ | ⟨_,_,_⟩
    · rcases top with eq|⟨deg,eq⟩ <;> omega
    · omega
  have fifth : ¬(7 ≤ p.s ∧ cutoff p = 2*p.s-7 ∧ p.n+4 ≤ cutoff p*p.s) :=
    exclusion_from_run p bad .fifthLow
  have reach : ¬ShapeClimbAt3.WindowGWith (ShapeClimbAt3.guardedBoundAt3 (cutoff p) p.s
      projectionFloor 1) p.n p.s (cutoff p) projectionFloor := ShapeClimbAt3.at_completedG bad 1
  have climb : ¬ShapeClimbAt.WindowGWith (ShapeClimbAt.guardedBoundAt (cutoff p) p.s
      projectionFloor 2) p.n p.s (cutoff p) projectionFloor := ShapeClimbAt.at_completedG bad 2
  have reach3 : ¬ShapeClimbAt3.WindowGWith (reachBound32 (cutoff p) p.s) p.n p.s (cutoff p)
      projectionFloor := by
    unfold reachBound32
    split
    · exact ShapeClimbAt3.at_completedG bad 7
    · exact fun ⟨_, _, _, pos, le⟩ => by omega
  have fourth : ¬(9 ≤ p.s ∧ cutoff p = 2*p.s-6 ∧ 0 < p.n ∧ p.n ≤ cutoff p*p.s) :=
    fun ⟨hs, hq, hn, hnq⟩ => bad.missing
      (FourthStripTopAll.cycle_fourth_strip_closed_all hs hq hn hnq bad.loopless bad.degree)
  have fifthTop : ¬(11 ≤ p.s ∧ cutoff p = 2*p.s-7 ∧ 0 < p.n ∧ p.n < cutoff p*p.s) :=
    fun ⟨hs, hq, hn, hnq⟩ => bad.missing
      (FifthStripAll.cycle_fifth_strip_below_top_all hs hq hn hnq bad.loopless bad.degree)
  simp [rule, ruleWith, reach, climb, reach3, fourth, fifthTop, show ¬p.s ≤ 8 by omega, show ¬(cutoff p = 3 ∧ p.s ≤ 9) by
    rintro ⟨h,le⟩; exact (triangle h).not_gt (by omega), quota, strip, fifth,
    Nat.not_lt_of_ge (ShellBankFrontier.native_order p bad),
    SinkDepthCover.exclude bad, LowShellCycleSelection.outside_search bad,
    Nat.not_lt_of_ge (ReachCompletionCatalog.bad_order bad), promoted_peel bad,
    inherited_at_completed bad, promoted_mixed bad, FragmentScoreEquality.replay_at_completed bad,
    FragmentScoreEquality.at_completed bad, FragmentScoreEquality.inherited_at_source bad,
    FragmentScoreEquality.quota_at_completed bad, DistinctReceiverBudget.fifth_transfer bad,
    SharedBankOrderTransfer.from_prefix bad, FragmentScoreEquality.original_exit bad,
    AvoidedHeadQuota.lift_excluded bad (AvoidedHeadQuota.available bad),
    AvoidedHeadQuota.window_excluded bad (AvoidedHeadQuota.available bad),
    SymbolicQuotaSweep.replay_outside bad, SingleExitProfile.at_completed bad,
    RecursivePrefixBudget.at_completed bad, RenewedPrefixWitness.at_completed bad,
    WideQuotaWindow.from_prefix bad, ShapeClimb.at_completed bad]

/-- A nonzero cell of the map is a Caccetta–Häggkvist bound at that order and degree. -/
theorem ch_of_rule {n r : ℕ} (D : CH.Digraph) (order : 0 < n) (positive : 0 < r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (cell : rule n r (CH.ceilDiv n r) ≠ 0) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  exact cell (zero_on_bad ⟨n, r, D⟩ ⟨order, positive, loopless, degree, missing⟩)

#print axioms zero_on_bad
#print axioms ch_of_rule
end LeanCH.BR.CoverageRules
