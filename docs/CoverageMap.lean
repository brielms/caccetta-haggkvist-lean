import checkpoints.shen_extension.CompromiseQuotaReplay
import checkpoints.shen_extension.SymbolicQuotaSweep

namespace LeanCH.BR.CoverageMapPreview
open CHRuleCatalog ProjectedQuotaTransfer

/-- Each nonzero output names a particular checked exclusion on this input. -/
def rule (n r q : ℕ) : Nat :=
  if r ≤ 8 then 1
  else if q = 3 ∧ r ≤ 9 then 2
  else if QuotaWindow n r q 8 then 3
  else if 2*r-6 < q ∨ (q = 2*r-6 ∧ (11 < r ∨ n < q*r)) then 4
  else if 7 ≤ r ∧ q = 2*r-7 ∧ n+4 ≤ q*r then 5
  else if n < ShellBankFrontier.orderFloor q r then 6
  else if SinkDepthCover.Fits n r q then 7
  else if LowShellCycleSelection.searchedWindow n r q then 8
  else 0

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
  simp [rule, show ¬p.s ≤ 8 by omega, show ¬(cutoff p = 3 ∧ p.s ≤ 9) by
    rintro ⟨h,le⟩; exact (triangle h).not_gt (by omega), quota, strip, fifth,
    Nat.not_lt_of_ge (ShellBankFrontier.native_order p bad),
    SinkDepthCover.exclude bad, LowShellCycleSelection.outside_search bad]

#print axioms zero_on_bad
#eval do
  for r in [1:13] do
    let cells := (List.range 275).map fun i => Char.ofNat (48 + rule (i+1) r (CH.ceilDiv (i+1) r))
    IO.println s!"ROW {r} {String.ofList cells}"
end LeanCH.BR.CoverageMapPreview
