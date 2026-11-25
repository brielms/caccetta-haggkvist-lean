import checkpoints.shen_extension.ShapeClimbMono
import checkpoints.shen_extension.CollarRule
import checkpoints.shen_extension.FlatRule

/-!
# The seeded reach bound at degree nine, as literals

`PublicResults.degree_nine_except` checks 108 cells in the kernel. The seeded reach bound
`ShapeClimbMono.guardedBoundM q 9 projectionFloor 1` is the same number for every order of one
cutoff, so it is checked here once per cutoff, through the pruned evaluation, and handed on as
the literal `nineReach q`. Only the cutoffs 7 to 11 have a cell that needs it.
The collar bound `CollarRule.collarBound` is needed at cutoff 8 only (`nineCollar`), the flat
bound `FlatRule.flatBound` at cutoff 9 only (`nineFlat`).
-/

namespace LeanCH.BR.DegreeNineReach
open ProjectedQuotaTransfer

/-- A lower bound for the seeded reach bound at degree nine; zero where no cell needs it. -/
def nineReach : ℕ → ℕ
  | 7 => 59
  | 8 => 67
  | 9 => 77
  | 10 => 90
  | 11 => 99
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_7 : 59 ≤ ShapeClimbMono.guardedBoundMF 7 9 projectionFloor 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_8 : 67 ≤ ShapeClimbMono.guardedBoundMF 8 9 projectionFloor 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_9 : 77 ≤ ShapeClimbMono.guardedBoundMF 9 9 projectionFloor 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_10 : 90 ≤ ShapeClimbMono.guardedBoundMF 10 9 projectionFloor 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_11 : 99 ≤ ShapeClimbMono.guardedBoundMF 11 9 projectionFloor 1 := by decide +kernel

theorem nineReach_le (q : ℕ) :
    nineReach q ≤ ShapeClimbMono.guardedBoundM q 9 projectionFloor 1 := by
  rw [← ShapeClimbMono.guardedBoundMF_eq]
  unfold nineReach
  split
  · exact reach_7
  · exact reach_8
  · exact reach_9
  · exact reach_10
  · exact reach_11
  · exact Nat.zero_le _

/-- A lower bound for the collar bound at degree nine; zero where no cell needs it. -/
def nineCollar : ℕ → ℕ
  | 8 => 69
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem collar_8 : 69 ≤ CollarRule.collarBoundF 8 := by decide +kernel

theorem nineCollar_le (q : ℕ) : nineCollar q ≤ CollarRule.collarBound q := by
  rw [← CollarRule.collarBoundF_eq]
  unfold nineCollar
  split
  · exact collar_8
  · exact Nat.zero_le _

/-- A lower bound for the flat bound at degree nine; zero where no cell needs it. -/
def nineFlat : ℕ → ℕ
  | 9 => 79
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem flat_9 : 79 ≤ FlatRule.flatBoundF 9 := by decide +kernel

theorem nineFlat_le (q : ℕ) : nineFlat q ≤ FlatRule.flatBound q := by
  rw [← FlatRule.flatBoundF_eq]
  unfold nineFlat
  split
  · exact flat_9
  · exact Nat.zero_le _

#print axioms nineReach_le
#print axioms nineCollar_le
#print axioms nineFlat_le
end LeanCH.BR.DegreeNineReach
