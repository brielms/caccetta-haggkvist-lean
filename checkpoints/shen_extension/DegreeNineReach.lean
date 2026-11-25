import checkpoints.shen_extension.ShapeClimbMono

/-!
# The seeded reach bound at degree nine, as literals

`PublicResults.degree_nine_except` checks 108 cells in the kernel. The seeded reach bound
`ShapeClimbMono.guardedBoundM q 9 projectionFloor 1` is the same number for every order of one
cutoff, so it is checked here once per cutoff, through the pruned evaluation, and handed on as
the literal `nineReach q`. Only the cutoffs 7 to 11 have a cell that needs it.
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

#print axioms nineReach_le
end LeanCH.BR.DegreeNineReach
