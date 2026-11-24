import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenThreeEndpoints_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointFinal_20261121

namespace LeanCH.BR.DotDegreeSeven

theorem endpoint_six_seven : Endpoint 6 7 := by
  intro D V hf ne hcard deg
  exact DotDegreeSevenQ6.order42 hf deg (by omega) ne

/-- Cutoffs four and six supplied by native endpoint proofs. -/
theorem ch_seven_of_two_endpoints
    (E5 : Endpoint 5 7) (E7 : Endpoint 7 7)
    (n : ℕ) (D : CH.Digraph)
    (hn : 0<n) (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 7) :=
  ch_seven_of_three_endpoints E5 endpoint_six_seven E7 n D hn loop degree

#print axioms endpoint_six_seven
#print axioms ch_seven_of_two_endpoints
end LeanCH.BR.DotDegreeSeven
