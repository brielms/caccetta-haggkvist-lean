import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenFourEndpoints_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4EndpointVerified_20261121

namespace LeanCH.BR.DotDegreeSeven

/-- With the order-28 exclusion now installed, only the other
three paper endpoints remain to be replayed in this adapter. -/
theorem ch_seven_of_three_endpoints
    (E5 : Endpoint 5 7) (E6 : Endpoint 6 7) (E7 : Endpoint 7 7)
    (n : ℕ) (D : CH.Digraph)
    (hn : 0<n) (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 7) :=
  ch_seven_of_four_endpoints
    ⟨DotDegreeSevenLow.endpoint_four_seven,E5,E6,E7⟩ n D hn loop degree

#print axioms ch_seven_of_three_endpoints
end LeanCH.BR.DotDegreeSeven
