import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7PackedEndpoint_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssemblyFinal_20261121

namespace LeanCH.BR.DotDegreeSeven

/-- Caccetta–Häggkvist at fixed minimum outdegree seven, for every positive order. -/
theorem ch_degree_seven (n : ℕ) (D : CH.Digraph) (hn : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 7) :=
  ch_seven_of_four_endpoints
    ⟨DotDegreeSevenLow.endpoint_four_seven, DotDegreeSevenLow.endpoint_five_seven,
      endpoint_six_seven, DotDegreeSevenQ7.packed_endpoint_seven_seven⟩
    n D hn loopless degree

#print axioms DotDegreeSevenLow.endpoint_four_seven
#print axioms DotDegreeSevenLow.endpoint_five_seven
#print axioms endpoint_six_seven
#print axioms DotDegreeSevenQ7.packed_endpoint_seven_seven
#print axioms ch_degree_seven
end LeanCH.BR.DotDegreeSeven
