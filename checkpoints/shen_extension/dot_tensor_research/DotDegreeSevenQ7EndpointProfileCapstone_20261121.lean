import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileClose_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7GrowthProofSingleton_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenTwoEndpoints_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssemblyFinal_20261121

namespace LeanCH.BR.DotDegreeSeven
open Finset BRq2 BRq3 BR45 BRsGen

/-- Native endpoint theorem, including degree thinning. -/
theorem endpoint_seven_seven : Endpoint 7 7 := by
  intro D V hf hn hcard hm
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  have free := qfree_sub sub hf
  have ge := DotDegreeSevenQ7.card_ge_fifty_of_floor free ho hn
    (fun _ hv => DotDegreeSevenQ7GrowthProof.floor_four free ho hv)
  omega

/-- Literal Caccetta–Häggkvist for minimum outdegree seven, at all orders. -/
theorem ch_seven (n : ℕ) (D : CH.Digraph) (hn : 0<n)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 7) :=
  ch_seven_of_two_endpoints DotDegreeSevenLow.endpoint_five_seven endpoint_seven_seven n D hn loop degree

#print axioms endpoint_seven_seven
#print axioms ch_seven
end LeanCH.BR.DotDegreeSeven
