import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointAssembly_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointNative_20261121

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

/-- The full cutoff-six endpoint: any nonempty host of order at most 42 and
minimum outdegree at least seven has a directed closed walk of length at most six. -/
theorem order42 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (ho : ∀ u∈V, 7≤(outN D V u).card)
    (hn : V.card≤42) (ne : V.Nonempty) : False := by
  obtain ⟨G,sub,eq⟩ := exists_outEq (G:=D) (V:=V) (s:=7) ho
  have free := qfree_sub sub hf
  exact order42_of_first_layer_no_return free eq hn ne
    (fun u hu c2 c3 => no_return_of_ball_two15 free eq hu c2 c3)

#print axioms order42
end LeanCH.BR.DotDegreeSevenQ6
