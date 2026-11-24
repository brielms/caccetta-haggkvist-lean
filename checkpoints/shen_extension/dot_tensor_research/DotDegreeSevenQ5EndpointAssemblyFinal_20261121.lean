import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssembly_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactEndpoint_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSeven_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- Degree-seven sources at the cutoff-five endpoint fail in both possible
radius-two branches. The edits to obtain exact degree preserve freeness. -/
theorem endpoint_five_seven : DotDegreeSeven.Endpoint 5 7 := by
  intro D V hf _ hn hd
  obtain ⟨G,sub,ho⟩ := exists_outEq hd
  have free := qfree_sub sub hf
  exact exact_endpoint_all_large_impossible free ho hn (no_short_at35 free ho hn)

/-- Equivalent order floor, including orders below the endpoint. -/
theorem five_free_ge36 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v∈V,7≤(outN D V v).card) (hne : V.Nonempty) :
    36≤V.card := by
  have lo := five_free_ge35 hf hm hne
  by_contra! hi
  exact endpoint_five_seven D V hf hne (by omega) hm

#print axioms endpoint_five_seven
#print axioms five_free_ge36
end LeanCH.BR.DotDegreeSevenLow
