import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4LocalGuarded_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4LocalTransport_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4Order28Assembly_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSeven_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

theorem endpoint_four_seven : DotDegreeSeven.Endpoint 4 7 := by
  intro D V hf hne hn hd
  obtain ⟨G,sub,ho⟩ := exists_outEq hd
  have free := qfree_sub sub hf
  apply order28_of_guarded_local_selection free ho (by simpa using hn)
  apply q4_local_selection_to_frames free ho
  intro A av a7 hm
  have lift (x : ℕ) (hg : LocalGuarded G A x) : LocalGuardQ4 G A x := by
    obtain ⟨y,hy,fy⟩ := hg
    obtain ⟨yA,k,kk,w⟩ := mem_ball.mp hy
    exact ⟨y,yA,fy,k,kk,w⟩
  obtain ⟨P,pA,p2,hP⟩ := local_guarded_pair_q4 (free.mono_set av) a7 hm
  refine ⟨P,pA,p2,?_⟩
  intro c hc
  obtain ⟨full,s,hs,a,ha,cs,sa,gs,ga⟩ := hP c hc
  exact ⟨full,s,hs,a,ha,cs,sa,lift s gs,lift a ga⟩

#print axioms endpoint_four_seven
end LeanCH.BR.DotDegreeSevenLow
