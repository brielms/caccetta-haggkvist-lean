import checkpoints.shen_extension.CHRuleCatalog
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixQ4EscortTransfer_20261121
namespace LeanCH.BR.DotDegreeSix
open LeanCH.BR.CHRuleCatalog

theorem ch_six_of_endpoint_five (h5 : DotDegreeSeven.Endpoint 5 6) (n : ℕ) (hn : 0 < n)
    (G : CH.Digraph) (hloop : CH.Loopless G n) (hdeg : CH.MinOutdegreeAtLeast G n 6) :
    CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 6) := by
  have hc : CH.ceilDiv n 6 = (n + 5) / 6 := rfl
  by_cases h19 : 19 ≤ n
  · by_cases h25 : 25 ≤ n
    · by_cases h31 : 31 ≤ n
      · by_contra no
        have h := remaining_from_run ⟨n, 6, G⟩ ⟨hn, (show 0 < 6 by decide), hloop, hdeg, no⟩
        simp only [RemainingOrders, cutoff, CH.ceilDiv] at h
        omega
      · have hq : CH.ceilDiv n 6 = 5 := by rw [hc]; omega
        rw [hq]
        exact DotDegreeSeven.from_endpoint h5 hn (by omega) hloop hdeg
    · have hq : CH.ceilDiv n 6 = 4 := by rw [hc]; omega
      rw [hq]
      exact DotDegreeSeven.from_endpoint endpoint_four_six hn (by omega) hloop hdeg
  · by_cases h13 : 13 ≤ n
    · by_contra no
      exact exclusion_from_run ⟨n, 6, G⟩ ⟨hn, (show 0 < 6 by decide), hloop, hdeg, no⟩ .triangle24
        ⟨by simp only [cutoff, CH.ceilDiv]; omega, by show n ≤ 24; omega⟩
    · by_contra no
      have h := remaining_from_run ⟨n, 6, G⟩ ⟨hn, (show 0 < 6 by decide), hloop, hdeg, no⟩
      simp only [RemainingOrders, cutoff, CH.ceilDiv] at h
      omega

#print axioms LeanCH.BR.DotDegreeSix.ch_six_of_endpoint_five

end LeanCH.BR.DotDegreeSix

