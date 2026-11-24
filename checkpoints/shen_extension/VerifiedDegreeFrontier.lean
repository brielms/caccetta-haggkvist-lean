import checkpoints.shen_extension.SevenDegreeCapstoneEntry
import checkpoints.shen_extension.TightBankDegreeTransfer
import checkpoints.shen_extension.dot_tensor_research.DiagonalEight

namespace LeanCH.BR.VerifiedDegreeFrontier

/-- The numerical premises inherited by every subsequent repair at this input. -/
structure Remaining (n r q : ℕ) : Prop where
  floor : 8 ≤ r
  pastSeven : 7*q+r < n+7
  eightOrder : q=8 → 64≤n
  coverBudget : ∀ d k, DotDegreeSeven.Endpoint q d → 0<q*d →
    n=q*d+k → d+k=r+1 → n.choose k ≤ n*r.choose k

theorem cycle_or_remaining {n r : ℕ} (D : CH.Digraph) (hn : 0<n) (six : 6≤r)
    (loopless : CH.Loopless D n) (minimum : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) ∨ Remaining n r (CH.ceilDiv n r) := by
  classical
  let q := CH.ceilDiv n r
  change CH.HasDirectedCycleAtMost D n q ∨ Remaining n r q
  by_cases low : r=6
  · subst r
    exact Or.inl (DotDegreeSix.ch_six n hn D loopless minimum)
  by_cases seven : r=7
  · subst r
    exact Or.inl (DotDegreeSeven.ch_degree_seven n D hn loopless minimum)
  have floor : 8≤r := by omega
  have qpos : 0<q := by dsimp [q,CH.ceilDiv]; exact Nat.div_pos (by omega) (by omega)
  by_cases window : n+7≤7*q+r
  · exact Or.inl (SevenDegreeCapstoneEntry.seven_window hn qpos (by omega) window loopless minimum)
  by_cases eight : q=8 ∧ n≤63
  · left
    rw [eight.1]
    exact DiagonalEight.cycle_at_most_eight D hn eight.2 loopless
      (Triangle24.minOut_mono floor minimum)
  by_cases banks : ∃ d k, DotDegreeSeven.Endpoint q d ∧ 0<q*d ∧ n=q*d+k ∧
      d+k=r+1 ∧ n*r.choose k<n.choose k
  · obtain ⟨d,k,endpoint,positive,size,cost,bill⟩ := banks
    exact Or.inl (TightBankDegreeTransfer.cycle_of_count D endpoint positive size cost bill loopless minimum)
  right
  refine ⟨floor,Nat.lt_of_not_ge window,?_,?_⟩
  · intro cut
    exact Nat.lt_of_not_ge (fun small => eight ⟨cut,small⟩)
  · intro d k endpoint positive size cost
    exact Nat.le_of_not_gt (fun violation => banks ⟨d,k,endpoint,positive,size,cost,violation⟩)

theorem Remaining.excludes_nine_38 {n r : ℕ} (h : Remaining n r (CH.ceilDiv n r))
    (degree : r=9) : n≠38 := by
  rintro rfl
  subst r
  have bad := h.coverBudget 7 3 DotDegreeSevenLow.endpoint_five_seven
    (by decide) (by decide) (by decide)
  exact (by decide : ¬ ((38:ℕ).choose 3 ≤ 38*(9:ℕ).choose 3)) bad

#print axioms cycle_or_remaining
#print axioms Remaining.excludes_nine_38
end LeanCH.BR.VerifiedDegreeFrontier
