import checkpoints.shen_extension.SharedBankOrderTransfer

namespace LeanCH.Results

open BR CHRuleCatalog ProjectedQuotaTransfer

/-- The Caccetta–Häggkvist cycle bound for every positive order at degrees one through eight. -/
theorem degree_one_to_eight {n r : ℕ} (D : CH.Digraph) (order : 0 < n)
    (positive : 1 ≤ r) (upper : r ≤ 8) (loopless : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  have bad : Bad ⟨n, r, D⟩ := ⟨order, positive, loopless, degree, missing⟩
  have lower : 9 ≤ r := replay_completed_floor bad
  omega

/-- The same shared-bank rule gives the four-cycle bound at each of the two advertised orders. -/
theorem degree_nine_at_34_or_35 {n : ℕ} (D : CH.Digraph) (size : n = 34 ∨ n = 35)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 9) :
    CH.HasDirectedCycleAtMost D n 4 := by
  have q : CH.ceilDiv n 9 = 4 := by rcases size with h | h <;> subst n <;> decide
  by_contra missing
  have bad : Bad ⟨n, 9, D⟩ :=
    ⟨by change 0 < n; omega, by change 0 < 9; decide, loopless, degree,
      by simpa [cutoff, q] using missing⟩
  apply SharedBankOrderTransfer.from_prefix bad
  change SharedBankOrderTransfer.Window n 9 (CH.ceilDiv n 9) projectionFloor
  rw [q]
  rcases size with h | h <;> subst n <;> decide

/-- info: 'LeanCH.Results.degree_one_to_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degree_one_to_eight
/-- info: 'LeanCH.Results.degree_nine_at_34_or_35' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degree_nine_at_34_or_35

end LeanCH.Results
