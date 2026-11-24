import checkpoints.shen_extension.CoverageRules

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

/-- Every order and degree whose coverage-map cell is nonzero satisfies the
bound. The cell is a decidable condition in free `n` and `r`: it names the
first generic window (deletion transfer, strip, bank, fragment or prefix
budget) that holds at `q = ⌈n/r⌉`. -/
theorem of_covered_cell {n r : ℕ} (D : CH.Digraph) (order : 0 < n) (positive : 0 < r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (cell : CoverageRules.rule n r (CH.ceilDiv n r) ≠ 0) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) :=
  CoverageRules.ch_of_rule D order positive loopless degree cell

/-- Above the top strip `⌈n/r⌉ > 2r - 6` the bound holds at every degree `r`. -/
theorem above_top_strip {n r : ℕ} (D : CH.Digraph) (order : 0 < n) (positive : 0 < r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (strip : 2*r-6 < CH.ceilDiv n r) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  have region := (remaining_from_run ⟨n, r, D⟩ ⟨order, positive, loopless, degree, missing⟩).2.2
  change 2*r-6 < cutoff ⟨n, r, D⟩ at strip
  dsimp only at region
  rcases region with ⟨_,_,_,_⟩ | ⟨_,_,_⟩ <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Outdegree nine, every order except the 26 listed ones: one instantiation of
`of_covered_cell` (orders up to 108, checked cell by cell) and `above_top_strip`. -/
theorem degree_nine_except {n : ℕ} (D : CH.Digraph) (order : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 9)
    (known : n ∉ [36,44,45,54,59,60,61,62,63,67,68,69,70,71,72,77,78,79,80,81,88,89,90,98,99,108]) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 9) := by
  by_cases small : n < 109
  · have cells : ∀ m < 109, 0 < m →
        m ∉ [36,44,45,54,59,60,61,62,63,67,68,69,70,71,72,77,78,79,80,81,88,89,90,98,99,108] →
        CoverageRules.rule m 9 (CH.ceilDiv m 9) ≠ 0 := by decide +kernel
    exact of_covered_cell D order (by decide) loopless degree (cells n small order known)
  · exact above_top_strip D order (by decide) loopless degree (by unfold CH.ceilDiv; omega)

/-- info: 'LeanCH.Results.above_top_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms above_top_strip
/-- info: 'LeanCH.Results.degree_nine_except' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degree_nine_except
/-- info: 'LeanCH.Results.of_covered_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms of_covered_cell
/-- info: 'LeanCH.Results.degree_one_to_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degree_one_to_eight
/-- info: 'LeanCH.Results.degree_nine_at_34_or_35' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degree_nine_at_34_or_35

end LeanCH.Results
