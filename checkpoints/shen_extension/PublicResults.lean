import checkpoints.shen_extension.CoverageRules
import checkpoints.shen_extension.DegreeNineReach
import checkpoints.shen_extension.FifthStripAllEven
import checkpoints.shen_extension.WindowSchedule
import checkpoints.shen_extension.TightWindow
import checkpoints.shen_extension.CumulativeDeficitSharp
import checkpoints.shen_extension.SixthStripSharp

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

private theorem le_cut {n r : ℕ} (hr : 0 < r) : n ≤ CH.ceilDiv n r * r := by
  unfold CH.ceilDiv
  have := Nat.lt_div_mul_add (a := n + r - 1) hr
  omega

/-- **Beyond Shen's range at every degree.** Shen proved the bound for
`n ≥ 2r² - 3r + 1`. Here it holds for `n ≥ 2r² - G·r + 1` with `G = 7` at every
degree, `G = 8` from degree 13, `G = 9` from degree 6276, and every `G` with
`424·G² ≤ r`. The range is written without subtraction. -/
theorem beyond_shen {n r G : ℕ} (D : CH.Digraph) (order : 0 < n) (positive : 0 < r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (wide : G ≤ 7 ∨ (G = 8 ∧ 13 ≤ r) ∨ (G = 9 ∧ 6276 ≤ r) ∨ 424*(G*G) ≤ r)
    (range : 2*(r*r)+1 ≤ n+G*r) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  have bad : Bad ⟨n, r, D⟩ := ⟨order, positive, loopless, degree, missing⟩
  obtain ⟨_, six, region⟩ := remaining_from_run ⟨n, r, D⟩ bad
  have cover : n ≤ cutoff ⟨n, r, D⟩ * r := le_cut positive
  have big : 2*r+1 ≤ cutoff ⟨n, r, D⟩ + G := by
    by_contra small
    have less : cutoff ⟨n, r, D⟩ + G ≤ 2*r := by omega
    have scaled := Nat.mul_le_mul_right r less
    rw [Nat.add_mul, Nat.mul_assoc] at scaled
    omega
  have deg : (⟨n, r, D⟩ : Input).s = r := rfl
  have ord : (⟨n, r, D⟩ : Input).n = n := rfl
  dsimp only at six region
  rcases region with ⟨top, low, high, _⟩ | ⟨fifth, sixth, seventh⟩
  · exact missing (FourthStripTopAll.cycle_fourth_strip_closed_all
      (replay_completed_floor bad : 9 ≤ r) top order cover loopless degree)
  · rcases wide with w | ⟨w,d⟩ | ⟨w,d⟩ | w
    · omega
    · exact missing (FifthStripAll.cycle_fifth_strip_closed_every d
        (by omega : cutoff ⟨n, r, D⟩ = 2*r-7) order cover loopless degree)
    · have := sixth (by omega : 59 ≤ r)
      exact missing (SixthStripSharp.cycle_sixth_strip_closed d
        (by omega : cutoff ⟨n, r, D⟩ = 2*r-8) order cover loopless degree)
    · have gap : 2*r - cutoff ⟨n, r, D⟩ + 1 ≤ G := by omega
      have square : (2*r - cutoff ⟨n, r, D⟩ + 1)^2 ≤ G*G := by
        rw [pow_two]
        exact Nat.mul_le_mul gap gap
      exact missing (CumulativeDeficitSharp.cycle_in_window
        (q := cutoff ⟨n, r, D⟩) (h := 2*r - cutoff ⟨n, r, D⟩) (by omega) (by omega)
        ((Nat.mul_le_mul_left _ square).trans w) order cover loopless degree)

/-- Below that range, most of each strip. For any gap `g` with `3g ≤ 2r`, a
digraph of order at most `(2r - g)·r - (g-1)²/2` has a cycle of length at most
`2r - g`. The earlier window needed `3g ≤ r` and `3g²`. -/
theorem strip_window {n r q g : ℕ} (D : CH.Digraph) (order : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (gap : q+g = 2*r) (one : 1 ≤ g) (small : 3*g ≤ 2*r)
    (room : 2*n+(g-1)*(g-1) ≤ 2*(q*r)) :
    CH.HasDirectedCycleAtMost D n q :=
  Window.variable_window' gap one small order room loopless degree

/-- The same with slack about `g²/8`, for gaps with `2g + 2 ≤ r` and `g² ≤ 8r`.
Ball counting cannot go below `⌊g²/8⌋`: see `WindowBreakpoint.prof_two_balls`. -/
theorem strip_window_eighth {n r q g : ℕ} (D : CH.Digraph) (order : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (gap : q+g = 2*r) (small : 2*g+2 ≤ r) (square : g*g ≤ 8*r)
    (room : 8*n+((g+2)*(g+2)+1) ≤ 8*(q*r)) :
    CH.HasDirectedCycleAtMost D n q :=
  Window.variable_window_rec gap small square order room loopless degree

/-- Strip windows with the tight pair. For any gap `g` with `3g ≤ 2r`, a digraph of
order at most `(2r - g)·r - g(g-3)/2` has a cycle of length at most `2r - g`; for even
`g ≥ 4` order `(2r - g)·r + 1 - (g-2)²/2` suffices. -/
theorem strip_window_tight {n r q g : ℕ} (D : CH.Digraph) (order : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (gap : q+g = 2*r) (one : 1 ≤ g) (small : 3*g ≤ 2*r)
    (room : 2*n+g*(g-3) ≤ 2*(q*r) ∨ (g%2 = 0 ∧ 4 ≤ g ∧ 2*n+(g-2)*(g-2) ≤ 2*(q*r)+2)) :
    CH.HasDirectedCycleAtMost D n q :=
  TightWindow.variable_window_tight gap one small order room loopless degree

/-- The recursive window with the tight pair: slack `g(g+4)/8`, for gaps with
`2g + 2 ≤ r` and `g² ≤ 8r`. -/
theorem strip_window_eighth_tight {n r q g : ℕ} (D : CH.Digraph) (order : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (gap : q+g = 2*r) (small : 2*g+2 ≤ r) (square : g*g ≤ 8*r)
    (room : 8*n+g*(g+4) ≤ 8*(q*r)+7) :
    CH.HasDirectedCycleAtMost D n q :=
  TightWindow.variable_window_rec_tight gap small square order room loopless degree

/-- The collar rule on the row `r = q + 1`: a directed cycle of length at most `q` whenever
`n ≤ CollarRule.collarBound q` (loop collar, collar dip and the thin-root ledger). -/
theorem collar_row {n q : ℕ} (D : CH.Digraph) (order : 0 < n) (loopless : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n (q+1)) (small : n ≤ CollarRule.collarBound q) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra missing
  have free : BRq2.QFree D (Finset.range n) q := BRq2.qfree_of_noShort loopless missing
  have deg : ∀ v ∈ Finset.range n, q + 1 ≤ (BRq3.outN D (Finset.range n) v).card :=
    fun v hv => Compose.FloorSix.out_card degree (Finset.mem_range.mp hv)
  have := CollarRule.collarBound_sound free ⟨0, Finset.mem_range.mpr order⟩ deg
  rw [Finset.card_range] at this
  omega

/-- The flat rule on the row `r = q`: a directed cycle of length at most `q` whenever
`n ≤ FlatRule.flatBound q` (the flat dip at the cutoff in the seeded reach climb). -/
theorem flat_row {n q : ℕ} (D : CH.Digraph) (order : 0 < n) (loopless : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n q) (small : n ≤ FlatRule.flatBound q) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra missing
  have free : BRq2.QFree D (Finset.range n) q := BRq2.qfree_of_noShort loopless missing
  have deg : ∀ v ∈ Finset.range n, q ≤ (BRq3.outN D (Finset.range n) v).card :=
    fun v hv => Compose.FloorSix.out_card degree (Finset.mem_range.mp hv)
  have := FlatRule.flatBound_sound free ⟨0, Finset.mem_range.mpr order⟩ deg
  rw [Finset.card_range] at this
  omega

/-- The tight rule on the row `r = q + 2`: a directed cycle of length at most `q` whenever
`n ≤ TightRule2.tightBound2 q` (the second collar with the floors of tight and loose roots). -/
theorem tight_row {n q : ℕ} (D : CH.Digraph) (order : 0 < n) (loopless : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n (q+2)) (small : n ≤ TightRule2.tightBound2 q) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra missing
  have free : BRq2.QFree D (Finset.range n) q := BRq2.qfree_of_noShort loopless missing
  have deg : ∀ v ∈ Finset.range n, q + 2 ≤ (BRq3.outN D (Finset.range n) v).card :=
    fun v hv => Compose.FloorSix.out_card degree (Finset.mem_range.mp hv)
  have := TightRule2.tightBound2_sound free ⟨0, Finset.mem_range.mpr order⟩ deg
  rw [Finset.card_range] at this
  omega

/-- The thin-root count at any degree `r`: a directed cycle of length at most `q` whenever
`n ≤ ThinRule.thinBound q r` (zero unless `4 ≤ q` and `r ≤ 2q - 1`). -/
theorem thin_row {n q r : ℕ} (D : CH.Digraph) (order : 0 < n) (loopless : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r) (small : n ≤ ThinRule.thinBound q r) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra missing
  have free : BRq2.QFree D (Finset.range n) q := BRq2.qfree_of_noShort loopless missing
  have deg : ∀ v ∈ Finset.range n, r ≤ (BRq3.outN D (Finset.range n) v).card :=
    fun v hv => Compose.FloorSix.out_card degree (Finset.mem_range.mp hv)
  have := ThinRule.thinBound_sound free ⟨0, Finset.mem_range.mpr order⟩ deg
  rw [Finset.card_range] at this
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 0 in
/-- Outdegree nine, every order except the 5 listed ones: one instantiation of
`of_covered_cell` (orders up to 108, checked cell by cell) and `above_top_strip`. The seeded
reach bound and the collar, flat, tight and thin bounds enter the cell check as the literals
`DegreeNineReach.nineReach`, `DegreeNineReach.nineCollar`, `DegreeNineReach.nineFlat`,
`DegreeNineReach.nineTight`, `DegreeNineReach.nineThin`, proved lower bounds
(`CoverageRules.rule_ne_zero`). -/
theorem degree_nine_except {n : ℕ} (D : CH.Digraph) (order : 0 < n)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 9)
    (known : n ∉ [36,54,62,63,72]) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 9) := by
  by_cases small : n < 109
  · -- The cheap cells first, so that rules 1–32 are evaluated only where none of them applies.
    have cells : ∀ m < 109, 0 < m → m ∉ [36,54,62,63,72] →
        CoverageRules.collarCell (DegreeNineReach.nineCollar (CH.ceilDiv m 9)) m 9
            (CH.ceilDiv m 9) ≠ 0 ∨
          CoverageRules.flatCell (DegreeNineReach.nineFlat (CH.ceilDiv m 9)) m 9
            (CH.ceilDiv m 9) ≠ 0 ∨
          CoverageRules.tightCell (DegreeNineReach.nineTight (CH.ceilDiv m 9)) m 9
            (CH.ceilDiv m 9) ≠ 0 ∨
          CoverageRules.thinCell (DegreeNineReach.nineThin (CH.ceilDiv m 9)) m 9
            (CH.ceilDiv m 9) ≠ 0 ∨
          CoverageRules.nineFiveCell m 9 (CH.ceilDiv m 9) ≠ 0 ∨
          CoverageRules.ruleWith (DegreeNineReach.nineReach (CH.ceilDiv m 9)) 0 0 m 9
            (CH.ceilDiv m 9) ≠ 0 := by decide +kernel
    exact of_covered_cell D order (by decide) loopless degree
      (CoverageRules.rule_ne_zero (DegreeNineReach.nineReach_le _) (Nat.zero_le _)
        (Nat.zero_le _) (DegreeNineReach.nineCollar_le _) (DegreeNineReach.nineFlat_le _)
        (DegreeNineReach.nineTight_le _) (DegreeNineReach.nineThin_le _)
        (by
          rcases cells n small order known with c | c | c | c | c | c
          exacts [.inr (.inl c), .inr (.inr (.inl c)), .inr (.inr (.inr (.inl c))),
            .inr (.inr (.inr (.inr (.inl c)))), .inr (.inr (.inr (.inr (.inr c)))), .inl c]))
  · exact above_top_strip D order (by decide) loopless degree (by unfold CH.ceilDiv; omega)

/-- info: 'LeanCH.Results.beyond_shen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms beyond_shen
/-- info: 'LeanCH.Results.strip_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strip_window
/-- info: 'LeanCH.Results.strip_window_eighth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strip_window_eighth
/-- info: 'LeanCH.Results.strip_window_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strip_window_tight
/-- info: 'LeanCH.Results.strip_window_eighth_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strip_window_eighth_tight
/-- info: 'LeanCH.Results.above_top_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms above_top_strip
/-- info: 'LeanCH.Results.collar_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collar_row
/-- info: 'LeanCH.Results.flat_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_row
/-- info: 'LeanCH.Results.tight_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tight_row
/-- info: 'LeanCH.Results.thin_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thin_row
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
