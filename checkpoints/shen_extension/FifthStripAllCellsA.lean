import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 4 … 13 (degrees s = 11 … 20).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_4 : Cell 4 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 4), (by decide +kernel : Top 4 164), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_5 : Cell 5 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 5), (by decide +kernel : Top 5 203), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_6 : Cell 6 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 6), (by decide +kernel : Top 6 246), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 6 247), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_7 : Cell 7 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 7), (by decide +kernel : Top 7 293), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_8 : Cell 8 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 8), (by decide +kernel : Top 8 344), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 8 345), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_9 : Cell 9 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 9), (by decide +kernel : Top 9 399), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_10 : Cell 10 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 10), (by decide +kernel : Top 10 458), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 10 459), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_11 : Cell 11 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 11), (by decide +kernel : Top 11 521), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_12 : Cell 12 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 12), (by decide +kernel : Top 12 588), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 12 589), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_13 : Cell 13 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 13), (by decide +kernel : Top 13 659), ?_⟩
  intro h; exact absurd h (by decide)

theorem cells_A : ∀ a ∈ Icc 4 13, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_4
  · exact cell_5
  · exact cell_6
  · exact cell_7
  · exact cell_8
  · exact cell_9
  · exact cell_10
  · exact cell_11
  · exact cell_12
  · exact cell_13

#print axioms cells_A
end LeanCH.BR.FifthStripAll
