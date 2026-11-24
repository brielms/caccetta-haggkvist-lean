import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 48 … 51 (degrees s = 55 … 58).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_48 : Cell 48 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 48), (by decide +kernel : Top 48 5664), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 48 5665), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_49 : Cell 49 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 49), (by decide +kernel : Top 49 5879), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 49 5880), ?_⟩
  exact Or.inr ⟨4, by decide, 32, by decide, (by decide +kernel : DenseOK 49 4 32)⟩

set_option maxHeartbeats 0 in
theorem cell_50 : Cell 50 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 50), (by decide +kernel : Top 50 6098), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 50 6099), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_51 : Cell 51 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 51), (by decide +kernel : Top 51 6321), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 51 6322), ?_⟩
  exact Or.inr ⟨4, by decide, 33, by decide, (by decide +kernel : DenseOK 51 4 33)⟩

theorem cells_H : ∀ a ∈ Icc 48 51, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_48
  · exact cell_49
  · exact cell_50
  · exact cell_51

#print axioms cells_H
end LeanCH.BR.FifthStripAll
