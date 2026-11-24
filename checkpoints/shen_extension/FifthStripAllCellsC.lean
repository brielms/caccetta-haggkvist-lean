import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 22 … 28 (degrees s = 29 … 35).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_22 : Cell 22 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 22), (by decide +kernel : Top 22 1478), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 22 1479), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_23 : Cell 23 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 23), (by decide +kernel : Top 23 1589), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_24 : Cell 24 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 24), (by decide +kernel : Top 24 1704), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 24 1705), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_25 : Cell 25 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 25), (by decide +kernel : Top 25 1823), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_26 : Cell 26 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 26), (by decide +kernel : Top 26 1946), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 26 1947), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_27 : Cell 27 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 27), (by decide +kernel : Top 27 2073), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_28 : Cell 28 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 28), (by decide +kernel : Top 28 2204), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 28 2205), ?_⟩
  exact Or.inl (by decide)

theorem cells_C : ∀ a ∈ Icc 22 28, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_22
  · exact cell_23
  · exact cell_24
  · exact cell_25
  · exact cell_26
  · exact cell_27
  · exact cell_28

#print axioms cells_C
end LeanCH.BR.FifthStripAll
