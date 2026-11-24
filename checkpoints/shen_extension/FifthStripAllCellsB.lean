import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 14 … 21 (degrees s = 21 … 28).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_14 : Cell 14 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 14), (by decide +kernel : Top 14 734), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 14 735), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_15 : Cell 15 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 15), (by decide +kernel : Top 15 813), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_16 : Cell 16 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 16), (by decide +kernel : Top 16 896), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 16 897), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_17 : Cell 17 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 17), (by decide +kernel : Top 17 983), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_18 : Cell 18 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 18), (by decide +kernel : Top 18 1074), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 18 1075), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_19 : Cell 19 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 19), (by decide +kernel : Top 19 1169), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_20 : Cell 20 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 20), (by decide +kernel : Top 20 1268), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 20 1269), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_21 : Cell 21 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 21), (by decide +kernel : Top 21 1371), ?_⟩
  intro h; exact absurd h (by decide)

theorem cells_B : ∀ a ∈ Icc 14 21, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_14
  · exact cell_15
  · exact cell_16
  · exact cell_17
  · exact cell_18
  · exact cell_19
  · exact cell_20
  · exact cell_21

#print axioms cells_B
end LeanCH.BR.FifthStripAll
