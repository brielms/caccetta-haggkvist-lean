import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 35 … 39 (degrees s = 42 … 46).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_35 : Cell 35 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 35), (by decide +kernel : Top 35 3233), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_36 : Cell 36 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 36), (by decide +kernel : Top 36 3396), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 36 3397), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_37 : Cell 37 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 37), (by decide +kernel : Top 37 3563), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 37 3564), ?_⟩
  exact Or.inr ⟨5, by decide, 27, by decide, (by decide +kernel : DenseOK 37 5 27)⟩

set_option maxHeartbeats 0 in
theorem cell_38 : Cell 38 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 38), (by decide +kernel : Top 38 3734), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 38 3735), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_39 : Cell 39 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 39), (by decide +kernel : Top 39 3909), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 39 3910), ?_⟩
  exact Or.inr ⟨5, by decide, 28, by decide, (by decide +kernel : DenseOK 39 5 28)⟩

theorem cells_E : ∀ a ∈ Icc 35 39, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_35
  · exact cell_36
  · exact cell_37
  · exact cell_38
  · exact cell_39

#print axioms cells_E
end LeanCH.BR.FifthStripAll
