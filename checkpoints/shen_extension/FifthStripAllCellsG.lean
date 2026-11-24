import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 44 … 47 (degrees s = 51 … 54).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_44 : Cell 44 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 44), (by decide +kernel : Top 44 4844), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 44 4845), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_45 : Cell 45 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 45), (by decide +kernel : Top 45 5043), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 45 5044), ?_⟩
  exact Or.inr ⟨4, by decide, 30, by decide, (by decide +kernel : DenseOK 45 4 30)⟩

set_option maxHeartbeats 0 in
theorem cell_46 : Cell 46 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 46), (by decide +kernel : Top 46 5246), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 46 5247), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_47 : Cell 47 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 47), (by decide +kernel : Top 47 5453), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 47 5454), ?_⟩
  exact Or.inr ⟨4, by decide, 31, by decide, (by decide +kernel : DenseOK 47 4 31)⟩

theorem cells_G : ∀ a ∈ Icc 44 47, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_44
  · exact cell_45
  · exact cell_46
  · exact cell_47

#print axioms cells_G
end LeanCH.BR.FifthStripAll
