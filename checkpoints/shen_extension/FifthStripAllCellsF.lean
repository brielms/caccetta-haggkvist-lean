import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 40 … 43 (degrees s = 47 … 50).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_40 : Cell 40 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 40), (by decide +kernel : Top 40 4088), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 40 4089), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_41 : Cell 41 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 41), (by decide +kernel : Top 41 4271), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 41 4272), ?_⟩
  exact Or.inr ⟨5, by decide, 29, by decide, (by decide +kernel : DenseOK 41 5 29)⟩

set_option maxHeartbeats 0 in
theorem cell_42 : Cell 42 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 42), (by decide +kernel : Top 42 4458), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 42 4459), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_43 : Cell 43 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 43), (by decide +kernel : Top 43 4649), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 43 4650), ?_⟩
  exact Or.inr ⟨5, by decide, 30, by decide, (by decide +kernel : DenseOK 43 5 30)⟩

theorem cells_F : ∀ a ∈ Icc 40 43, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_40
  · exact cell_41
  · exact cell_42
  · exact cell_43

#print axioms cells_F
end LeanCH.BR.FifthStripAll
