import checkpoints.shen_extension.FifthStripAllCell

/-! Finite checks `FifthStripAll.Cell a` for a = 29 … 34 (degrees s = 36 … 41).
Each component is decided separately with literal orders. -/

set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripAll
open Finset

set_option maxHeartbeats 0 in
theorem cell_29 : Cell 29 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 29), (by decide +kernel : Top 29 2339), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_30 : Cell 30 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 30), (by decide +kernel : Top 30 2478), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 30 2479), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_31 : Cell 31 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 31), (by decide +kernel : Top 31 2621), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_32 : Cell 32 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 32), (by decide +kernel : Top 32 2768), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 32 2769), ?_⟩
  exact Or.inl (by decide)

set_option maxHeartbeats 0 in
theorem cell_33 : Cell 33 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 33), (by decide +kernel : Top 33 2919), ?_⟩
  intro h; exact absurd h (by decide)

set_option maxHeartbeats 0 in
theorem cell_34 : Cell 34 := by
  refine ⟨(by decide +kernel : FifthStripLedger.Checks 34), (by decide +kernel : Top 34 3074), ?_⟩
  intro _
  refine ⟨(by decide +kernel : Top 34 3075), ?_⟩
  exact Or.inl (by decide)

theorem cells_D : ∀ a ∈ Icc 29 34, Cell a := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  interval_cases a
  · exact cell_29
  · exact cell_30
  · exact cell_31
  · exact cell_32
  · exact cell_33
  · exact cell_34

#print axioms cells_D
end LeanCH.BR.FifthStripAll
