import checkpoints.shen_extension.FifthStripAllCellsA
import checkpoints.shen_extension.FifthStripAllCellsB
import checkpoints.shen_extension.FifthStripAllCellsC
import checkpoints.shen_extension.FifthStripAllCellsD
import checkpoints.shen_extension.FifthStripAllCellsE
import checkpoints.shen_extension.FifthStripAllCellsF
import checkpoints.shen_extension.FifthStripAllCellsG
import checkpoints.shen_extension.FifthStripAllCellsH
import checkpoints.shen_extension.FifthStripMixedClone

/-!
# Fifth strip `q = 2s - 7`: the top two orders for small degrees

* `cycle_fifth_strip_below_top_all`: CH on the whole strip except its top order,
  `n + 1 ≤ q s`, for every degree `s ≥ 11`.
* `cycle_fifth_strip_closed_all`: the whole strip `n ≤ q s` for every odd `s ≥ 13` and
  every `s ≥ 43`.

For `s ≥ 59` both come from `ShenFifthStrip.cycle_fifth_strip_closed`. For `11 ≤ s ≤ 58`
the generic theorems of `FifthStripAllCore/Top/Dense/Cell` are applied to the finite
checks `Cell (s - 7)`, decided block by block in `FifthStripAllCells*`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAll
open Finset BRq2 BRq3 BR45

theorem cell_of {a : ℕ} (lo : 4 ≤ a) (hi : a ≤ 51) : Cell a := by
  rcases (by omega : a ≤ 13 ∨ (14 ≤ a ∧ a ≤ 21) ∨ (22 ≤ a ∧ a ≤ 28) ∨ (29 ≤ a ∧ a ≤ 34) ∨
      (35 ≤ a ∧ a ≤ 39) ∨ (40 ≤ a ∧ a ≤ 43) ∨ (44 ≤ a ∧ a ≤ 47) ∨ 48 ≤ a) with
    h | h | h | h | h | h | h | h
  · exact cells_A a (mem_Icc.mpr ⟨lo, h⟩)
  · exact cells_B a (mem_Icc.mpr h)
  · exact cells_C a (mem_Icc.mpr h)
  · exact cells_D a (mem_Icc.mpr h)
  · exact cells_E a (mem_Icc.mpr h)
  · exact cells_F a (mem_Icc.mpr h)
  · exact cells_G a (mem_Icc.mpr h)
  · exact cells_H a (mem_Icc.mpr ⟨h, hi⟩)

/-- **Fifth strip below its top order, every degree `s ≥ 11`.** -/
theorem cycle_fifth_strip_below_top_all {s q n : ℕ} {D : CH.Digraph}
    (hs : 11 ≤ s) (hq : q = 2*s-7) (hn : 0 < n) (hnq : n+1 ≤ q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_cases big : 59 ≤ s
  · exact ShenFifthStrip.cycle_fifth_strip_closed big hq hn (by omega) hl hm
  obtain ⟨a, rfl⟩ : ∃ a, s = a+7 := ⟨s-7, by omega⟩
  have he : q = 2*a+7 := by omega
  rw [he] at hnq ⊢
  by_contra no
  have hf := qfree_of_noShort hl no
  have md := fun v (hv : v ∈ Finset.range n) => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)
  have ne := Finset.card_pos.mp (by rwa [Finset.card_range] : 0 < (Finset.range n).card)
  have cell := cell_of (a := a) (by omega) (by omega)
  have h := cell_order (by omega) cell _ _ hf md ne
  rw [Finset.card_range] at h
  omega

/-- **The whole fifth strip for every odd degree `s ≥ 13` and every degree `s ≥ 43`.** -/
theorem cycle_fifth_strip_closed_all {s q n : ℕ} {D : CH.Digraph}
    (hs : 13 ≤ s) (hpar : s % 2 = 1 ∨ 43 ≤ s) (hq : q = 2*s-7) (hn : 0 < n) (hnq : n ≤ q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_cases big : 59 ≤ s
  · exact ShenFifthStrip.cycle_fifth_strip_closed big hq hn hnq hl hm
  obtain ⟨a, rfl⟩ : ∃ a, s = a+7 := ⟨s-7, by omega⟩
  have he : q = 2*a+7 := by omega
  rw [he] at hnq ⊢
  by_contra no
  have hf := qfree_of_noShort hl no
  have md := fun v (hv : v ∈ Finset.range n) => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv)
  have ne := Finset.card_pos.mp (by rwa [Finset.card_range] : 0 < (Finset.range n).card)
  have cell := cell_of (a := a) (by omega) (by omega)
  have h := cell_order (by omega) cell _ _ hf md ne
  rw [Finset.card_range] at h
  have top : topCase a = true := by
    unfold topCase; simp only [decide_eq_true_eq]; omega
  exact cell_top (by omega) cell top hf md ne (by rw [Finset.card_range]; omega)

#print axioms cycle_fifth_strip_below_top_all
#print axioms cycle_fifth_strip_closed_all
end LeanCH.BR.FifthStripAll
