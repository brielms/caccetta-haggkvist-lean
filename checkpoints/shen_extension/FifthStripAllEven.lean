import checkpoints.shen_extension.FifthStripAll
import checkpoints.shen_extension.RigidFalse

/-!
# Fifth strip: the top order at even degrees

`FifthStripAll.cycle_fifth_strip_closed_all` closes the top order `q s` of the fifth strip
(`q = 2 s - 7`) for odd `s ≥ 13` and for `s ≥ 43`. Here the even degrees `14 ≤ s ≤ 42` are closed:
the top-order check `Top a (q s)` holds for every odd shift `7 ≤ a ≤ 35` (kernel-checked below),
so a host of order `q s` is rigid, and `RigidFalse.rigid_false` says no rigid host exists.

`cycle_fifth_strip_closed_every` is the whole fifth strip for every degree `s ≥ 13`.
-/

set_option maxRecDepth 100000
set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAll
open Finset BRq2 BRq3 BR45

set_option maxHeartbeats 0 in
theorem top_7 : Top 7 294 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_9 : Top 9 400 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_11 : Top 11 522 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_13 : Top 13 660 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_15 : Top 15 814 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_17 : Top 17 984 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_19 : Top 19 1170 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_21 : Top 21 1372 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_23 : Top 23 1590 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_25 : Top 25 1824 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_27 : Top 27 2074 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_29 : Top 29 2340 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_31 : Top 31 2622 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_33 : Top 33 2920 := by decide +kernel

set_option maxHeartbeats 0 in
theorem top_35 : Top 35 3234 := by decide +kernel

/-- The top-order check at every odd shift from 7 to 35 (even degrees 14 to 42). -/
theorem top_odd {a : ℕ} (lo : 7 ≤ a) (hi : a ≤ 35) (odd : a % 2 = 1) :
    Top a ((2*a+7)*(a+7)) := by
  have cases : a = 7 ∨ a = 9 ∨ a = 11 ∨ a = 13 ∨ a = 15 ∨ a = 17 ∨ a = 19 ∨ a = 21 ∨ a = 23 ∨ a = 25 ∨ a = 27 ∨ a = 29 ∨ a = 31 ∨ a = 33 ∨ a = 35 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact top_7
  · exact top_9
  · exact top_11
  · exact top_13
  · exact top_15
  · exact top_17
  · exact top_19
  · exact top_21
  · exact top_23
  · exact top_25
  · exact top_27
  · exact top_29
  · exact top_31
  · exact top_33
  · exact top_35

/-- **The whole fifth strip for every degree `s ≥ 13`.** -/
theorem cycle_fifth_strip_closed_every {s q n : ℕ} {D : CH.Digraph}
    (hs : 13 ≤ s) (hq : q = 2*s-7) (hn : 0 < n) (hnq : n ≤ q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_cases old : s % 2 = 1 ∨ 43 ≤ s
  · exact cycle_fifth_strip_closed_all hs old hq hn hnq hl hm
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
  have L := ledger_floors (by omega) cell.1
  exact RigidFalse.fifth_top_false (by omega) L (top_odd (by omega) (by omega) (by omega)) hf md
    (by rw [Finset.card_range]; omega)

#print axioms top_odd
#print axioms cycle_fifth_strip_closed_every
end LeanCH.BR.FifthStripAll
