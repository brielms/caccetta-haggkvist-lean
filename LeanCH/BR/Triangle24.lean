import LeanCH.BR.CH8
import LeanCH.BR.BR37
import LeanCH.BR.BR36Disc
import LeanCH.BR.BR35
import LeanCH.BR.BR34
import LeanCH.BR.SmallBR

/-!
# The triangle case of Caccetta–Häggkvist for every order `n ≤ 24` (Lean 4.35.0)

`triangle_le_24`: every loopless digraph on `n` labels, `0 < n ≤ 24`, with minimum out-degree `r` where
`n ≤ 3r`, has a directed cycle of length at most `3`.

Proof: for `r ≤ 7` this is `ch_of_boundaryRegular` with `BR(3,r)` (`br_one` … `br_seven`); for `r ≥ 8`
lower the degree to `8` and use `CH8.ch_eight`.
-/

namespace LeanCH.BR.Triangle24

open CH Compose.Boundary

/-- Minimum out-degree is monotone: `r' ≥ r` distinct heads give `r` distinct heads. -/
theorem minOut_mono {G : CH.Digraph} {n r r' : Nat} (h : r ≤ r') (deg : CH.MinOutdegreeAtLeast G n r') :
    CH.MinOutdegreeAtLeast G n r := by
  intro v hv
  obtain ⟨nbrs, hlen, hnd, hmem⟩ := deg v hv
  refine ⟨nbrs.take r, ?_, hnd.sublist (List.take_sublist _ _), ?_⟩
  · rw [List.length_take, hlen]; omega
  · intro w hw
    exact hmem w (List.mem_of_mem_take hw)

/-- `BR(3,r)` for `1 ≤ r ≤ 7`. -/
theorem br_le_seven {r : Nat} (h1 : 1 ≤ r) (h7 : r ≤ 7) : BoundaryRegular 3 r := by
  rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LeanCH.BR.SmallBR.br_one
  · exact LeanCH.BR.SmallBR.br_two
  · exact LeanCH.BR.SmallBR.br_three
  · exact LeanCH.BR.BR34.br_four
  · exact LeanCH.BR.BR35.br_five
  · exact LeanCH.BR.BR36.br_six
  · exact LeanCH.BR.BR37.br_seven

/-- **Triangle case of Caccetta–Häggkvist for `n ≤ 24`.** A loopless digraph on `n` labels, `0 < n ≤ 24`,
with minimum out-degree at least `r` and `n ≤ 3r`, has a directed cycle of length at most `3`. -/
theorem triangle_le_24 : ∀ n r : Nat, 0 < n → n ≤ 24 → n ≤ 3 * r → ∀ G : CH.Digraph,
    CH.Loopless G n → CH.MinOutdegreeAtLeast G n r → CH.HasDirectedCycleAtMost G n 3 := by
  intro n r hn h24 hnr G hl deg
  by_cases h8 : 8 ≤ r
  · exact LeanCH.BR.CH8.ch_eight n hn h24 G hl (minOut_mono h8 deg)
  · have hr1 : 1 ≤ r := by omega
    exact ch_of_boundaryRegular (by omega) (br_le_seven hr1 (by omega)) hn hnr hl deg

end LeanCH.BR.Triangle24
