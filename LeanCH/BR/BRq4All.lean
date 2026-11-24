import LeanCH.BR.BRq4Five
import LeanCH.BR.BR34

/-!
# `Ball(q,4)` and `BR(q,4)` for every `q ≥ 4`, and CH at `r = 4` (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §5 (Corollary 19).

* `ball_all4` (**Corollary 19**): `Ball(q,4)` for every `q ≥ 4`, by strong induction from `ball44` (Proposition 5),
  `ball54` (Theorem 18) and `thm16` (Theorem 16 at `k = q - 2 ≥ 4`; its slot `b_{k-2} ≥ 4k-7` is `Ball(k-1,4)` for
  `k ≥ 5` and `b_2 ≥ 9` (`n2_ge_four`) at `k = 4`).
* `br_q_four`: `BR(q,4)` for every `q ≥ 4` (`br_of_ball`).
* `ch_four_of_le`: on `n ≤ 4q` labels (`q ≥ 4`), min out `≥ 4` forces a cycle of length `≤ q`.
* `ch_four_all`: the Caccetta–Häggkvist bound `⌈n/4⌉` at `r = 4` for every `n > 0`, using also `BR(3,4)`
  (`BR34.br_four`) and `BR(1,4)`, `BR(2,4)` (trivial balls).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 Compose.Boundary

/-- `b_2 ≥ 9` in a 4-free out-4 digraph (`n2_ge_four`). -/
theorem b2_ge_nine {D : CH.Digraph} {W : Finset ℕ} {u : ℕ} (hfree : QFree D W 4) (hout : OutEq 4 D W)
    (hu : u ∈ W) : 9 ≤ (ball D W u 2).card := by
  have h2 := n2_ge_four hfree hout hu
  have h1 := card_ball_one_four hfree hout hu
  have e := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := D) (W := W) (u := u) (by omega : 1 ≤ 2))
  unfold lay2 at h2
  omega

/-- **Corollary 19.** `Ball(q,4)` for every `q ≥ 4`. -/
theorem ball_all4 : ∀ q, 4 ≤ q → Ball q 4 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq
  rcases (by omega : q = 4 ∨ q = 5 ∨ 6 ≤ q) with rfl | rfl | h6
  · exact ball44
  · exact ball54
  · obtain ⟨j, rfl⟩ : ∃ j, q = j + 5 := ⟨q - 5, by omega⟩
    refine thm16 (by omega) (ih (j + 3) (by omega) (by omega)) (ih (j + 4) (by omega) (by omega)) ?_
    intro D W u hfree hout hu
    rcases (by omega : j = 1 ∨ 2 ≤ j) with rfl | hj2
    · exact b2_ge_nine (hfree.mono_bound (by omega)) hout hu
    · have := ih (j + 2) (by omega) (by omega) D W (hfree.mono_bound (by omega)) hout u hu
      rwa [show j + 2 - 1 = j + 1 by omega] at this

/-- **`BR(q,4)` for every `q ≥ 4`.** -/
theorem br_q_four : ∀ q, 4 ≤ q → BoundaryRegular q 4 :=
  fun q hq => br_of_ball (by omega) (ball_all4 q hq)

/-- `Ball(1,4)` and `Ball(2,4)` (trivial). -/
theorem ball14 : Ball 1 4 := fun _ _ _ _ u hu => Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩

theorem ball24 : Ball 2 4 := by
  intro D W hfree hout u hu
  change 5 ≤ (ball D W u 1).card
  classical
  have e : ball D W u 1 = insert u (outN D W u) := by
    ext v; rw [mem_ball_one hu, Finset.mem_insert]
  have hnot : u ∉ outN D W u := fun h => loopfree hfree (by omega) hu (mem_outN.mp h).2
  rw [e, Finset.card_insert_of_notMem hnot, hout u hu]

/-- CH at degree four below the boundary: on `n ≤ 4q` labels (`q ≥ 4`), min out `≥ 4` forces a cycle of length
`≤ q`. -/
theorem ch_four_of_le {q n : ℕ} (hq : 4 ≤ q) (hn : 0 < n) (hnq : n ≤ q * 4) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n 4) : CH.HasDirectedCycleAtMost G n q :=
  ch_of_boundaryRegular (by omega) (br_q_four q hq) hn hnq loopless deg

/-- **The Caccetta–Häggkvist conjecture at `r = 4`**: a cycle of length at most `⌈n/4⌉`. -/
theorem ch_four_all {n : ℕ} {G : CH.Digraph} (hn : 0 < n) (loopless : CH.Loopless G n)
    (deg : CH.MinOutdegreeAtLeast G n 4) : CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 4) := by
  have hc : CH.ceilDiv n 4 = (n + 3) / 4 := by unfold CH.ceilDiv; omega
  rcases (by omega : (n + 3) / 4 = 1 ∨ (n + 3) / 4 = 2 ∨ (n + 3) / 4 = 3 ∨ 4 ≤ (n + 3) / 4) with h | h | h | h
  · rw [hc, h]; exact ch_of_boundaryRegular (by omega) (br_of_ball (by omega) ball14) hn (by omega) loopless deg
  · rw [hc, h]; exact ch_of_boundaryRegular (by omega) (br_of_ball (by omega) ball24) hn (by omega) loopless deg
  · rw [hc, h]; exact ch_of_boundaryRegular (by omega) LeanCH.BR.BR34.br_four hn (by omega) loopless deg
  · rw [hc]; exact ch_four_of_le h hn (by omega) loopless deg

end LeanCH.BR.BRq4
