import LeanCH.BR.BRq2Ball
import LeanCH.BR.Compose.ThinRigid

/-!
# Boundary regularity `BR(q,2)` for every `q ≥ 1`, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq2_attempt_subagent.md`, §3 (Theorem C).

* `in_le_two`: on `2q+1` labels (loopless, min out `≥ 2`, no directed cycle of length `≤ q`), every in-neighbour of
  `u` lies outside `B_{q-1}(u)` (Fact 1.1(a)), and `|B_{q-1}(u)| ≥ 2q-1` (Theorem A, `ball_growth`), so
  `in(u) ≤ 2`.
* `br_q_two`: double counting (`Σ in = Σ out ≥ 2(2q+1)`) makes every in-degree exactly `2`.
* `ch_two_of_le`, `ch_degree_two`: via `ch_of_boundaryRegular`, every loopless digraph on `n ≤ 2q` labels with
  min out `≥ 2` has a directed cycle of length `≤ q`; equivalently CH at `r = 2` (cycle length `≤ ⌈n/2⌉`).
-/

namespace LeanCH.BR.BRq2

open CH Compose.Boundary Compose.FloorSix

theorem minOut2_of_deg {G : CH.Digraph} {n : ℕ} (deg : CH.MinOutdegreeAtLeast G n 2) :
    MinOut2 G (Finset.range n) :=
  fun _ hv => out_card deg (Finset.mem_range.mp hv)

/-- Theorem C, first half: every in-degree is at most two. -/
theorem in_le_two {q : ℕ} (hq : 1 ≤ q) {G : CH.Digraph} (loopless : CH.Loopless G (q * 2 + 1))
    (deg : CH.MinOutdegreeAtLeast G (q * 2 + 1) 2) (noShort : ¬ CH.HasDirectedCycleAtMost G (q * 2 + 1) q)
    {u : ℕ} (hu : u < q * 2 + 1) : (par G (q * 2 + 1) u).card ≤ 2 := by
  classical
  set V := Finset.range (q * 2 + 1)
  have hfree : QFree G V q := qfree_of_noShort loopless noShort
  have huV : u ∈ V := Finset.mem_range.mpr hu
  have hA := ball_growth q hq G V hfree (minOut2_of_deg deg) u huV (q - 1) (by omega)
  have hsub : par G (q * 2 + 1) u ⊆ V \ ball G V u (q - 1) := by
    intro y hy
    obtain ⟨hyV, hyu⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_sdiff.mpr ⟨hyV, fun hyb => no_back_arc hfree huV hyb (by omega) hyu⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset ball_subset, Finset.card_range] at this
  omega

/-- **`BR(q,2)` for every `q ≥ 1`.** Every loopless digraph on `2q+1` labels with minimum out-degree `2` and no
directed cycle of length at most `q` has every in-degree exactly `2`. -/
theorem br_q_two : ∀ q, 1 ≤ q → BoundaryRegular q 2 := by
  intro q hq G loopless deg noShort
  classical
  have hle : ∀ u ∈ Finset.range (q * 2 + 1), (par G (q * 2 + 1) u).card ≤ 2 :=
    fun u hu => in_le_two hq loopless deg noShort (Finset.mem_range.mp hu)
  -- double counting: Σ in = Σ out ≥ (2q+1) 2
  have hge : ∑ _u ∈ Finset.range (q * 2 + 1), 2 ≤
      ∑ u ∈ Finset.range (q * 2 + 1), (par G (q * 2 + 1) u).card :=
    calc ∑ _u ∈ Finset.range (q * 2 + 1), 2
        ≤ ∑ x ∈ Finset.range (q * 2 + 1),
            ((Finset.range (q * 2 + 1)).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range (q * 2 + 1),
            ((Finset.range (q * 2 + 1)).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ u ∈ Finset.range (q * 2 + 1), (par G (q * 2 + 1) u).card := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

/-- CH at degree two below the boundary: on `n ≤ 2q` labels, min out `≥ 2` forces a cycle of length `≤ q`. -/
theorem ch_two_of_le {q n : ℕ} (hq : 1 ≤ q) (hn : 0 < n) (hnq : n ≤ q * 2) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n 2) : CH.HasDirectedCycleAtMost G n q :=
  ch_of_boundaryRegular (by omega) (br_q_two q hq) hn hnq loopless deg

/-- The Caccetta–Häggkvist conjecture at `r = 2`: a cycle of length at most `⌈n/2⌉`. -/
theorem ch_degree_two {n : ℕ} {G : CH.Digraph} (hn : 0 < n) (loopless : CH.Loopless G n)
    (deg : CH.MinOutdegreeAtLeast G n 2) : CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 2) := by
  have hc : CH.ceilDiv n 2 = (n + 1) / 2 := rfl
  exact ch_two_of_le (q := CH.ceilDiv n 2) (by omega) hn (by omega) loopless deg

end LeanCH.BR.BRq2
