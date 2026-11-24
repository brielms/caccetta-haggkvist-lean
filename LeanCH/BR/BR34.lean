import LeanCH.BR.StrictCap
import LeanCH.BR.SmallBR

/-!
# Boundary regularity `BR(3,4)`, Lean 4.35.0

From the strict degree cap (`LeanCH.BR.StrictCap.strict_cap`): for `2 ≤ s ≤ 4`, a vertex of in-degree `s + a ≥ s`
has `3a + 2 ≤ 3a + 2f + 2 ≤ s ≤ 4`, so `a = 0`; hence every in-degree is at most `s`. Double counting
(`Σ in = Σ out ≥ (3s+1) s`) forces every in-degree to be exactly `s` (as in `LeanCH.BR.SmallBR.br_of_cap`).
With `BR(3,1)`, `BR(3,2)`, `BR(3,3)` from `LeanCH.BR.SmallBR` this gives `BR(3,4)`.

At `s = 4` the excluded equality case is: in-degree `5`, out-degree `4`, `O(v)` a directed 4-cycle (BR(3,1) on the
induced `O(v)`) every row of which heads all three vertices of `M(v)`. This is the paper's Case C (`k = |M(v)| = 3`,
`c = 1`, `K = 2c + 1 = 3`), closed in `LeanCH.BR.LargeModule.arith` by `ℓ = k` and lower BR on the induced `M(v)`.
-/

namespace LeanCH.BR.BR34

open CH Compose.Boundary Compose.FloorSix

/-- If `2 ≤ s ≤ 4` and `BR(3,t)` holds for `1 ≤ t < s`, then `BR(3,s)` holds. -/
theorem br_of_strict_cap {s : Nat} (hs2 : 2 ≤ s) (hs : s ≤ 4)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t) : BoundaryRegular 3 s := by
  classical
  intro G loopless deg noShort
  -- every in-degree is at most s
  have hle : ∀ u ∈ Finset.range (3 * s + 1), (par G (3 * s + 1) u).card ≤ s := by
    intro u hu
    by_contra hgt
    have := LeanCH.BR.StrictCap.strict_cap hs2 brs loopless deg noShort (Finset.mem_range.mp hu)
      (by omega)
    omega
  -- double counting: Σ in = Σ out ≥ (3s+1) s
  have hge : ∑ _u ∈ Finset.range (3 * s + 1), s ≤
      ∑ u ∈ Finset.range (3 * s + 1), (par G (3 * s + 1) u).card :=
    calc ∑ _u ∈ Finset.range (3 * s + 1), s
        ≤ ∑ x ∈ Finset.range (3 * s + 1),
            ((Finset.range (3 * s + 1)).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range (3 * s + 1),
            ((Finset.range (3 * s + 1)).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ u ∈ Finset.range (3 * s + 1), (par G (3 * s + 1) u).card := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

/-- **`BR(3,4)`.** Every loopless digraph on 13 labels with minimum out-degree 4 and no directed cycle of length at
most 3 has every in-degree exactly 4. -/
theorem br_four : BoundaryRegular 3 4 :=
  br_of_strict_cap (by omega) le_rfl (fun t h1 h2 => by
    rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl
    · exact LeanCH.BR.SmallBR.br_one
    · exact LeanCH.BR.SmallBR.br_two
    · exact LeanCH.BR.SmallBR.br_three)

end LeanCH.BR.BR34
