import LeanCH.BR.WeakCap

/-!
# Boundary regularity for small `s` (q = 3), Lean 4.35.0

From the weak degree cap: for `s ≤ 3`, a vertex of in-degree `s + a ≥ s` has `3a ≤ s - 1 ≤ 2`, so `a = 0`;
hence every in-degree is at most `s`. Double counting (`Σ in = Σ out ≥ (3s+1) s`) forces every in-degree to be
exactly `s`. Induction from `s = 1` (where the range `1 ≤ t < s` is empty) gives `BR(3,1)`, `BR(3,2)`, `BR(3,3)`.
-/

namespace LeanCH.BR.SmallBR

open CH Compose.Boundary Compose.FloorSix

/-- If `1 ≤ s ≤ 3` and `BR(3,t)` holds for `1 ≤ t < s`, then `BR(3,s)` holds. -/
theorem br_of_cap {s : Nat} (hs1 : 1 ≤ s) (hs : s ≤ 3)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t) : BoundaryRegular 3 s := by
  classical
  intro G loopless deg noShort
  -- every in-degree is at most s
  have hle : ∀ u ∈ Finset.range (3 * s + 1), (par G (3 * s + 1) u).card ≤ s := by
    intro u hu
    by_contra hgt
    have := LeanCH.BR.WeakCap.weak_cap hs1 brs loopless deg noShort (Finset.mem_range.mp hu)
      (by omega)
    omega
  -- double counting: Σ in = Σ out ≥ (3s+1) s
  have hge : ∑ _u ∈ Finset.range (3 * s + 1), s ≤ ∑ u ∈ Finset.range (3 * s + 1), (par G (3 * s + 1) u).card :=
    calc ∑ _u ∈ Finset.range (3 * s + 1), s
        ≤ ∑ x ∈ Finset.range (3 * s + 1), ((Finset.range (3 * s + 1)).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range (3 * s + 1), ((Finset.range (3 * s + 1)).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ u ∈ Finset.range (3 * s + 1), (par G (3 * s + 1) u).card := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

theorem br_one : BoundaryRegular 3 1 :=
  br_of_cap le_rfl (by omega) (fun _ h1 h2 => absurd h2 (by omega))

theorem br_two : BoundaryRegular 3 2 :=
  br_of_cap (by omega) (by omega) (fun t h1 h2 => by
    obtain rfl : t = 1 := by omega
    exact br_one)

theorem br_three : BoundaryRegular 3 3 :=
  br_of_cap (by omega) le_rfl (fun t h1 h2 => by
    rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
    · exact br_one
    · exact br_two)

end LeanCH.BR.SmallBR
