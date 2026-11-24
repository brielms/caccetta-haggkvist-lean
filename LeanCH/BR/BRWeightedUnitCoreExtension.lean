import LeanCH.BR.BRWeightedUnitCoreArithmetic
import LeanCH.BR.BRWeightedTightCut

/-! SelfDual is used on the actual induced one-vertex extension.
No algebra-only implication from SelfDual to rootedness is used. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem unit_core_extension_column_le {q : ℕ} {D : CH.Digraph} {S : Finset ℕ} {v : ℕ}
    (hv : v ∉ S) (hSD : SelfDual q D (insert v S)) (z : ℕ → ℚ)
    (hz : ∀ x ∈ S, 0 ≤ z x) (hm : mass S z = 1)
    (hr : ∀ x ∈ S, row q D S z x = 1) (hout : 1 ≤ (q : ℚ)*outW D S z v) :
    (q : ℚ)*inW D S z v ≤ 1 := by
  let z0 : ℕ → ℚ := fun x => if x ∈ S then z x else 0
  have hzero : ∀ x ∈ insert v S, x ∉ S → z0 x = 0 := by
    intro x _ hx; simp [z0,hx]
  have hmass : mass (insert v S) z0 = 1 := by
    rw [← mass_subset_zero (subset_insert v S) hzero]
    calc
      mass S z0 = mass S z := sum_congr rfl (fun x hx => by simp [z0,hx])
      _ = 1 := hm
  have ho : ∀ x, outW D (insert v S) z0 x = outW D S z x := by
    intro x
    rw [← outW_subset_zero (subset_insert v S) hzero]
    exact sum_congr rfl (fun y hy => by simp [z0,hy])
  have hi : ∀ x, inW D (insert v S) z0 x = inW D S z x := by
    intro x
    rw [← inW_subset_zero (subset_insert v S) hzero]
    exact sum_congr rfl (fun y hy => by simp [z0,hy])
  have hn : ∀ x ∈ insert v S, 0 ≤ z0 x := by
    intro x _
    by_cases hx : x ∈ S
    · simpa only [z0,if_pos hx] using hz x hx
    · simp [z0,hx]
  have hr0 : ∀ x ∈ insert v S, mass (insert v S) z0 ≤ row q D (insert v S) z0 x := by
    intro x hx
    rw [hmass,row,ho]
    rcases mem_insert.mp hx with rfl | hx
    · simpa only [z0,if_neg hv,zero_add] using hout
    · simpa only [z0,if_pos hx,row] using (hr x hx).ge
  have hc := hSD z0 hn hr0 v (mem_insert_self _ _)
  simpa only [hmass,col,hi,z0,if_neg hv,zero_add] using hc

theorem unit_core_contact_nontight {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {S : Finset ℕ}
    (z : ℕ → ℚ) (hr : ∀ x ∈ S, row q D S z x = 1) (v : ℕ) :
    (q : ℚ)*outW D S z v ≠ 1 ∧ (q : ℚ)*inW D S z v ≠ 1 := by
  constructor
  · rw [outW_eq_mass]
    exact unit_row_subset_mass_ne hq (filter_subset _ _) z hr
  · have he : inW D S z v = mass (inN D S v) z := by
      exact outW_eq_mass (fun i j => D j i) S z v
    rw [he]
    exact unit_row_subset_mass_ne hq (filter_subset _ _) z hr

theorem unit_core_extension_heavy_light {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {S : Finset ℕ} {v : ℕ} (hv : v ∉ S)
    (hSD : SelfDual q D (insert v S)) (z : ℕ → ℚ) (hz : ∀ x ∈ S, 0 ≤ z x)
    (hm : mass S z = 1) (hr : ∀ x ∈ S, row q D S z x = 1)
    (hout : 1 < (q : ℚ)*outW D S z v) : (q : ℚ)*inW D S z v < 1 :=
  lt_of_le_of_ne (unit_core_extension_column_le hv hSD z hz hm hr hout.le)
    (unit_core_contact_nontight hq z hr v).2

end LeanCH.BR.WeightedSD
