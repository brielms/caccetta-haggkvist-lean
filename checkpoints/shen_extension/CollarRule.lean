import checkpoints.shen_extension.ShapeClimbX
import checkpoints.shen_extension.ShapeClimbFat
import checkpoints.shen_extension.ShapeClimbAvoid
import checkpoints.shen_extension.CollarBound
import checkpoints.shen_extension.CollarRowDips3

/-!
# The collar rule: an order bound on the row `r = q + 1`

At degree `r = q + 1` the heads of a root are exactly enough for one loop of length `q + 1`.

* `floorsC q`: the seeded reach climb at degree `q + 1` with the proved row patterns
  (`CollarRowDips.collarRowX2`: collar dip, B1 and B2) added to the checker.
* `fatC q`: the climb for roots that avoid `ShapeClimbAvoid.thinA (q+1)`, with the same patterns,
  over those floors (`ShapeClimbAvoid.layersA`); fat roots avoid `thinA`
  (`ShapeClimbAvoid.fat_avoids_thin`), so these are fat-root floors.
* `collarBound q`: the larger of the order bound of `floorsC q` and the largest order `m`,
  at most the order bound of `fatC q`, that passes the ledger test `CollarBound.CollarOK`.
* `collarBound_sound`: every `q`-free digraph of minimum out-degree `q + 1` has more than
  `collarBound q` labels. `collar_excluded`: so no counterexample at degree `cutoff + 1` has
  order at most `collarBound`.
* `collarBoundF`: the same number over the pruned evaluations, proved equal.

Generic in `q`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarRule
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget
open ShapeClimbAt (library_bankAt)

/-- The closed lower degrees available to the bank at degree `q + 1`. -/
def bankDegree (q : ℕ) : ℕ := min q (projectionFloor - 1)

/-- Floors of every root at degree `q + 1`, radii `0 … q/2 + 2`. -/
def floorsC (q : ℕ) : List ℕ :=
  ShapeClimbX.layersX (CollarRowDips.collarRowX2 q (q+1)) q (q+1) (library q (bankDegree q))
    (ShapeClimbMono.seedAt q (q+1) (bankDegree q) (q/2+1)) (q/2+1)

/-- Floors of fat roots at degree `q + 1` (roots that avoid `thinA (q+1)`). -/
def fatC (q : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersA (ShapeClimbAvoid.thinA (q+1)) (CollarRowDips.collarRowX2 q (q+1)) q (q+1)
    (library q (bankDegree q)) (floorsC q) (q/2+1)

/-- The order bound of the collar rule at cutoff `q`, degree `q + 1`. -/
def collarBound (q : ℕ) : ℕ :=
  if 4 ≤ q then
    max (ShapeClimbMono.boundOf q (q+1) (floorsC q))
      (Nat.findGreatest (fun m => CollarBound.CollarOK q (floorsC q) (fatC q) m)
        (ShapeClimbMono.boundOf q (q+1) (fatC q)))
  else 0

theorem collarBound_sound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q)
    (ne : V.Nonempty) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card) : collarBound q < V.card := by
  unfold collarBound
  split
  next hq =>
    have pf : 0 < projectionFloor := Nat.succ_pos _
    have known : ∀ q' t, t ≤ bankDegree q → NoHost q' t := fun q' t ht =>
      ShapeClimbMono.lower_hosts_every q' t (by
        have := ht.trans (min_le_right q (projectionFloor - 1))
        omega)
    have cr : bankDegree q < q + 1 := lt_of_le_of_lt (min_le_left ..) (Nat.lt_succ_self q)
    have bank := library_bankAt (r := q+1) (by omega : 2 ≤ q) cr (known q)
    have seeds := ShapeClimbMono.seedAt_sound (q := q) (K := q/2+1) cr known
    have floors : ∀ i, Floor q (q+1) i ((floorsC q).getD i 0) :=
      (ShapeClimbX.layersX_sound (CollarRowDips.collarRowX2_sound q (q+1)) (by omega) bank seeds
        (q/2+1) (by omega)).2
    have fats : ∀ i, ShapeClimbFat.FatFloor q (q+1) i ((fatC q).getD i 0) := fun i =>
      ShapeClimbAvoid.fatFloor_of_thin
        ((ShapeClimbAvoid.layersA_sound (CollarRowDips.collarRowX2_sound q (q+1)) (by omega) bank
          floors (q/2+1) (by omega)).2 i)
    refine max_lt (ShapeClimbMono.boundOf_sound (by omega) floors free ne deg) ?_
    by_cases zero : Nat.findGreatest (fun m => CollarBound.CollarOK q (floorsC q) (fatC q) m)
        (ShapeClimbMono.boundOf q (q+1) (fatC q)) = 0
    · rw [zero]
      exact card_pos.mpr ne
    · exact CollarBound.collar_bound (by omega) floors (fun i => fats i)
        (Nat.findGreatest_of_ne_zero rfl zero) (Nat.findGreatest_le _) free ne deg
  next => exact card_pos.mpr ne

/-- No counterexample at degree `cutoff + 1` has order at most `collarBound`. -/
theorem collar_excluded {p : Input} (bad : Bad p) (row : p.s = cutoff p + 1) :
    ¬(0 < p.n ∧ p.n ≤ collarBound (cutoff p)) := by
  rintro ⟨pos, small⟩
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  have deg : ∀ v ∈ range p.n, cutoff p + 1 ≤ (outN p.D (range p.n) v).card := by
    intro v hv
    rw [← row]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  have := collarBound_sound free ⟨0, mem_range.mpr pos⟩ deg
  rw [card_range] at this
  omega

/-! ### The same number over the pruned evaluations -/

def floorsCF (q : ℕ) : List ℕ :=
  ShapeClimbX.layersXF (CollarRowDips.collarRowX2 q (q+1)) q (q+1) (library q (bankDegree q))
    (ShapeClimbMono.seedAtF q (q+1) (bankDegree q) (q/2+1)) (q/2+1)

def fatCF (q : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersAF (ShapeClimbAvoid.thinA (q+1)) (CollarRowDips.collarRowX2 q (q+1)) q (q+1)
    (library q (bankDegree q)) (floorsCF q) (q/2+1)

def collarBoundF (q : ℕ) : ℕ :=
  if 4 ≤ q then
    max (ShapeClimbMono.boundOf q (q+1) (floorsCF q))
      (Nat.findGreatest (fun m => CollarBound.CollarOK q (floorsCF q) (fatCF q) m)
        (ShapeClimbMono.boundOf q (q+1) (fatCF q)))
  else 0

theorem floorsCF_eq (q : ℕ) : floorsCF q = floorsC q := by
  simp only [floorsCF, floorsC, ShapeClimbX.layersXF_eq, ShapeClimbMono.seedAtF,
    ShapeClimbMono.seedAt, ShapeClimbFast.layers3F_eq]

theorem fatCF_eq (q : ℕ) : fatCF q = fatC q := by
  simp only [fatCF, fatC, ShapeClimbAvoid.layersAF_eq, floorsCF_eq]

theorem collarBoundF_eq (q : ℕ) : collarBoundF q = collarBound q := by
  simp only [collarBoundF, collarBound, floorsCF_eq, fatCF_eq]

#print axioms collarBound_sound
#print axioms collar_excluded
#print axioms collarBoundF_eq
end LeanCH.BR.CollarRule
