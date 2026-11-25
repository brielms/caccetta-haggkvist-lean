import checkpoints.shen_extension.ThinBound
import checkpoints.shen_extension.FatShort

/-!
# The thin rule: an order bound on the rows `r ≤ 2q - 1`

At degree `r ≤ 2q - 1` a root whose second layer has `r - 1` labels and whose third layer has at
most `r - 1` is tight (`ThinSuppliers.TightR`); `ThinSuppliers.no_tight_thin` excludes tight
roots once the floors pay for it (`ThinBound.thin_bound`).

* `floorsH q r`: the seeded reach climb at degree `r` with the fat-short pattern
  `FatShort.fatShortGX q r` (sound for every root) added to the checker, radii
  `0 … q - q/2 + 1` (the count reads radius `j + 1`, `j = q - q/2`).
* `looseH q r`: the climb for roots that avoid `ShapeClimbAvoid.tightA r`
  (`ShapeClimbAvoid.layersA`, with the same pattern) over those floors, radii `0 … q - q/2`
  (the count and the order bound read radius `j` at most).
* `thinBound q r`: the larger of the order bound of `floorsH q r` and the largest order `m`,
  at most the order bound of `looseH q r`, that passes the ledger test `ThinBound.ThinOK`.
  Zero unless `4 ≤ q`, `1 ≤ r`, `r ≤ 2q - 1`.
* `thinBound_sound`: every `q`-free digraph of minimum out-degree `r` has more than
  `thinBound q r` labels. `thin_excluded`: so no counterexample has order at most
  `thinBound (cutoff p) p.s`.
* `thinBoundF`: the same number over the pruned evaluations, proved equal.

Generic in `q` and `r`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ThinRule
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget
open ShapeClimbAt (library_bankAt)

/-- The closed lower degrees available to the bank at degree `r`. -/
def bankDegree (r : ℕ) : ℕ := min (r - 1) (projectionFloor - 1)

/-- Floors of every root at degree `r`, radii `0 … q - q/2 + 1`. -/
def floorsH (q r : ℕ) : List ℕ :=
  ShapeClimbX.layersX (FatShort.fatShortGX q r) q r (library q (bankDegree r))
    (ShapeClimbMono.seedAt q r (bankDegree r) (q - q/2)) (q - q/2)

/-- Floors of roots that are not tight at degree `r`, radii `0 … q - q/2`. -/
def looseH (q r : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersA (ShapeClimbAvoid.tightA r) (FatShort.fatShortGX q r) q r
    (library q (bankDegree r)) (floorsH q r) (q - q/2 - 1)

/-- The order bound of the thin rule at cutoff `q`, degree `r`. -/
def thinBound (q r : ℕ) : ℕ :=
  if 4 ≤ q ∧ 1 ≤ r ∧ r + 1 ≤ 2 * q then
    max (ShapeClimbMono.boundOf q r (floorsH q r))
      (Nat.findGreatest (fun m => ThinBound.ThinOK q r (floorsH q r) (looseH q r) m)
        (ShapeClimbMono.boundOf q r (looseH q r)))
  else 0

theorem thinBound_sound {q r : ℕ} {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q)
    (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) : thinBound q r < V.card := by
  unfold thinBound
  split
  next hq =>
    have pf : 0 < projectionFloor := Nat.succ_pos _
    have known : ∀ q' t, t ≤ bankDegree r → NoHost q' t := fun q' t ht =>
      ShapeClimbMono.lower_hosts_every q' t (by
        have := ht.trans (min_le_right (r - 1) (projectionFloor - 1))
        omega)
    have cr : bankDegree r < r := lt_of_le_of_lt (min_le_left ..) (by omega)
    have bank := library_bankAt (r := r) (by omega : 2 ≤ q) cr (known q)
    have seeds := ShapeClimbMono.seedAt_sound (q := q) (K := q - q/2) cr known
    have floors : ∀ i, Floor q r i ((floorsH q r).getD i 0) :=
      (ShapeClimbX.layersX_sound (FatShort.fatShortGX_sound q r) (by omega) bank seeds
        (q - q/2) (by omega)).2
    have loose : ∀ i, ShapeClimbAvoid.AvoidFloor q r (ShapeClimbAvoid.tightA r) i
        ((looseH q r).getD i 0) :=
      (ShapeClimbAvoid.layersA_sound (FatShort.fatShortGX_sound q r) (by omega) bank floors
        (q - q/2 - 1) (by omega)).2
    refine max_lt (ShapeClimbMono.boundOf_sound (by omega) floors free ne deg) ?_
    by_cases zero : Nat.findGreatest (fun m => ThinBound.ThinOK q r (floorsH q r) (looseH q r) m)
        (ShapeClimbMono.boundOf q r (looseH q r)) = 0
    · rw [zero]
      exact card_pos.mpr ne
    · exact ThinBound.thin_bound hq.1 hq.2.2 floors loose
        (Nat.findGreatest_of_ne_zero rfl zero) (Nat.findGreatest_le _) free ne deg
  next => exact card_pos.mpr ne

/-- No counterexample has order at most `thinBound (cutoff p) p.s`. (Outside `4 ≤ cutoff p`,
`p.s ≤ 2 cutoff p - 1` the bound is zero.) -/
theorem thin_excluded {p : Input} (bad : Bad p) :
    ¬(0 < p.n ∧ p.n ≤ thinBound (cutoff p) p.s) := by
  rintro ⟨pos, small⟩
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  have deg : ∀ v ∈ range p.n, p.s ≤ (outN p.D (range p.n) v).card := fun v hv =>
    Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  have := thinBound_sound free ⟨0, mem_range.mpr pos⟩ deg
  rw [card_range] at this
  omega

/-! ### The same number over the pruned evaluations -/

def floorsHF (q r : ℕ) : List ℕ :=
  ShapeClimbX.layersXF (FatShort.fatShortGX q r) q r (library q (bankDegree r))
    (ShapeClimbMono.seedAtF q r (bankDegree r) (q - q/2)) (q - q/2)

def looseHF (q r : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersAF (ShapeClimbAvoid.tightA r) (FatShort.fatShortGX q r) q r
    (library q (bankDegree r)) (floorsHF q r) (q - q/2 - 1)

def thinBoundF (q r : ℕ) : ℕ :=
  if 4 ≤ q ∧ 1 ≤ r ∧ r + 1 ≤ 2 * q then
    max (ShapeClimbMono.boundOf q r (floorsHF q r))
      (Nat.findGreatest (fun m => ThinBound.ThinOK q r (floorsHF q r) (looseHF q r) m)
        (ShapeClimbMono.boundOf q r (looseHF q r)))
  else 0

theorem floorsHF_eq (q r : ℕ) : floorsHF q r = floorsH q r := by
  simp only [floorsHF, floorsH, ShapeClimbX.layersXF_eq, ShapeClimbMono.seedAtF,
    ShapeClimbMono.seedAt, ShapeClimbFast.layers3F_eq]

theorem looseHF_eq (q r : ℕ) : looseHF q r = looseH q r := by
  simp only [looseHF, looseH, ShapeClimbAvoid.layersAF_eq, floorsHF_eq]

theorem thinBoundF_eq (q r : ℕ) : thinBoundF q r = thinBound q r := by
  simp only [thinBoundF, thinBound, floorsHF_eq, looseHF_eq]

#print axioms thinBound_sound
#print axioms thin_excluded
#print axioms thinBoundF_eq
end LeanCH.BR.ThinRule
