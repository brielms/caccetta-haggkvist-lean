import checkpoints.shen_extension.TightBound

/-!
# The tight rule: an order bound on the row `r = q + 2`

At degree `r = q + 2` a root whose second layer has `q + 1` labels and whose third layer has at
most `q + 1` is tight (`CollarTwo.Tight`); `CollarTwo.no_tight` excludes tight roots once the
floors pay for it.

* `floorsT q`: the seeded reach climb at degree `q + 2`, radii `0 … q/2 + 3`.
* `looseT q`: the climb for roots that avoid `ShapeClimbAvoid.tightA (q+2)`
  (`ShapeClimbAvoid.layersA`) over those floors.
* `tightBound q`: the larger of the order bound of `floorsT q` and the largest order `m`,
  at most the order bound of `looseT q`, that passes the ledger test `TightBound.TightOK`.
* `tightBound_sound`: every `q`-free digraph of minimum out-degree `q + 2` has more than
  `tightBound q` labels. `tight_excluded`: so no counterexample at degree `cutoff + 2` has
  order at most `tightBound`.
* `tightBoundF`: the same number over the pruned evaluations, proved equal.

The radii `q/2 + 2` and `q - q/2 + 2` must be in the lists, so the climbs run to `K = q/2 + 2`;
their time condition `K + 1 ≤ q` holds from `q = 5` on. Generic in `q`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TightRule
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget
open ShapeClimbAt (library_bankAt)

/-- The closed lower degrees available to the bank at degree `q + 2`. -/
def bankDegree (q : ℕ) : ℕ := min (q + 1) (projectionFloor - 1)

/-- Floors of every root at degree `q + 2`, radii `0 … q/2 + 3`. -/
def floorsT (q : ℕ) : List ℕ :=
  ShapeClimbMono.layersS q (q+2) (library q (bankDegree q))
    (ShapeClimbMono.seedAt q (q+2) (bankDegree q) (q/2+2)) (q/2+2)

/-- Floors of roots that are not tight at degree `q + 2`. -/
def looseT (q : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersA (ShapeClimbAvoid.tightA (q+2)) ShapeClimbAvoid.noX q (q+2)
    (library q (bankDegree q)) (floorsT q) (q/2+2)

/-- The order bound of the tight rule at cutoff `q`, degree `q + 2`. -/
def tightBound (q : ℕ) : ℕ :=
  if 5 ≤ q then
    max (ShapeClimbMono.boundOf q (q+2) (floorsT q))
      (Nat.findGreatest (fun m => TightBound.TightOK q (floorsT q) (looseT q) m)
        (ShapeClimbMono.boundOf q (q+2) (looseT q)))
  else 0

theorem tightBound_sound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q)
    (ne : V.Nonempty) (deg : ∀ v ∈ V, q + 2 ≤ (outN D V v).card) : tightBound q < V.card := by
  unfold tightBound
  split
  next hq =>
    have pf : 0 < projectionFloor := Nat.succ_pos _
    have known : ∀ q' t, t ≤ bankDegree q → NoHost q' t := fun q' t ht =>
      ShapeClimbMono.lower_hosts_every q' t (by
        have := ht.trans (min_le_right (q + 1) (projectionFloor - 1))
        omega)
    have cr : bankDegree q < q + 2 := lt_of_le_of_lt (min_le_left ..) (by omega)
    have bank := library_bankAt (r := q+2) (by omega : 2 ≤ q) cr (known q)
    have seeds := ShapeClimbMono.seedAt_sound (q := q) (K := q/2+2) cr known
    have floors : ∀ i, Floor q (q+2) i ((floorsT q).getD i 0) :=
      (ShapeClimbMono.layersS_sound (by omega) bank seeds (q/2+2) (by omega)).2
    have loose : ∀ i, ShapeClimbAvoid.AvoidFloor q (q+2) (ShapeClimbAvoid.tightA (q+2)) i
        ((looseT q).getD i 0) :=
      (ShapeClimbAvoid.layersA_sound (ShapeClimbAvoid.noX_sound q (q+2)) (by omega) bank floors
        (q/2+2) (by omega)).2
    refine max_lt (ShapeClimbMono.boundOf_sound (by omega) floors free ne deg) ?_
    by_cases zero : Nat.findGreatest (fun m => TightBound.TightOK q (floorsT q) (looseT q) m)
        (ShapeClimbMono.boundOf q (q+2) (looseT q)) = 0
    · rw [zero]
      exact card_pos.mpr ne
    · exact TightBound.tight_bound (by omega) floors loose
        (Nat.findGreatest_of_ne_zero rfl zero) (Nat.findGreatest_le _) free ne deg
  next => exact card_pos.mpr ne

/-- No counterexample at degree `cutoff + 2` has order at most `tightBound`. -/
theorem tight_excluded {p : Input} (bad : Bad p) (row : p.s = cutoff p + 2) :
    ¬(0 < p.n ∧ p.n ≤ tightBound (cutoff p)) := by
  rintro ⟨pos, small⟩
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  have deg : ∀ v ∈ range p.n, cutoff p + 2 ≤ (outN p.D (range p.n) v).card := by
    intro v hv
    rw [← row]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  have := tightBound_sound free ⟨0, mem_range.mpr pos⟩ deg
  rw [card_range] at this
  omega

/-! ### The same number over the pruned evaluations -/

def floorsTF (q : ℕ) : List ℕ :=
  ShapeClimbMono.layersSF q (q+2) (library q (bankDegree q))
    (ShapeClimbMono.seedAtF q (q+2) (bankDegree q) (q/2+2)) (q/2+2)

def looseTF (q : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersAF (ShapeClimbAvoid.tightA (q+2)) ShapeClimbAvoid.noX q (q+2)
    (library q (bankDegree q)) (floorsTF q) (q/2+2)

def tightBoundF (q : ℕ) : ℕ :=
  if 5 ≤ q then
    max (ShapeClimbMono.boundOf q (q+2) (floorsTF q))
      (Nat.findGreatest (fun m => TightBound.TightOK q (floorsTF q) (looseTF q) m)
        (ShapeClimbMono.boundOf q (q+2) (looseTF q)))
  else 0

theorem floorsTF_eq (q : ℕ) : floorsTF q = floorsT q := by
  simp only [floorsTF, floorsT, ShapeClimbMono.layersSF_eq, ShapeClimbMono.seedAtF,
    ShapeClimbMono.seedAt, ShapeClimbFast.layers3F_eq]

theorem looseTF_eq (q : ℕ) : looseTF q = looseT q := by
  simp only [looseTF, looseT, ShapeClimbAvoid.layersAF_eq, floorsTF_eq]

theorem tightBoundF_eq (q : ℕ) : tightBoundF q = tightBound q := by
  simp only [tightBoundF, tightBound, floorsTF_eq, looseTF_eq]

#print axioms tightBound_sound
#print axioms tight_excluded
#print axioms tightBoundF_eq
end LeanCH.BR.TightRule
