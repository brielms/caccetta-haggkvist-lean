import checkpoints.shen_extension.ShapeClimbX
import checkpoints.shen_extension.FlatAtCutoff

/-!
# The flat rule: an order bound on the row `r = q`

At degree `r = q` a root with exactly `q` heads and exactly `q` labels in its second layer has at
least `q` labels in its third layer (`FlatAtCutoff.flat_third`).

* `floorsQ q`: the seeded reach climb at degree `q` with the flat pattern
  (`FlatAtCutoff.flatQ`) added to the checker.
* `flatBound q`: the order bound of `floorsQ q`.
* `flatBound_sound`: every `q`-free digraph of minimum out-degree `q` has more than
  `flatBound q` labels. `flat_excluded`: so no counterexample at degree `cutoff` has
  order at most `flatBound`.
* `flatBoundF`: the same number over the pruned evaluations, proved equal.

Generic in `q`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FlatRule
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget
open ShapeClimbAt (library_bankAt)

/-- The closed lower degrees available to the bank at degree `q`. -/
def bankDegree (q : ℕ) : ℕ := min (q - 1) (projectionFloor - 1)

/-- Floors of every root at degree `q`, radii `0 … q/2 + 2`. -/
def floorsQ (q : ℕ) : List ℕ :=
  ShapeClimbX.layersX (FlatAtCutoff.flatQ q q) q q (library q (bankDegree q))
    (ShapeClimbMono.seedAt q q (bankDegree q) (q/2+1)) (q/2+1)

/-- The order bound of the flat rule at cutoff `q`, degree `q`. -/
def flatBound (q : ℕ) : ℕ :=
  if 4 ≤ q then ShapeClimbMono.boundOf q q (floorsQ q) else 0

theorem flatBound_sound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q)
    (ne : V.Nonempty) (deg : ∀ v ∈ V, q ≤ (outN D V v).card) : flatBound q < V.card := by
  unfold flatBound
  split
  next hq =>
    have pf : 0 < projectionFloor := Nat.succ_pos _
    have known : ∀ q' t, t ≤ bankDegree q → NoHost q' t := fun q' t ht =>
      ShapeClimbMono.lower_hosts_every q' t (by
        have := ht.trans (min_le_right (q - 1) (projectionFloor - 1))
        omega)
    have cr : bankDegree q < q := lt_of_le_of_lt (min_le_left ..) (by omega)
    have bank := library_bankAt (r := q) (by omega : 2 ≤ q) cr (known q)
    have seeds := ShapeClimbMono.seedAt_sound (q := q) (K := q/2+1) cr known
    have floors : ∀ i, Floor q q i ((floorsQ q).getD i 0) :=
      (ShapeClimbX.layersX_sound (FlatAtCutoff.flatQ_sound q q) (by omega) bank seeds
        (q/2+1) (by omega)).2
    exact ShapeClimbMono.boundOf_sound (by omega) floors free ne deg
  next => exact card_pos.mpr ne

/-- No counterexample at degree `cutoff` has order at most `flatBound`. -/
theorem flat_excluded {p : Input} (bad : Bad p) (row : p.s = cutoff p) :
    ¬(0 < p.n ∧ p.n ≤ flatBound (cutoff p)) := by
  rintro ⟨pos, small⟩
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  have deg : ∀ v ∈ range p.n, cutoff p ≤ (outN p.D (range p.n) v).card := by
    intro v hv
    rw [← row]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  have := flatBound_sound free ⟨0, mem_range.mpr pos⟩ deg
  rw [card_range] at this
  omega

/-! ### The same number over the pruned evaluation -/

def floorsQF (q : ℕ) : List ℕ :=
  ShapeClimbX.layersXF (FlatAtCutoff.flatQ q q) q q (library q (bankDegree q))
    (ShapeClimbMono.seedAtF q q (bankDegree q) (q/2+1)) (q/2+1)

def flatBoundF (q : ℕ) : ℕ :=
  if 4 ≤ q then ShapeClimbMono.boundOf q q (floorsQF q) else 0

theorem floorsQF_eq (q : ℕ) : floorsQF q = floorsQ q := by
  simp only [floorsQF, floorsQ, ShapeClimbX.layersXF_eq, ShapeClimbMono.seedAtF,
    ShapeClimbMono.seedAt, ShapeClimbFast.layers3F_eq]

theorem flatBoundF_eq (q : ℕ) : flatBoundF q = flatBound q := by
  simp only [flatBoundF, flatBound, floorsQF_eq]

#print axioms flatBound_sound
#print axioms flat_excluded
#print axioms flatBoundF_eq
end LeanCH.BR.FlatRule
