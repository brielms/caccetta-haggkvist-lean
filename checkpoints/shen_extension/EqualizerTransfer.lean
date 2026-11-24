import checkpoints.shen_extension.CycleSlotOrbit
import checkpoints.shen_extension.CycleFanDistance
import LeanCH.BR.BRWeightedStrictAtomFloor

namespace LeanCH.BR.Closure.EqualizerTransfer
open Finset BRq2 BRq3 BR45 WeightedSD

/-- With equalized rows, the table of strict failures for a single transfer is
exactly the directed incidence difference between its two columns. -/
theorem classify {q E V x c} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (pos : ∀i∈V,0≤x i)
    (high : mass V x<c) (rows : ∀ i∈V,WeightedSD.row q E V x i=c)
    {y r b} (yv : y∈V) (rv : r∈V) (diff : y≠r) (bv : b∈V.erase y) :
    let t := WeightedSD.row q E (V.erase y) (transferWeight x y r) b
    let W := mass (V.erase y) (transferWeight x y r)
    (t<W ↔ E b y=true ∧ E b r=false) ∧ (W<t ↔ ¬(E b y=true ∧ E b r=false)) := by
  intro t W
  have floor := strict_atom_floor_of_proper hq free (small.induced free) x pos c high
    (fun i hi => (rows i hi).ge) y yv
  have old := rows b (mem_of_mem_erase bv)
  have lost := outW_erase (D:=E) yv x b
  have gain := outW_transfer (D:=E) (mem_erase.mpr ⟨diff.symm,rv⟩) (x:=y) x b
  have wx := pos y yv
  have qpos : (0:ℚ)≤q := Nat.cast_nonneg _
  have ge := mul_nonneg qpos wx
  change (_ < _ ↔ _) ∧ (_ < _ ↔ _)
  dsimp only [t,W]
  rw [mass_transfer yv rv diff, WeightedSD.row, gain]
  unfold WeightedSD.row at old
  unfold transferWeight
  rw [lost] at old
  cases a : E b y <;> cases h : E b r <;> simp [a] at old ⊢ <;> by_cases same : b=r <;>
    simp [same] at old ⊢ <;> constructor <;> nlinarith only [old,floor,high,ge,wx]

#print axioms classify
end LeanCH.BR.Closure.EqualizerTransfer
