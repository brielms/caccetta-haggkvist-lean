import LeanCH.BR.BRsubTightSix

/-! The remaining non-tight cap as an explicit premise at `(q,s)=(5,6)`. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 Compose.Boundary

/-- The unresolved non-tight cap. The tight-first-layer branch is supplied
by `tight_six_ball_four_ge_twenty_four`. -/
def NTC6 : Prop :=
  ∀ E : CH.Digraph, QFree E (Finset.range 31) 5 →
    (∀ v ∈ Finset.range 31, 6 ≤ (outN E (Finset.range 31) v).card) →
    Sat 5 E (Finset.range 31) → ∀ u ∈ Finset.range 31,
      ¬ TightRoot E (Finset.range 31) 6 u → 25 ≤ (ball E (Finset.range 31) u 4).card

/-- All of the tight branch is discharged; only the non-tight cap remains. -/
theorem sc_six_of_ntc (hntc : NTC6) : SC 6 := by
  intro E hf hmin hsat u hu
  change QFree E (Finset.range 31) 5 at hf
  change Sat 5 E (Finset.range 31) at hsat
  change ∀ v ∈ Finset.range 31, 6 ≤ (outN E (Finset.range 31) v).card at hmin
  change u ∈ Finset.range 31 at hu
  change 24 ≤ (ball E (Finset.range 31) u 4).card ∧
    ((ball E (Finset.range 31) u 4).card = 24 → TightRoot E (Finset.range 31) 6 u)
  by_cases ht : TightRoot E (Finset.range 31) 6 u
  · exact ⟨tight_six_ball_four_ge_twenty_four hf hsat (Finset.card_range 31) hmin hu ht, fun _ => ht⟩
  · have hb := hntc E hf hmin hsat u hu ht
    exact ⟨by omega, fun h => (by omega : False).elim⟩

/-- Conditional boundary regularity; `NTC6` is an explicit unproved input. -/
theorem br_five_six_of_ntc (hntc : NTC6) : BoundaryRegular 5 6 :=
  br_of_sc (s := 6) (by decide) (sc_six_of_ntc hntc)

end LeanCH.BR.BRsub
