module

public import LeanCH.CompromisePacking
public import LeanCH.CompromisePrimeExample

set_option linter.style.header false

/-! An exact obstruction to whole-neighbourhood packing, on the already
specified 32-vertex graph. The finite checks verify this graph only. -/

open Finset CH.CompromisePrimeExample CH.CompromisePacking
public section

namespace CH.CompromisePrimePacking

@[expose] def hub (v : Vertex) : Vertex := (next (next (next v.1)), 0, false)

@[expose] def oppositeLight (v : Vertex) : Vertex := (next (next v.1), v.2.1, true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify the support obstruction for the fixed 32-vertex graph.
theorem missing_hub_obstruction : ∀ v y, ¬ edge y (hub v) →
    ∃ z, edge y z ∧ z ∉ second v ∧ ¬ edge z v := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Computing exact second neighbourhoods checks all possible intermediates.
theorem hub_counts : ∀ v, hub v ∉ second v ∧ edge (hub v) v := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Verify a specific feasible whole neighbourhood in each row of this graph.
theorem opposite_fits : ∀ v z, edge (oppositeLight v) z → z ∈ second v ∨ edge z v := by
  decide

theorem second_eq (v : Vertex) : CH.CompromiseSeven.second edge v = second v := by
  ext z
  simp [second, CH.CompromiseSeven.mem_second]

theorem hub_capacity (v : Vertex) : capacity edge v (hub v) = 1 := by
  obtain ⟨hs, hi⟩ := hub_counts v
  simp [capacity, second_eq, hs, hi]

/-- Every whole out-neighbourhood that fits uses the same unit-capacity target. -/
theorem fits_hits_hub (v y : Vertex)
    (fits : ∀ z, edge y z → 0 < capacity edge v z) : edge y (hub v) := by
  by_contra h
  obtain ⟨z, hyz, hs, hi⟩ := missing_hub_obstruction v y h
  have hp := fits z hyz
  simp [capacity, second_eq, hs, hi] at hp

/-- Every fractional whole-neighbourhood packing has every row sum at most one. -/
theorem packing_rows (C : Vertex → Vertex → ℝ) (hC : Packed edge C) :
    ∀ v, ∑ y, C v y ≤ 1 := by
  intro v
  have h := row_sum_bound edge C hC v (hub v) (fits_hits_hub v)
  simpa [hub_capacity] using h

@[expose] def unitPacking (v y : Vertex) : ℝ := if y = oppositeLight v then 1 else 0

theorem unitPacking_feasible : Packed edge unitPacking := by
  refine ⟨?_, ?_⟩
  · intro v y
    simp only [unitPacking]
    split_ifs <;> norm_num
  · intro v z
    have hr : rowImage edge unitPacking v z =
        if edge (oppositeLight v) z then 1 else 0 := by
      simp [rowImage, unitPacking]
    rw [hr]
    by_cases h : edge (oppositeLight v) z
    · rcases opposite_fits v z h with hs | hi
      · simp [capacity, second_eq, h, hs]
        split_ifs <;> norm_num
      · simp [capacity, second_eq, h, hi]
        split_ifs <;> norm_num
    · simp [capacity, second_eq, h]
      split_ifs <;> norm_num

theorem unitPacking_rows : ∀ v, ∑ y, unitPacking v y = 1 := by
  intro v
  simp [unitPacking]

/-- In particular, no such packing can supply the report's left certificate. -/
theorem packing_no_left_growth (C : Vertex → Vertex → ℝ) (hC : Packed edge C)
    (p : Vertex → ℝ) (hp : ∀ v, 0 ≤ p v)
    (growth : ∀ y, 2 * p y ≤ ∑ v, p v * C v y) : ∀ v, p v = 0 :=
  no_left_growth C (packing_rows C hC) p hp growth

@[expose] def backwards (v : Vertex) : Finset Vertex :=
  univ.filter (fun a => a ≠ v ∧ ¬ edge a v ∧ ∃ b, edge a b ∧ edge b v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Check the exact three unit-weight counts in the fixed graph.
theorem reverse_counts : ∀ v,
    (outN v).card = (if v.2.2 then 9 else 10) ∧
    (inN v).card = (if v.2.2 then 9 else 10) ∧
    (backwards v).card = (if v.2.2 then 11 else 10) := by decide

/-- The packing obstruction coexists with a uniform fair certificate. -/
theorem uniform_fair : CH.CompromiseFair.Fair edge (fun _ => 1) := by
  refine ⟨fun _ => by norm_num, ⟨(0, 0, false), by norm_num⟩, ?_⟩
  intro v
  have ho : outN v = CH.CompromiseSeven.outN edge v := by ext; simp [outN]
  have hi : inN v = CH.CompromiseSeven.inN edge v := by ext; simp [inN]
  have hs : backwards v = CH.CompromiseFair.secondIn edge v := by ext; simp [backwards]
  have hc : 2 * (inN v).card ≤ (outN v).card + (backwards v).card := by
    obtain ⟨ho', hi', hs'⟩ := reverse_counts v
    rw [ho', hi', hs']
    cases v.2.2 <;> norm_num
  rw [← ho, ← hi, ← hs]
  have unit_mass (S : Finset Vertex) :
      CH.CompromiseWeighted.mass (fun _ => (1 : ℝ)) S = S.card := by
    simp [CH.CompromiseWeighted.mass]
  rw [unit_mass, unit_mass, unit_mass]
  exact_mod_cast hc

/-- K* holds on this graph for every nonnegative vertex weighting. -/
theorem all_weights_compromise (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 2 * CH.CompromiseWeighted.outWeight edge w v ≤
      CH.CompromiseWeighted.inWeight edge w v + CH.CompromiseWeighted.secondWeight edge w v := by
  obtain ⟨v, _, hv⟩ := CH.CompromiseFair.compromise_of_fair edge (fun _ => 1) w uniform_fair hw
  exact ⟨v, hv⟩

end CH.CompromisePrimePacking

#print axioms CH.CompromisePrimePacking.missing_hub_obstruction
#print axioms CH.CompromisePrimePacking.hub_counts
#print axioms CH.CompromisePrimePacking.packing_rows
#print axioms CH.CompromisePrimePacking.unitPacking_feasible
#print axioms CH.CompromisePrimePacking.unitPacking_rows
#print axioms CH.CompromisePrimePacking.packing_no_left_growth
#print axioms CH.CompromisePrimePacking.uniform_fair
#print axioms CH.CompromisePrimePacking.all_weights_compromise
