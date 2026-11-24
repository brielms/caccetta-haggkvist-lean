module

public import LeanCH.CompromiseArcMinimal
public import LeanCH.CompromiseRowRepair

set_option linter.style.header false

/-! Arc deletion with the exact loss of second-neighbour endpoints.
The original row gains at most its newly unexcluded head and loses every
endpoint whose last surviving two-step path used the deleted arc. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePacking CH.CompromisePerturbation CH.CompromiseRowRepair
open CH.CompromiseArcMinimal
public section

namespace CH.CompromiseLostArc

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def lostSecond (i j : V) : Finset V :=
  second adj i \ second (CH.ArcMinimal.eraseArc adj i j) i

@[expose] def newHead (i j : V) : ℝ :=
  if j ∈ second (CH.ArcMinimal.eraseArc adj i j) i then 1 else 0

@[expose] def changeRow (i j u : V) : ℝ :=
  (if u = j then 2 + newHead adj i j else 0) - (if u ∈ lostSecond adj i j then 1 else 0)

theorem second_change (i j : V) (edge : adj i j) (u : V) :
    (if u ∈ second (CH.ArcMinimal.eraseArc adj i j) i then (1 : ℝ) else 0) =
      (if u ∈ second adj i then 1 else 0) + (if u = j then newHead adj i j else 0) -
        (if u ∈ lostSecond adj i j then 1 else 0) := by
  by_cases hu : u = j
  · subst u
    have hj : j ∉ second adj i := fun h => ((mem_second adj i j).mp h).2.1 edge
    have hl : j ∉ lostSecond adj i j := fun h => hj (mem_sdiff.mp h).1
    simp [newHead, hj, hl]
  · have hs : u ∈ second (CH.ArcMinimal.eraseArc adj i j) i → u ∈ second adj i := by
      intro h
      rcases second_after_erase adj i j i u h with hd | hj
      · exact hd
      · exact (hu hj.2).elim
    by_cases hc : u ∈ second (CH.ArcMinimal.eraseArc adj i j) i
    · simp [hu, hc, hs hc, lostSecond]
    · by_cases hd : u ∈ second adj i <;> simp [hu, hc, hd, lostSecond]

/-- The changed tail row is exact, including all its lost endpoints. -/
theorem changed_row_exact (i j : V) (hne : i ≠ j) (edge : adj i j) (u : V) :
    coefficient (CH.ArcMinimal.eraseArc adj i j) i u =
      coefficient adj i u + changeRow adj i j u := by
  have hi : CH.ArcMinimal.eraseArc adj i j u i ↔ adj u i := by
    simp [CH.ArcMinimal.eraseArc, hne]
  have ho : (if CH.ArcMinimal.eraseArc adj i j i u then (2 : ℝ) else 0) =
      (if adj i u then 2 else 0) - (if u = j then 2 else 0) := by
    by_cases hu : u = j
    · subst u
      simp [CH.ArcMinimal.eraseArc, edge]
    · simp [CH.ArcMinimal.eraseArc, hu]
  have hs := second_change adj i j edge u
  change (if u ∈ second (CH.ArcMinimal.eraseArc adj i j) i then 1 else 0) +
    (if CH.ArcMinimal.eraseArc adj i j u i then 1 else 0) -
    (if CH.ArcMinimal.eraseArc adj i j i u then 2 else 0) =
    (if u ∈ second adj i then 1 else 0) + (if adj u i then 1 else 0) -
    (if adj i u then 2 else 0) + changeRow adj i j u
  simp only [hi]
  rw [ho, hs]
  by_cases hu : u = j <;> simp only [changeRow, hu, ite_true, ite_false] <;> ring

theorem coefficient_bound (i j : V) (hne : i ≠ j) (edge : adj i j) (v u : V) :
    coefficient (CH.ArcMinimal.eraseArc adj i j) v u ≤
      shiftRow (coefficient adj) i (changeRow adj i j) v u := by
  by_cases hv : v = i
  · subst v
    simpa [shiftRow] using (changed_row_exact adj i j hne edge u).le
  · have h := coefficient_after_erase_le adj i j v u
    simpa [shiftRow, raiseEntry, hv] using h

theorem change_pairing (i j : V) (f : V → ℝ) :
    pairing (changeRow adj i j) f =
      (2 + newHead adj i j) * f j - mass f (lostSecond adj i j) := by
  have he : (∑ u, if u ∈ lostSecond adj i j then f u else 0) = mass f (lostSecond adj i j) := by
    rw [← sum_filter]
    have hs : univ.filter (fun u => u ∈ lostSecond adj i j) = lostSecond adj i j := by ext; simp
    rw [hs]
    rfl
  simp only [pairing, changeRow, sub_mul, ite_mul, zero_mul, one_mul, sum_sub_distrib]
  simp [he]

/-- Weighted arc minimality pays one unit plus the exact lost-endpoint
mass from the inverse column. No triangle or Seymour input is used. -/
theorem sharp_arc_charge (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i j : V) (edge : adj i j) :
    1 + mass (fun u => Q adj u i) (lostSecond adj i j) ≤
      (2 + newHead adj i j) * Q adj j i := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w0 hw0 bad0
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have hne : i ≠ j := by
    intro h
    subst j
    exact noLoop i edge
  have bad (v : V) : row (coefficient adj) w0 v < 0 := by
    rw [row_coefficient]
    exact bad0 v
  have good (y : V → ℝ) (hy : ∀ v, 0 ≤ y v) :
      ∃ v, 0 ≤ row (coefficient (CH.ArcMinimal.eraseArc adj i j)) y v := by
    obtain ⟨v, hv⟩ := minimal i j edge y hy
    exact ⟨v, by simpa [row_coefficient] using hv⟩
  have h := threshold_of_good (coefficient adj) (coefficient (CH.ArcMinimal.eraseArc adj i j))
    i (changeRow adj i j) w0 hw0 bad (fun u => Q adj u i) (fun u => qn u i)
    (inverse_column (CH.CompromiseInverse.matrix adj) unit i)
    (coefficient_bound adj i j hne edge) good
  rw [change_pairing] at h
  linarith

end CH.CompromiseLostArc

#print axioms CH.CompromiseLostArc.changed_row_exact
#print axioms CH.CompromiseLostArc.coefficient_bound
#print axioms CH.CompromiseLostArc.sharp_arc_charge
