module

public import LeanCH.CompromiseColumnCoupling

set_option linter.style.header false

/-! Exact off-tail loss under arc deletion. Only the incoming edge and
the second-neighbour endpoints whose unique last edge was removed can
contribute. The resulting certificate couples rows of the inverse. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseArcMinimal
open CH.CompromiseLostArc CH.CompromiseRowRepair CH.CompromiseColumnCoupling
public section

namespace CH.CompromiseArcLoss

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def lostParents (i j : V) : Finset V :=
  univ.filter (fun v => j ∈ second adj v ∧
    j ∉ second (CH.ArcMinimal.eraseArc adj i j) v)

theorem tail_not_lost (i j : V) (edge : adj i j) : i ∉ lostParents adj i j := by
  intro h
  exact ((mem_second adj i j).mp (mem_filter.mp h).2.1).2.1 edge

theorem other_second_unchanged (i j v u : V) (hv : v ≠ i) (hu : u ≠ j) :
    u ∈ second (CH.ArcMinimal.eraseArc adj i j) v ↔ u ∈ second adj v := by
  constructor
  · intro h
    exact (second_after_erase adj i j v u h).resolve_right (fun hh => hv hh.1)
  · intro h
    obtain ⟨hne, hnon, a, hva, hau⟩ := (mem_second adj v u).mp h
    apply (mem_second _ v u).mpr
    exact ⟨hne, fun hh => hnon hh.1, a,
      ⟨hva, fun hh => hv hh.1⟩, ⟨hau, fun hh => hu hh.2⟩⟩

theorem other_second_change (i j v u : V) (hv : v ≠ i) :
    (if u ∈ second (CH.ArcMinimal.eraseArc adj i j) v then (1 : ℝ) else 0) =
      (if u ∈ second adj v then 1 else 0) -
        (if v ∈ lostParents adj i j ∧ u = j then 1 else 0) := by
  by_cases hu : u = j
  · subst u
    have hs : j ∈ second (CH.ArcMinimal.eraseArc adj i j) v → j ∈ second adj v :=
      fun h => (second_after_erase adj i j v j h).resolve_right (fun hh => hv hh.1)
    by_cases hn : j ∈ second (CH.ArcMinimal.eraseArc adj i j) v
    · have hl : v ∉ lostParents adj i j := fun h => (mem_filter.mp h).2.2 hn
      simp only [hn, hs hn, hl, false_and, ite_true, ite_false, sub_zero]
    · by_cases ho : j ∈ second adj v
      · have hl : v ∈ lostParents adj i j := mem_filter.mpr ⟨mem_univ v, ho, hn⟩
        simp only [hn, ho, hl, and_self, ite_true, ite_false, sub_self]
      · have hl : v ∉ lostParents adj i j := fun h => ho (mem_filter.mp h).2.1
        simp only [hn, ho, hl, false_and, ite_false, sub_zero]
  · simp only [other_second_unchanged adj i j v u hv hu, hu, and_false, ite_false, sub_zero]

/-- The full nonnegative loss matrix has just two kinds of entries. -/
theorem arc_loss_exact (i j : V) (hne : i ≠ j) (edge : adj i j) (v u : V) :
    arcLoss adj i j v u = (if v = j ∧ u = i then 1 else 0) +
      (if v ∈ lostParents adj i j ∧ u = j then 1 else 0) := by
  by_cases hv : v = i
  · subst v
    have ht := tail_not_lost adj i j edge
    simp [arcLoss, loss, shiftRow, changed_row_exact adj i j hne edge, hne, ht]
  · have ho : CH.ArcMinimal.eraseArc adj i j v u ↔ adj v u := by
      simp [CH.ArcMinimal.eraseArc, hv]
    have hi : (if adj u v then (1 : ℝ) else 0) -
        (if CH.ArcMinimal.eraseArc adj i j u v then 1 else 0) =
        if v = j ∧ u = i then 1 else 0 := by
      by_cases hh : v = j ∧ u = i
      · obtain ⟨rfl, rfl⟩ := hh
        simp [CH.ArcMinimal.eraseArc, edge]
      · have hn : ¬ (u = i ∧ v = j) := fun h => hh ⟨h.2, h.1⟩
        simp [CH.ArcMinimal.eraseArc, hn, hh]
    have hs := other_second_change adj i j v u hv
    simp only [arcLoss, loss, shiftRow, ite_eq_right hv, add_zero, coefficient,
      CH.CompromisePacking.capacity, ho]
    linarith

theorem arc_loss_payoff (i j : V) (hne : i ≠ j) (edge : adj i j) (x p : V → ℝ) :
    payoff (arcLoss adj i j) x p = p j * x i + mass p (lostParents adj i j) * x j := by
  have hr (v : V) : row (arcLoss adj i j) x v =
      (if v = j then x i else 0) + (if v ∈ lostParents adj i j then x j else 0) := by
    simp only [row, arc_loss_exact adj i j hne edge, add_mul, sum_add_distrib]
    by_cases hv : v = j
    · subst v
      by_cases hl : j ∈ lostParents adj i j <;> simp [hl]
    · by_cases hl : v ∈ lostParents adj i j <;> simp [hv, hl]
  have he : (∑ v, if v ∈ lostParents adj i j then p v * x j else 0) =
      mass p (lostParents adj i j) * x j := by
    rw [← sum_filter]
    have hf : univ.filter (fun v => v ∈ lostParents adj i j) = lostParents adj i j := by ext; simp
    rw [hf]
    exact (sum_mul _ _ _).symm
  simp only [payoff, hr, mul_add, sum_add_distrib, mul_ite, mul_zero]
  rw [sum_ite_eq', he]
  simp only [mem_univ, ite_true]

/-- Explicit coupling through the incoming and outgoing private paths
of the very same deleted arc. -/
theorem private_path_coupling (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i j : V) (edge : adj i j) :
    ∃ p ∈ simplex,
      (∀ u, 0 ≤ col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p u) ∧
      0 < p i ∧ ∀ k,
      p k + p j * Q adj i k + p i * mass (fun u => Q adj u k) (lostSecond adj i j) ≤
        ((2 + newHead adj i j) * p i - mass p (lostParents adj i j)) * Q adj j k := by
  obtain ⟨p, hp, cols, pp, ht⟩ :=
    deleted_certificate_coupling adj noLoop deleted minimal w0 hw0 bad0 i j edge
  have hne : i ≠ j := by intro hh; subst j; exact noLoop i edge
  refine ⟨p, hp, cols, pp, ?_⟩
  intro k
  have h := ht k
  rw [arc_loss_payoff adj i j hne edge] at h
  nlinarith

end CH.CompromiseArcLoss

#print axioms CH.CompromiseArcLoss.arc_loss_exact
#print axioms CH.CompromiseArcLoss.arc_loss_payoff
#print axioms CH.CompromiseArcLoss.private_path_coupling
