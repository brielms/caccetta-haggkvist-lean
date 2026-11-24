module

public import LeanCH.CompromiseDeletionCone

set_option linter.style.header false

/-! Exact tests for a genuine deletion certificate whose only possible
positive retained slack is at one target. At positive inverse diagonal
the rate is fixed, and every off-target private path saturates an
inverse-entry capacity. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseCertificateCone CH.CompromiseZeroDiagonalCone CH.CompromiseDeletionCone
open CH.CompromiseLostArc CH.CompromiseRegainedSlack
public section

namespace CH.CompromiseSingleTarget

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def oneTarget (u : V) (e : ℝ) (k : V) : ℝ := if k = u then e else 0

variable (adj : V → V → Prop) [DecidableRel adj]

theorem residual_one (j u : V) (e : ℝ) :
    CH.CompromiseZeroDiagonalCone.residual adj j (oneTarget u e) =
      fun k => Q adj j k - e * Q adj u k := by
  funext k
  simp only [CH.CompromiseZeroDiagonalCone.residual, oneTarget, ite_mul,
    zero_mul, sum_ite_eq', mem_univ, ite_true]

theorem single_columns (j u : V) (uj : u ≠ j) (r : V → ℝ) (e : ℝ)
    (normalized : col (coefficient adj) r j = -1)
    (target : col (coefficient adj) r u = e)
    (flat : ∀ k, k ≠ j → k ≠ u → col (coefficient adj) r k = 0) :
    ∀ k, col (coefficient adj) r k = (if k = j then -1 else 0) + oneTarget u e k := by
  intro k
  by_cases kj : k = j
  · subst k
    simp only [normalized, oneTarget, ite_true, ite_eq_right (Ne.symm uj), add_zero]
  · by_cases ku : k = u
    · subst k
      simp only [target, oneTarget, ite_eq_right uj, ite_true, zero_add]
    · simp only [flat k kj ku, oneTarget, ite_eq_right kj, ite_eq_right ku, add_zero]

theorem lost_retained (j v x : V) (lost : x ∈ lostSecond adj v j) : x ≠ j := by
  have member : x ∈ CH.CompromiseDeletion.lost adj (univ.erase j) v := by
    rwa [singleton_lost_eq_arc]
  exact (mem_erase.mp ((mem_lost adj (univ.erase j) v x).mp member).1).1

/-- Each private endpoint gets at least the certificate mass at its
starting vertex. This uses the actual regained-path term. -/
theorem private_endpoint_slack_bound (j : V) (r : V → ℝ)
    (fair : FairOn adj (univ.erase j) r) (v : V) (vj : v ≠ j)
    (x : V) (lost : x ∈ lostSecond adj v j) : r v ≤ col (coefficient adj) r x := by
  have xj := lost_retained adj j v x lost
  have member : x ∈ CH.CompromiseDeletion.lost adj (univ.erase j) v := by
    rwa [singleton_lost_eq_arc]
  have gained := (lost_gained_transpose adj (univ.erase j) v x
    (by simp [vj]) (by simp [xj])).mp member
  have lower : r v ≤ mass r (gainedIn adj (univ.erase j) x) :=
    single_le_sum (fun k _ => fair.1 k) gained
  exact lower.trans (retained_path_budget adj j r fair x xj)

/-- A certificate paying only target u can put positive mass only on
vertices whose private endpoints through j are all u. -/
theorem private_support (j u : V) (r : V → ℝ)
    (fair : FairOn adj (univ.erase j) r)
    (flat : ∀ k, k ≠ j → k ≠ u → col (coefficient adj) r k = 0) :
    ∀ v, 0 < r v → lostSecond adj v j ⊆ {u} := by
  intro v positive x lost
  have vj : v ≠ j := by
    intro h
    subst v
    have zero := fair.2.1 j (by simp)
    linarith
  by_contra hn
  have xu : x ≠ u := fun equal => hn (mem_singleton.mpr equal)
  have bound := private_endpoint_slack_bound adj j r fair v vj x lost
  rw [flat x (lost_retained adj j v x lost) xu] at bound
  linarith

theorem regained_zero_of_private_support (j u : V) (r : V → ℝ)
    (rn : ∀ v, 0 ≤ r v) (support : ∀ v, 0 < r v → lostSecond adj v j ⊆ {u})
    (x : V) (xj : x ≠ j) (xu : x ≠ u) :
    mass r (gainedIn adj (univ.erase j) x) = 0 := by
  apply sum_eq_zero
  intro v hv
  by_contra hn
  have positive : 0 < r v := lt_of_le_of_ne (rn v) (Ne.symm hn)
  have retained : v ∈ univ.erase j := (mem_inter.mp (mem_sdiff.mp hv).1).2
  have member := (lost_gained_transpose adj (univ.erase j) v x retained (by simp [xj])).mpr hv
  rw [singleton_lost_eq_arc] at member
  exact xu (mem_singleton.mp (support v positive member))

/-- Complete single-target test: inverse-entry capacities, the omitted
coordinate, a restriction on all private endpoints of positive residual
vertices, and the remaining target path budget. -/
theorem single_target_iff (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j u : V) (uj : u ≠ j) (e : ℝ) (en : 0 ≤ e) :
    ((∀ k, e * Q adj u k ≤ Q adj j k) ∧ e * Q adj u j = Q adj j j ∧
      (∀ v, 0 < Q adj j v - e * Q adj u v → lostSecond adj v j ⊆ {u}) ∧
      mass (fun v => Q adj j v - e * Q adj u v) (gainedIn adj (univ.erase j) u) ≤ e) ↔
    ∃ r : V → ℝ, FairOn adj (univ.erase j) r ∧ col (coefficient adj) r j = -1 ∧
      col (coefficient adj) r u = e ∧
      ∀ k, k ≠ j → k ≠ u → col (coefficient adj) r k = 0 := by
  have bj : oneTarget u e j = 0 := by simp only [oneTarget, ite_eq_right (Ne.symm uj)]
  constructor
  · rintro ⟨packing, diagonal, support, budget⟩
    have rn (v : V) : 0 ≤ Q adj j v - e * Q adj u v := sub_nonneg.mpr (packing v)
    have feasible : Admissible adj j (oneTarget u e) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k
        unfold oneTarget
        split_ifs <;> linarith
      · intro k
        simpa only [oneTarget, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] using packing k
      · simpa only [oneTarget, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] using diagonal
      · intro x xj
        rw [residual_one]
        by_cases xu : x = u
        · subst x
          simpa only [oneTarget, ite_true] using budget
        · rw [regained_zero_of_private_support adj j u _ rn support x xj xu]
          simp only [oneTarget, ite_eq_right xu, le_refl]
    obtain ⟨fair, columns⟩ := admissible_certificate adj unit j (oneTarget u e) bj feasible
    refine ⟨_, fair, ?_, ?_, ?_⟩
    · rw [columns, ite_eq_left (by rfl), bj, add_zero]
    · simp only [columns, ite_eq_right uj, zero_add, oneTarget, ite_true]
    · intro k kj ku
      simp only [columns, ite_eq_right kj, zero_add, oneTarget, ite_eq_right ku]
  · rintro ⟨r, fair, normalized, target, flat⟩
    have columns := single_columns adj j u uj r e normalized target flat
    have equal := certificate_eq_residual adj unit j (oneTarget u e) r columns
    have formula : r = fun v => Q adj j v - e * Q adj u v := equal.trans (residual_one adj j u e)
    obtain ⟨_, packing, diagonal, paths⟩ :=
      (admissible_iff adj unit j (oneTarget u e) bj).mpr ⟨r, fair, columns⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [oneTarget, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] using packing k
    · simpa only [oneTarget, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] using diagonal
    · intro v positive
      apply private_support adj j u r fair flat v
      simpa only [formula] using positive
    · have h := paths u uj
      simpa only [residual_one, oneTarget, ite_true] using h

/-- Positive diagonal removes the freedom to choose a single-target
rate. The forced ratio must be a minimum among every inverse coordinate. -/
theorem positive_diagonal_rate (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j u : V) (uj : u ≠ j) (qp : 0 < Q adj j j)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r) (e : ℝ)
    (normalized : col (coefficient adj) r j = -1)
    (target : col (coefficient adj) r u = e)
    (flat : ∀ k, k ≠ j → k ≠ u → col (coefficient adj) r k = 0) :
    0 < e ∧ 0 < Q adj u j ∧ e = Q adj j j / Q adj u j ∧
      ∀ k, Q adj j j * Q adj u k ≤ Q adj u j * Q adj j k := by
  have columns := single_columns adj j u uj r e normalized target flat
  have formula := (certificate_eq_residual adj unit j (oneTarget u e) r columns).trans
    (residual_one adj j u e)
  have rj := fair.2.1 j (by simp)
  rw [formula] at rj
  have diagonal : e * Q adj u j = Q adj j j := by linarith
  have en : 0 ≤ e := by rw [← target]; exact retained_column adj j r fair u uj
  have ep : 0 < e := by nlinarith [qn u j]
  have up : 0 < Q adj u j := by nlinarith
  refine ⟨ep, up, (eq_div_iff (ne_of_gt up)).mpr diagonal, ?_⟩
  intro k
  have bound := normalized_entry_bound adj unit qn j r fair normalized u uj k
  rw [target] at bound
  have scaled := mul_le_mul_of_nonneg_left bound up.le
  calc
    _ = (e * Q adj u j) * Q adj u k := by rw [diagonal]
    _ = Q adj u j * (e * Q adj u k) := by ring
    _ ≤ _ := scaled

/-- An off-target private endpoint forces exact saturation of the
inverse-entry capacity at its starting vertex. -/
theorem off_target_private_saturation (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j u : V) (uj : u ≠ j) (r : V → ℝ) (fair : FairOn adj (univ.erase j) r) (e : ℝ)
    (normalized : col (coefficient adj) r j = -1)
    (target : col (coefficient adj) r u = e)
    (flat : ∀ k, k ≠ j → k ≠ u → col (coefficient adj) r k = 0)
    (v x : V) (lost : x ∈ lostSecond adj v j) (xu : x ≠ u) :
    Q adj j v = e * Q adj u v := by
  have zero : r v = 0 := by
    apply le_antisymm _ (fair.1 v)
    by_contra hn
    have support := private_support adj j u r fair flat v (lt_of_not_ge hn)
    exact xu (mem_singleton.mp (support lost))
  have columns := single_columns adj j u uj r e normalized target flat
  have formula := (certificate_eq_residual adj unit j (oneTarget u e) r columns).trans
    (residual_one adj j u e)
  have value := congrFun formula v
  rw [zero] at value
  linarith

end CH.CompromiseSingleTarget

#print axioms CH.CompromiseSingleTarget.private_endpoint_slack_bound
#print axioms CH.CompromiseSingleTarget.private_support
#print axioms CH.CompromiseSingleTarget.single_target_iff
#print axioms CH.CompromiseSingleTarget.positive_diagonal_rate
#print axioms CH.CompromiseSingleTarget.off_target_private_saturation
