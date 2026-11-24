module

public import LeanCH.CompromiseZeroDiagonalCone

set_option linter.style.header false

/-! The exact certificate cone for every vertex deletion. Positive
inverse diagonals require both the omitted-coordinate equation and
payment for all actual regained paths. No loss-free assumption is used. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseCertificateCone CH.CompromiseZeroDiagonalCone
public section

namespace CH.CompromiseDeletionCone

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem retained_path_budget (j : V) (r : V → ℝ)
    (fair : FairOn adj (univ.erase j) r) (u : V) (uj : u ≠ j) :
    mass r (gainedIn adj (univ.erase j) u) ≤ col (coefficient adj) r u := by
  have identity := fair_deletion_identity adj r (univ.erase j) fair.2.1 u
  rw [← col_coefficient] at identity
  have nonnegative := fair.2.2.2 u (by simp [uj])
  dsimp [localSlack] at identity
  linarith

theorem fair_on_of_path_budget (j : V) (r : V → ℝ) (rn : ∀ v, 0 ≤ r v)
    (positive : ∃ v, 0 < r v) (rj : r j = 0)
    (budget : ∀ u, u ≠ j → mass r (gainedIn adj (univ.erase j) u) ≤
      col (coefficient adj) r u) : FairOn adj (univ.erase j) r := by
  have support : ∀ v, v ∉ univ.erase j → r v = 0 := by
    intro v hv
    have vj : v = j := by simpa using hv
    simpa only [vj] using rj
  refine ⟨rn, support, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := positive
    have vj : v ≠ j := by intro h; subst v; linarith
    exact ⟨v, by simp [vj], hv⟩
  · intro u hu
    have identity := fair_deletion_identity adj r (univ.erase j) support u
    rw [← col_coefficient] at identity
    have bound := budget u (mem_erase.mp hu).1
    dsimp [localSlack] at identity
    linarith

theorem certificate_eq_residual (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (b r : V → ℝ)
    (columns : ∀ k, col (coefficient adj) r k = (if k = j then -1 else 0) + b k) :
    r = residual adj j b := by
  funext k
  have recover := inverse_recovery (CH.CompromiseInverse.matrix adj) unit r k
  change r k = -∑ u, col (coefficient adj) r u * Q adj u k at recover
  have identity : (∑ u, col (coefficient adj) r u * Q adj u k) =
      -Q adj j k + ∑ u, b u * Q adj u k := by
    simp only [columns, add_mul, sum_add_distrib]
    simp [ite_mul]
  rw [identity] at recover
  dsimp [CH.CompromiseZeroDiagonalCone.residual]
  linarith

@[expose] noncomputable def Admissible (j : V) (b : V → ℝ) : Prop :=
  (∀ u, 0 ≤ b u) ∧
    (∀ k, (∑ u, b u * Q adj u k) ≤ Q adj j k) ∧
    (∑ u, b u * Q adj u j) = Q adj j j ∧
    ∀ u, u ≠ j → mass (residual adj j b) (gainedIn adj (univ.erase j) u) ≤ b u

/-- The packing, diagonal equality, and regained-path inequalities
are sufficient for a genuine induced certificate with omitted slack -1. -/
theorem admissible_certificate (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (b : V → ℝ) (bj : b j = 0) (feasible : Admissible adj j b) :
    FairOn adj (univ.erase j) (residual adj j b) ∧
      ∀ k, col (coefficient adj) (residual adj j b) k =
        (if k = j then -1 else 0) + b k := by
  obtain ⟨_, packing, diagonal, paths⟩ := feasible
  have rn (k : V) : 0 ≤ residual adj j b k := sub_nonneg.mpr (packing k)
  have rj : residual adj j b j = 0 := by
    simp only [CH.CompromiseZeroDiagonalCone.residual, diagonal, sub_self]
  have cj : col (coefficient adj) (residual adj j b) j = -1 := by
    rw [residual_columns adj unit, ite_eq_left (by rfl), bj, add_zero]
  have positive : ∃ k, 0 < residual adj j b k := by
    by_contra hn
    push Not at hn
    have zero (k : V) : residual adj j b k = 0 := le_antisymm (hn k) (rn k)
    have cz : col (coefficient adj) (residual adj j b) j = 0 := by
      simp only [col, zero, zero_mul, sum_const_zero]
    linarith
  refine ⟨fair_on_of_path_budget adj j _ rn positive rj ?_, residual_columns adj unit j b⟩
  intro u uj
  rw [residual_columns adj unit, ite_eq_right uj, zero_add]
  exact paths u uj

/-- Exact at every inverse diagonal, including positive ones. The
right side uses actual induced neighbourhoods and the same certificate
in every retained column. -/
theorem admissible_iff (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (b : V → ℝ) (bj : b j = 0) :
    Admissible adj j b ↔ ∃ r : V → ℝ, FairOn adj (univ.erase j) r ∧
      ∀ k, col (coefficient adj) r k = (if k = j then -1 else 0) + b k := by
  constructor
  · intro feasible
    exact ⟨residual adj j b, admissible_certificate adj unit j b bj feasible⟩
  · rintro ⟨r, fair, columns⟩
    have equal := certificate_eq_residual adj unit j b r columns
    have rn (k : V) : 0 ≤ residual adj j b k := by rw [← equal]; exact fair.1 k
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u
      by_cases uj : u = j
      · simp only [uj, bj, le_refl]
      · have nonnegative := retained_column adj j r fair u uj
        simpa only [columns, ite_eq_right uj, zero_add] using nonnegative
    · intro k
      exact sub_nonneg.mp (rn k)
    · have rj : residual adj j b j = 0 := by rw [← equal]; exact fair.2.1 j (by simp)
      dsimp [CH.CompromiseZeroDiagonalCone.residual] at rj
      linarith
    · intro u uj
      have budget := retained_path_budget adj j r fair u uj
      rw [columns, ite_eq_right uj, zero_add] at budget
      simpa only [equal] using budget

theorem fair_div_positive (j : V) (r : V → ℝ) (fair : FairOn adj (univ.erase j) r)
    (t : ℝ) (tp : 0 < t) : FairOn adj (univ.erase j) (fun v => r v / t) := by
  refine ⟨fun v => div_nonneg (fair.1 v) tp.le, ?_, ?_, ?_⟩
  · intro v hv
    change r v / t = 0
    rw [fair.2.1 v hv, zero_div]
  · obtain ⟨v, hv, positive⟩ := fair.2.2.1
    exact ⟨v, hv, div_pos positive tp⟩
  · intro u hu
    have h := fair.2.2.2 u hu
    have scaled := div_le_div_of_nonneg_right h tp.le
    simpa only [mass, ← sum_div, add_div, mul_div_assoc] using scaled

/-- DeletedFair and a strict counterweight really supply a point of
each exact cone. No arc minimality or loss-free assumption is used. -/
theorem admissible_exists (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0) (j : V) :
    ∃ b : V → ℝ, b j = 0 ∧ Admissible adj j b := by
  obtain ⟨unit, _⟩ := graph_inverse_nonpos adj deleted w hw bad
  obtain ⟨r, fair⟩ := deleted j
  let t := -col (coefficient adj) r j
  have tp : 0 < t := (deleted_domination adj deleted w hw bad j r fair).1
  let p (v : V) := r v / t
  have pf : FairOn adj (univ.erase j) p := fair_div_positive adj j r fair t tp
  have normalized : col (coefficient adj) p j = -1 := by
    have scale : col (coefficient adj) p j = col (coefficient adj) r j / t := by
      simp only [col, p, div_mul_eq_mul_div, sum_div]
    rw [scale]
    apply (div_eq_iff (ne_of_gt tp)).mpr
    dsimp [t]
    ring
  let b (u : V) := if u = j then 0 else col (coefficient adj) p u
  have bj : b j = 0 := by simp only [b, ite_true]
  refine ⟨b, bj, (admissible_iff adj unit j b bj).mpr ⟨p, pf, ?_⟩⟩
  intro u
  by_cases uj : u = j
  · subst u
    simp only [normalized, b, ite_true, add_zero]
  · simp only [b, ite_eq_right uj, zero_add]

/-- The extra regained-path conditions can be written as linear
inequalities in b, with no residual vector left to choose. -/
theorem path_budget_linear (j : V) (b : V → ℝ) (u : V) :
    mass (residual adj j b) (gainedIn adj (univ.erase j) u) ≤ b u ↔
      mass (fun v => Q adj j v) (gainedIn adj (univ.erase j) u) ≤
        b u + ∑ a, b a * mass (fun v => Q adj a v) (gainedIn adj (univ.erase j) u) := by
  have identity : mass (residual adj j b) (gainedIn adj (univ.erase j) u) =
      mass (fun v => Q adj j v) (gainedIn adj (univ.erase j) u) -
        ∑ a, b a * mass (fun v => Q adj a v) (gainedIn adj (univ.erase j) u) := by
    simp only [mass, CH.CompromiseZeroDiagonalCone.residual, sum_sub_distrib, mul_sum]
    rw [sum_comm]
  rw [identity]
  constructor <;> intro h <;> linarith

end CH.CompromiseDeletionCone

#print axioms CH.CompromiseDeletionCone.retained_path_budget
#print axioms CH.CompromiseDeletionCone.admissible_certificate
#print axioms CH.CompromiseDeletionCone.admissible_iff
#print axioms CH.CompromiseDeletionCone.admissible_exists
#print axioms CH.CompromiseDeletionCone.path_budget_linear
