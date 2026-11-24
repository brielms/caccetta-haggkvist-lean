module

public import LeanCH.CompromiseWitnessMultiplicity
public import LeanCH.CompromiseMinimumWeight

set_option linter.style.header false

/-! Witness multiplicity competes with inverse mass outside the head
block. Its scalar quadratic cap is already implied by the older trace
budget for minimum outdegree at least two. Neither excludes an order. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseMinimumWeight
open CH.CompromiseWitnessMultiplicity
public section

namespace CH.CompromiseWitnessBudget

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def externalIn (S : Finset V) : ℕ := ∑ a ∈ S, (inN adj a \ S).card

theorem inverse_row_budget (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (w : V → ℝ) (kappa : ℝ)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (v : V) :
    kappa * (∑ u, Q adj v u) ≤ w v := by
  have identity : payoff (CH.CompromiseInverse.matrix adj) w (Q adj v) = -w v := by
    erw [payoff_transpose]
    simp only [Q, inverse_row (CH.CompromiseInverse.matrix adj) unit]
    simp [mul_ite]
  have bound : payoff (CH.CompromiseInverse.matrix adj) w (Q adj v) ≤
      -kappa * ∑ u, Q adj v u := by
    change (∑ u, Q adj v u * row (coefficient adj) w u) ≤ _
    simp only [row_coefficient]
    calc
      _ ≤ ∑ u, Q adj v u * (-kappa) := sum_le_sum (fun u _ =>
        mul_le_mul_of_nonneg_left (rows u) (qn v u))
      _ = _ := by rw [← sum_mul]; ring
  linarith

/-- Incoming arcs from outside S already consume some of each inverse
row's mass, before its entries inside S can pay for two-step witnesses. -/
theorem block_row_budget (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ a u, adj a u → 1 ≤ 3 * Q adj u a)
    (w : V → ℝ) (kappa : ℝ) (kn : 0 ≤ kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (S : Finset V) :
    3 * kappa * block adj S S + kappa * (externalIn adj S : ℝ) ≤ 3 * mass w S := by
  have each (v : V) : 3 * kappa * mass (Q adj v) S +
      kappa * ((inN adj v \ S).card : ℝ) ≤ 3 * w v := by
    have count := sum_le_sum (s := inN adj v \ S) (fun u hu =>
      charge u v ((mem_inN adj v u).mp (mem_sdiff.mp hu).1))
    simp only [sum_const, nsmul_eq_mul, mul_one, ← mul_sum] at count
    have subset : inN adj v \ S ⊆ univ \ S := sdiff_subset_sdiff (subset_univ _) Subset.rfl
    have mono := weight_mono (Q adj v) (qn v) _ _ subset
    change ((inN adj v \ S).card : ℝ) ≤ 3 * mass (Q adj v) (inN adj v \ S) at count
    have outside : ((inN adj v \ S).card : ℝ) ≤ 3 * mass (Q adj v) (univ \ S) := by
      linarith
    have scaled := mul_le_mul_of_nonneg_left outside kn
    have split := sum_sdiff (f := Q adj v) (subset_univ S)
    change mass (Q adj v) (univ \ S) + mass (Q adj v) S = ∑ u, Q adj v u at split
    have total := inverse_row_budget adj unit qn w kappa rows v
    nlinarith
  have summed := sum_le_sum (s := S) (fun v _ => each v)
  simpa only [sum_add_distrib, ← mul_sum, block, externalIn, Nat.cast_sum, mass] using summed

theorem heads_external_count (noDigon : ∀ v u, adj v u → ¬ adj u v) (i : V) :
    (outN adj i).card ≤ externalIn adj (outN adj i) := by
  have each (a : V) (ha : a ∈ outN adj i) : 1 ≤ (inN adj a \ outN adj i).card := by
    have ia := (mem_outN adj i a).mp ha
    have member : i ∈ inN adj a \ outN adj i := by
      refine mem_sdiff.mpr ⟨(mem_inN adj a i).mpr ia, ?_⟩
      intro h
      have loop := (mem_outN adj i i).mp h
      exact noDigon i i loop loop
    exact card_pos.mpr ⟨i, member⟩
  have summed := sum_le_sum each
  simpa only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_id, externalIn] using summed

theorem full_witness_budget (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (i : V) :
    kappa * ((witnesses adj i (second adj i) : ℝ) +
      2 * (externalIn adj (outN adj i) : ℝ)) ≤ 6 * outWeight adj w i := by
  have bad (v : V) : surplus adj w v < 0 := lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have count := full_witness_bound adj noDigon deleted minimal w hw bad i
  have scaled := mul_le_mul_of_nonneg_left count kp.le
  have budget := block_row_budget adj unit qn (arc_lower adj deleted minimal w hw bad)
    w kappa kp.le rows (outN adj i)
  change _ ≤ 3 * outWeight adj w i at budget
  nlinarith

/-- The local normalized cap keeps every outside incoming arc. -/
theorem normalized_witness_budget (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v = -kappa) (i : V) :
    kappa * ((witnesses adj i (second adj i) : ℝ) +
      2 * (externalIn adj (outN adj i) : ℝ) + 1) ≤ 2 := by
  let : Nonempty V := ⟨i⟩
  have bound := full_witness_budget adj noDigon deleted minimal w hw.1 kappa kp
    (fun v => (rows v).le) i
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw.1 kappa kp
    (fun v => (rows v).le) i
  have ball := CH.WeightSeparation.ball_weight_le adj noDigon noTri w hw.1 i
  rw [hw.2] at ball
  have row := rows i
  dsimp [surplus] at row
  nlinarith

theorem normalized_degree_witness_budget (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v = -kappa) (i : V) :
    kappa * ((witnesses adj i (second adj i) : ℝ) +
      2 * ((outN adj i).card : ℝ) + 1) ≤ 2 := by
  have bound := normalized_witness_budget adj noDigon noTri deleted minimal w hw kappa kp rows i
  have external : ((outN adj i).card : ℝ) ≤ (externalIn adj (outN adj i) : ℝ) := by
    exact_mod_cast heads_external_count adj noDigon i
  have scaled := mul_le_mul_of_nonneg_left external kp.le
  nlinarith

/-- This bounds the normalized game deficit quadratically in minimum
outdegree. It does not bound that outdegree independently of the deficit. -/
theorem minimum_degree_deficit_cap (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v = -kappa)
    (R : ℕ) (positive : 0 < R) (degrees : ∀ v, R ≤ (outN adj v).card)
    (i : V) (degree : (outN adj i).card = R) :
    kappa * ((R : ℝ)^2 + 5 * R + 2) ≤ 4 := by
  have bound := normalized_degree_witness_budget adj noDigon noTri deleted minimal
    w hw kappa kp rows i
  rw [degree] at bound
  have count : (R : ℝ) * (R + 1) ≤ 2 * (witnesses adj i (second adj i) : ℝ) := by
    exact_mod_cast minimum_degree_witnesses adj noDigon R positive degrees i degree
  have scaled := mul_le_mul_of_nonneg_left count kp.le
  nlinarith

/-- A probability counterweight with equalized rows gives an equalized
dual probability from column totals of the negative inverse. No reverse
minimality assumption is required. -/
theorem equalized_dual (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kn : 0 ≤ kappa)
    (rows : ∀ v, surplus adj w v = -kappa) :
    ∃ p : V → ℝ, p ∈ simplex ∧ ∀ u, col (coefficient adj) p u = -kappa := by
  let p (v : V) : ℝ := kappa * ∑ u, Q adj u v
  have rowMass (v : V) : kappa * (∑ u, Q adj v u) = w v := by
    apply inverse_row_mass (CH.CompromiseInverse.matrix adj) unit
    intro a
    change row (coefficient adj) w a = -kappa
    rw [row_coefficient]
    exact rows a
  have ptotal : ∑ v, p v = 1 := by
    calc
      _ = kappa * ∑ v, ∑ u, Q adj u v := by simp only [p, mul_sum]
      _ = kappa * ∑ u, ∑ v, Q adj u v := by rw [sum_comm]
      _ = ∑ u, w u := by rw [mul_sum]; exact sum_congr rfl (fun u _ => rowMass u)
      _ = 1 := hw.2
  refine ⟨p, ⟨fun v => mul_nonneg kn (sum_nonneg (fun u _ => qn u v)), ptotal⟩, ?_⟩
  intro u
  have inv (a : V) : col (coefficient adj) (Q adj a) u = if u = a then -1 else 0 :=
    inverse_row (CH.CompromiseInverse.matrix adj) unit a u
  calc
    col (coefficient adj) p u = kappa * ∑ a, col (coefficient adj) (Q adj a) u := by
      simp only [col, p, mul_sum, sum_mul, mul_assoc]
      rw [sum_comm]
    _ = -kappa := by simp only [inv]; simp

/-- Application of the previously established trace bound to the same
normalized equalized deficit used by the witness bounds. -/
theorem equalized_trace_budget (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v = -kappa) :
    kappa * ((CH.ArcMinimal.arcCount adj : ℝ) - (Fintype.card V : ℝ) +
      ∑ v, Q adj v v) ≤ 1 := by
  have bad (v : V) : surplus adj w v < 0 := by rw [rows v]; linarith
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw.1 bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  obtain ⟨p, hp, cols⟩ := equalized_dual adj unit qn w hw kappa kp.le rows
  exact arc_trace_bound adj noDigon noTri unit qn (arc_lower adj deleted minimal w hw.1 bad)
    p hp kappa kp.le cols

theorem global_degree_deficit_budget (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v = -kappa)
    (R : ℕ) (degrees : ∀ v, R ≤ (outN adj v).card) :
    kappa * (Fintype.card V : ℝ) * ((R : ℝ) - 1) ≤ 1 := by
  have bad (v : V) : surplus adj w v < 0 := by rw [rows v]; linarith
  obtain ⟨_, sign⟩ := graph_inverse_nonpos adj deleted w hw.1 bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have nonnegative : 0 ≤ ∑ v, Q adj v v := sum_nonneg (fun v _ => qn v v)
  have edgeLower : (Fintype.card V : ℝ) * R ≤ (CH.ArcMinimal.arcCount adj : ℝ) := by
    have bound := sum_le_sum (s := (univ : Finset V)) (fun v _ => degrees v)
    simp only [sum_const, nsmul_eq_mul, card_univ, Nat.cast_id] at bound
    exact_mod_cast bound
  have lower : (Fintype.card V : ℝ) * ((R : ℝ) - 1) ≤
      (CH.ArcMinimal.arcCount adj : ℝ) - (Fintype.card V : ℝ) + ∑ v, Q adj v v := by
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left lower kp.le
  have trace := equalized_trace_budget adj noDigon noTri deleted minimal w hw kappa kp rows
  nlinarith

omit [DecidableEq V] in
theorem degree_order_bound [Nonempty V] (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (R : ℕ) (degrees : ∀ v, R ≤ (outN adj v).card) :
    2 * R + 1 ≤ Fintype.card V := by
  classical
  have internal := internal_arc_count adj noDigon univ
  simp only [inter_univ, card_univ] at internal
  have outgoing := sum_le_sum (s := (univ : Finset V)) (fun v _ => degrees v)
  simp only [sum_const, nsmul_eq_mul, card_univ, Nat.cast_id] at outgoing
  have positive : 0 < Fintype.card V := Fintype.card_pos
  have pred : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  nlinarith

omit adj [Fintype V] [DecidableEq V] [DecidableRel adj] in
/-- The older global trace budget already implies the new scalar cap
for R >= 2. This comparison does not discard the local witness data. -/
theorem trace_implies_degree_cap (n R : ℕ) (degree : 2 ≤ R) (order : 2 * R + 1 ≤ n)
    (kappa : ℝ) (kn : 0 ≤ kappa)
    (trace : kappa * n * ((R : ℝ) - 1) ≤ 1) :
    kappa * ((R : ℝ)^2 + 5 * R + 2) ≤ 4 := by
  have dr : 2 ≤ (R : ℝ) := by exact_mod_cast degree
  have nr : 2 * (R : ℝ) + 1 ≤ n := by exact_mod_cast order
  have product := mul_le_mul_of_nonneg_right nr (by linarith : 0 ≤ (R : ℝ) - 1)
  have quadratic := mul_nonneg (by linarith : 0 ≤ (R : ℝ) - 2) (by positivity : 0 ≤ (R : ℝ))
  have coefficient : (R : ℝ)^2 + 5 * R + 2 ≤ 4 * n * ((R : ℝ) - 1) := by
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left coefficient kn
  nlinarith

omit adj [Fintype V] [DecidableEq V] [DecidableRel adj] in
/-- The two numerical upper bounds alone remain compatible with a
positive deficit for every order and degree parameter. No graph is built. -/
theorem numerical_caps_compatible (n R : ℕ) : ∃ kappa : ℝ, 0 < kappa ∧
    3 * n * kappa ≤ 2 ∧ kappa * ((R : ℝ)^2 + 5 * R + 2) ≤ 4 := by
  let d : ℝ := 3 * n + (R : ℝ)^2 + 5 * R + 2
  have dp : 0 < d := by dsimp [d]; positivity
  have kp : 0 < 1 / d := one_div_pos.mpr dp
  have equation : (1 / d) * d = 1 := div_mul_cancel₀ _ (ne_of_gt dp)
  have first : 3 * (n : ℝ) ≤ d := by
    dsimp [d]
    nlinarith [Nat.cast_nonneg (α := ℝ) R, sq_nonneg (R : ℝ)]
  have second : (R : ℝ)^2 + 5 * R + 2 ≤ d := by
    dsimp [d]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h1 := mul_le_mul_of_nonneg_left first kp.le
  have h2 := mul_le_mul_of_nonneg_left second kp.le
  exact ⟨1 / d, kp, by nlinarith, by nlinarith⟩

end CH.CompromiseWitnessBudget

#print axioms CH.CompromiseWitnessBudget.inverse_row_budget
#print axioms CH.CompromiseWitnessBudget.block_row_budget
#print axioms CH.CompromiseWitnessBudget.full_witness_budget
#print axioms CH.CompromiseWitnessBudget.normalized_witness_budget
#print axioms CH.CompromiseWitnessBudget.minimum_degree_deficit_cap
#print axioms CH.CompromiseWitnessBudget.equalized_dual
#print axioms CH.CompromiseWitnessBudget.equalized_trace_budget
#print axioms CH.CompromiseWitnessBudget.global_degree_deficit_budget
#print axioms CH.CompromiseWitnessBudget.degree_order_bound
#print axioms CH.CompromiseWitnessBudget.trace_implies_degree_cap
#print axioms CH.CompromiseWitnessBudget.numerical_caps_compatible
