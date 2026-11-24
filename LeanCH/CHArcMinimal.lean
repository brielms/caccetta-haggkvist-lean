module

public import LeanCH.CHLinearProgram
public import LeanCH.CompromisePerturbation

set_option linter.style.header false

/-! Arc-minimal CH LP counterexamples. Deleting i -> j increases one
entry of J-I-3A by three. The inverse threshold therefore gives exact
deletion certificates and degree-dependent atom bounds. Vertex-deletion
and arc-deletion hypotheses are explicit throughout. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.CompromiseInverse CH.CompromisePerturbation
public section

namespace CH.ArcMinimal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def eraseArc (i j v u : V) : Prop := adj v u ∧ ¬ (v = i ∧ u = j)

instance (i j : V) : DecidableRel (eraseArc adj i j) := fun v u => by
  unfold eraseArc
  infer_instance

@[expose] noncomputable def Q : Matrix V V ℝ := negativeInverse (CH.LinearProgram.matrix adj)

@[expose] def ArcMinimalLP : Prop :=
  ∀ i j, adj i j → ∀ w : V → ℝ, (∀ v, 0 ≤ w v) →
    ∃ v, w v + 3 * outWeight (eraseArc adj i j) w v ≤ ∑ u, w u

@[expose] def arcCount : ℕ := ∑ v, (outN adj v).card

theorem row_erase (i j : V) (edge : adj i j) (w : V → ℝ) (v : V) :
    row (raiseEntry (CH.LinearProgram.matrix adj) i j 3) w v =
      (∑ u, w u) - w v - 3 * outWeight (eraseArc adj i j) w v := by
  have he : raiseEntry (CH.LinearProgram.matrix adj) i j 3 =
      (CH.LinearProgram.matrix (eraseArc adj i j) : V → V → ℝ) := by
    funext a b
    by_cases h : a = i ∧ b = j
    · rcases h with ⟨rfl, rfl⟩
      simp only [raiseEntry, CH.LinearProgram.matrix, Matrix.of_apply, eraseArc,
        edge, true_and, and_self, not_true_eq_false, ite_true, ite_false]
      ring
    · have he : eraseArc adj i j a b ↔ adj a b := by
        simp only [eraseArc]
        exact and_iff_left h
      simp [raiseEntry, CH.LinearProgram.matrix, he, h]
  rw [he, CH.LinearProgram.row_matrix]

theorem counter_inverse (deleted : CH.LinearProgram.DeletedLP adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v)
    (bad0 : ∀ v, (∑ u, w0 u) < w0 v + 3 * outWeight adj w0 v) :
    IsUnit (CH.LinearProgram.matrix adj) ∧ ∀ v u, (CH.LinearProgram.matrix adj)⁻¹ v u ≤ 0 := by
  have full := full_of_deletedLeft _ (CH.LinearProgram.deleted_left adj deleted)
  have bad (v : V) : row (CH.LinearProgram.matrix adj) w0 v < 0 := by
    rw [CH.LinearProgram.row_matrix]
    linarith [bad0 v]
  exact ⟨matrix_isUnit _ full w0 hw0 bad, inverse_nonpos _ full w0 hw0 bad⟩

/-- Deleting a particular arc repairs the LP exactly when its inverse
entry reaches the threshold. -/
theorem deletion_iff (deleted : CH.LinearProgram.DeletedLP adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v)
    (bad0 : ∀ v, (∑ u, w0 u) < w0 v + 3 * outWeight adj w0 v)
    (i j : V) (edge : adj i j) :
    (∀ w : V → ℝ, (∀ v, 0 ≤ w v) →
      ∃ v, w v + 3 * outWeight (eraseArc adj i j) w v ≤ ∑ u, w u) ↔
        1 ≤ 3 * Q adj j i := by
  obtain ⟨unit, sign⟩ := counter_inverse adj deleted w0 hw0 bad0
  have bad (v : V) : row (CH.LinearProgram.matrix adj) w0 v < 0 := by
    rw [CH.LinearProgram.row_matrix]
    linarith [bad0 v]
  have ht := threshold_iff (CH.LinearProgram.matrix adj) unit sign w0 hw0 bad i j 3 (by norm_num)
  constructor
  · intro good
    apply ht.mp
    intro w hw
    obtain ⟨v, hv⟩ := good w hw
    refine ⟨v, ?_⟩
    rw [row_erase adj i j edge]
    linarith
  · intro h w hw
    obtain ⟨v, hv⟩ := ht.mpr h w hw
    refine ⟨v, ?_⟩
    rw [row_erase adj i j edge] at hv
    linarith

theorem arc_lower (deleted : CH.LinearProgram.DeletedLP adj) (minimal : ArcMinimalLP adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v)
    (bad0 : ∀ v, (∑ u, w0 u) < w0 v + 3 * outWeight adj w0 v) :
    ∀ i j, adj i j → 1 ≤ 3 * Q adj j i := by
  intro i j edge
  exact (deletion_iff adj deleted w0 hw0 bad0 i j edge).mp (minimal i j edge)

theorem incoming_degree_atom (unit : IsUnit (CH.LinearProgram.matrix adj))
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (w : V → ℝ) (eta : ℝ) (hn : 0 ≤ eta)
    (rows : ∀ v, row (CH.LinearProgram.matrix adj) w v = -eta) (v : V) :
    eta * (((inN adj v).card : ℝ) - 1 + Q adj v v) ≤ w v := by
  have hrow := inverse_row (CH.LinearProgram.matrix adj) unit v v
  rw [ite_eq_left (by rfl)] at hrow
  change col (CH.LinearProgram.matrix adj) (fun u => Q adj v u) v = -1 at hrow
  rw [CH.LinearProgram.col_matrix] at hrow
  have hd : ((inN adj v).card : ℝ) ≤ 3 * inWeight adj (fun u => Q adj v u) v := by
    have h := sum_le_sum (s := inN adj v)
      (fun u hu => charge u v (by simpa using hu))
    simpa [inWeight, mass, ← mul_sum] using h
  have htotal : ((inN adj v).card : ℝ) - 1 + Q adj v v ≤ ∑ u, Q adj v u := by linarith
  have hm := mul_le_mul_of_nonneg_left htotal hn
  have he := inverse_row_mass (CH.LinearProgram.matrix adj) unit w eta rows v
  change eta * (∑ u, Q adj v u) = w v at he
  rwa [he] at hm

theorem outgoing_degree_atom (unit : IsUnit (CH.LinearProgram.matrix adj))
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (p : V → ℝ) (eta : ℝ) (hn : 0 ≤ eta)
    (cols : ∀ u, col (CH.LinearProgram.matrix adj) p u = -eta) (v : V) :
    eta * (((outN adj v).card : ℝ) - 1 + Q adj v v) ≤ p v := by
  have hcol := inverse_column (CH.LinearProgram.matrix adj) unit v v
  rw [ite_eq_left (by rfl)] at hcol
  change row (CH.LinearProgram.matrix adj) (fun u => Q adj u v) v = -1 at hcol
  rw [CH.LinearProgram.row_matrix] at hcol
  have hd : ((outN adj v).card : ℝ) ≤ 3 * outWeight adj (fun u => Q adj u v) v := by
    have h := sum_le_sum (s := outN adj v)
      (fun u hu => charge v u (by simpa using hu))
    simpa [outWeight, mass, ← mul_sum] using h
  have htotal : ((outN adj v).card : ℝ) - 1 + Q adj v v ≤ ∑ u, Q adj u v := by linarith
  have hm := mul_le_mul_of_nonneg_left htotal hn
  have he := inverse_col_mass (CH.LinearProgram.matrix adj) unit p eta cols v
  change eta * (∑ u, Q adj u v) = p v at he
  rwa [he] at hm

theorem arc_trace_bound (unit : IsUnit (CH.LinearProgram.matrix adj))
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (p : V → ℝ) (hp : p ∈ simplex) (eta : ℝ) (hn : 0 ≤ eta)
    (cols : ∀ u, col (CH.LinearProgram.matrix adj) p u = -eta) :
    eta * ((arcCount adj : ℝ) - (Fintype.card V : ℝ) + ∑ v, Q adj v v) ≤ 1 := by
  have h := sum_le_sum (s := (univ : Finset V))
    (fun v _ => outgoing_degree_atom adj unit charge p eta hn cols v)
  simpa [← mul_sum, sum_add_distrib, sum_sub_distrib, hp.2, arcCount] using h

theorem arc_count_bound (unit : IsUnit (CH.LinearProgram.matrix adj))
    (sign : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (p : V → ℝ) (hp : p ∈ simplex) (eta : ℝ) (hn : 0 ≤ eta)
    (cols : ∀ u, col (CH.LinearProgram.matrix adj) p u = -eta) :
    eta * ((arcCount adj : ℝ) - (Fintype.card V : ℝ)) ≤ 1 := by
  have hb := arc_trace_bound adj unit charge p hp eta hn cols
  have hs : 0 ≤ ∑ v, Q adj v v := sum_nonneg (fun v _ => sign v v)
  have hm := mul_nonneg hn hs
  nlinarith

theorem minimum_degree_deficit (R : ℕ) (minimum : ∀ v, R ≤ (outN adj v).card)
    (p : V → ℝ) (hp : p ∈ simplex) (eta : ℝ)
    (cols : ∀ u, col (CH.LinearProgram.matrix adj) p u = -eta) :
    3 * (R : ℝ) + 1 - (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) * eta := by
  have hr (v : V) : row (CH.LinearProgram.matrix adj) (fun _ => 1) v ≤
      (Fintype.card V : ℝ) - 1 - 3 * R := by
    rw [CH.LinearProgram.row_matrix]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, outWeight, mass]
    have hd : (R : ℝ) ≤ (outN adj v).card := by exact_mod_cast minimum v
    linarith
  have he : payoff (CH.LinearProgram.matrix adj) (fun _ => 1) p =
      -(Fintype.card V : ℝ) * eta := by
    rw [payoff_transpose (CH.LinearProgram.matrix adj) (fun _ => 1) p]
    simp [cols]
  have hb := sum_le_sum (s := (univ : Finset V))
    (fun v _ => mul_le_mul_of_nonneg_left (hr v) (hp.1 v))
  change payoff (CH.LinearProgram.matrix adj) (fun _ => 1) p ≤
    ∑ v, p v * ((Fintype.card V : ℝ) - 1 - 3 * R) at hb
  rw [he, ← sum_mul, hp.2, one_mul] at hb
  linarith

/-- The inverse arc thresholds exclude a uniformly dense underlying
graph. They do not exclude a counterexample whose density is weighted. -/
theorem no_dense_thresholds (unit : IsUnit (CH.LinearProgram.matrix adj))
    (sign : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (p : V → ℝ) (hp : p ∈ simplex) (eta : ℝ) (hn : 0 ≤ eta)
    (cols : ∀ u, col (CH.LinearProgram.matrix adj) p u = -eta)
    (R : ℕ) (hR : 3 ≤ R) (minimum : ∀ v, R ≤ (outN adj v).card)
    (small : Fintype.card V ≤ 3 * R) : False := by
  have hl := minimum_degree_deficit adj R minimum p hp eta cols
  have hb := arc_count_bound adj unit sign charge p hp eta hn cols
  have hnR : (Fintype.card V : ℝ) ≤ 3 * R := by exact_mod_cast small
  have hR' : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hneta : 1 ≤ (Fintype.card V : ℝ) * eta := by linarith
  have he : Fintype.card V * R ≤ arcCount adj := by
    have h := sum_le_sum (s := (univ : Finset V)) (fun v _ => minimum v)
    simpa [arcCount] using h
  have he' : (Fintype.card V : ℝ) * R ≤ (arcCount adj : ℝ) := by exact_mod_cast he
  have hm := mul_le_mul_of_nonneg_left he' hn
  have hu : ((Fintype.card V : ℝ) * eta) * ((R : ℝ) - 1) ≤ 1 := by nlinarith
  have hv := mul_le_mul_of_nonneg_right hneta (show (0 : ℝ) ≤ R - 1 by linarith)
  nlinarith

theorem no_dense_arc_minimal [Nonempty V]
    (deleted : CH.LinearProgram.DeletedLP adj) (minimal : ArcMinimalLP adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v)
    (bad0 : ∀ v, (∑ u, w0 u) < w0 v + 3 * outWeight adj w0 v)
    (R : ℕ) (hR : 3 ≤ R) (minimum : ∀ v, R ≤ (outN adj v).card)
    (small : Fintype.card V ≤ 3 * R) : False := by
  obtain ⟨unit, sign⟩ := counter_inverse adj deleted w0 hw0 bad0
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have charge := arc_lower adj deleted minimal w0 hw0 bad0
  obtain ⟨w, hw, p, hp, t, ht, _, _, _, cols⟩ :=
    CH.LinearProgram.two_sided adj deleted w0 hw0 bad0
  have hc (u : V) : col (CH.LinearProgram.matrix adj) p u = -(t - 1) := by
    rw [CH.LinearProgram.col_matrix, hp.2]
    linarith [cols u]
  exact no_dense_thresholds adj unit qn charge p hp (t - 1) (by linarith) hc R hR minimum small

end CH.ArcMinimal

#print axioms CH.ArcMinimal.deletion_iff
#print axioms CH.ArcMinimal.arc_lower
#print axioms CH.ArcMinimal.incoming_degree_atom
#print axioms CH.ArcMinimal.outgoing_degree_atom
#print axioms CH.ArcMinimal.arc_trace_bound
#print axioms CH.ArcMinimal.arc_count_bound
#print axioms CH.ArcMinimal.minimum_degree_deficit
#print axioms CH.ArcMinimal.no_dense_arc_minimal
