module

public import LeanCH.CompromiseEndpointUnique

set_option linter.style.header false

/-! Uniqueness of the endpoint deletion certificate prevents any other
inverse row from being supported inside the endpoint row's support.
Otherwise subtracting a small positive multiple constructs a second
genuine induced certificate. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseAtomEndpoint CH.CompromiseEndpointLoss CH.CompromiseEndpointUnique
public section

namespace CH.CompromiseEndpointSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem positive_scale_below [Finite V]
    (p q : V → ℝ) (pn : ∀ v, 0 ≤ p v) (qn : ∀ v, 0 ≤ q v)
    (support : ∀ v, 0 < q v → 0 < p v) :
    ∃ e : ℝ, 0 < e ∧ ∀ v, e * q v ≤ p v := by
  classical
  let := Fintype.ofFinite V
  let S := (univ : Finset V).filter (fun v => 0 < q v)
  by_cases ne : S.Nonempty
  · obtain ⟨k, hk, hmin⟩ := exists_min_image S (fun v => p v / q v) ne
    have qk : 0 < q k := (mem_filter.mp hk).2
    refine ⟨p k / q k, div_pos (support k qk) qk, ?_⟩
    intro v
    by_cases hv : 0 < q v
    · exact (le_div_iff₀ hv).mp (hmin v (mem_filter.mpr ⟨mem_univ v, hv⟩))
    · have hz : q v = 0 := le_antisymm (le_of_not_gt hv) (qn v)
      simpa only [hz, mul_zero] using pn v
  · refine ⟨1, by norm_num, ?_⟩
    intro v
    have hv : ¬ 0 < q v := fun h => ne ⟨v, mem_filter.mpr ⟨mem_univ v, h⟩⟩
    have hz : q v = 0 := le_antisymm (le_of_not_gt hv) (qn v)
    simpa only [hz, mul_zero] using pn v

variable (adj : V → V → Prop) [DecidableRel adj]

theorem fair_on_of_columns_no_loss (j : V) (r : V → ℝ) (rn : ∀ v, 0 ≤ r v)
    (positive : ∃ v, 0 < r v) (rj : r j = 0)
    (cols : ∀ u, u ≠ j → 0 ≤ col (coefficient adj) r u)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅) :
    FairOn adj (univ.erase j) r := by
  have support : ∀ v, v ∉ univ.erase j → r v = 0 := by
    intro v hv
    have vj : v = j := by simpa using hv
    simpa only [vj] using rj
  refine ⟨rn, support, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := positive
    have vj : v ≠ j := by intro h; subst v; linarith
    exact ⟨v, by simp [vj], hv⟩
  · intro u hu
    have gained : gainedIn adj (univ.erase j) u = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have vs : v ∈ univ.erase j := (mem_inter.mp (mem_sdiff.mp hv).1).2
      have loss := (lost_gained_transpose adj (univ.erase j) v u vs hu).mpr hv
      rw [noLoss v] at loss
      exact notMem_empty u loss
    have old := cols u (mem_erase.mp hu).1
    rw [col_coefficient] at old
    have ident := fair_deletion_identity adj r (univ.erase j) support u
    rw [gained] at ident
    simp only [mass, sum_empty, add_zero] at ident
    dsimp [localSlack] at ident
    linarith

/-- Every other inverse row has a positive entry outside the support
of the atom-floor row. This uses uniqueness of the actual induced
certificate and the absence of genuine vertex-deletion losses. -/
theorem other_row_hits_zero [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa) (x : V) (xj : x ≠ j) :
    ∃ v, Q adj j v = 0 ∧ 0 < Q adj x v := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  obtain ⟨qj, _, _⟩ := atom_endpoint_structure adj noDigon noTri deleted minimal
    w hw kappa kp rows j boundary
  have noLoss := endpoint_vertex_losses_empty adj noDigon noTri deleted minimal
    w hw kappa kp rows j boundary
  by_contra missing
  have support (v : V) (hv : 0 < Q adj x v) : 0 < Q adj j v := by
    by_contra hn
    have hz : Q adj j v = 0 := le_antisymm (le_of_not_gt hn) (qn j v)
    exact missing ⟨v, hz, hv⟩
  obtain ⟨e, ep, bound⟩ := positive_scale_below (fun v => Q adj j v)
    (fun v => Q adj x v) (qn j) (qn x) support
  let r : V → ℝ := fun v => Q adj j v - e * Q adj x v
  have rn (v : V) : 0 ≤ r v := sub_nonneg.mpr (bound v)
  have rj : r j = 0 := by
    apply le_antisymm _ (rn j)
    dsimp [r]
    rw [qj]
    nlinarith [qn x j]
  have columns (k : V) : col (coefficient adj) r k =
      (if k = j then -1 else 0) - e * (if k = x then -1 else 0) := by
    have invj := inverse_row (CH.CompromiseInverse.matrix adj) unit j k
    have invx := inverse_row (CH.CompromiseInverse.matrix adj) unit x k
    change col (coefficient adj) (fun v => Q adj j v) k = _ at invj
    change col (coefficient adj) (fun v => Q adj x v) k = _ at invx
    calc
      _ = col (coefficient adj) (fun v => Q adj j v) k -
          e * col (coefficient adj) (fun v => Q adj x v) k := by
        simp only [col, r, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
      _ = _ := by rw [invj, invx]
  have cj : col (coefficient adj) r j = -1 := by
    simp only [columns, ite_true, ite_eq_right (Ne.symm xj), mul_zero, sub_zero]
  have cx : col (coefficient adj) r x = e := by
    simp only [columns, ite_true, ite_eq_right xj]
    ring
  have cols (k : V) (kj : k ≠ j) : 0 ≤ col (coefficient adj) r k := by
    rw [columns, ite_eq_right kj]
    split_ifs <;> linarith
  have positive : ∃ v, 0 < r v := by
    by_contra hn
    push Not at hn
    have zero (v : V) : r v = 0 := le_antisymm (hn v) (rn v)
    have hc : col (coefficient adj) r j = 0 := by simp [col, zero]
    linarith
  have fair := fair_on_of_columns_no_loss adj j r rn positive rj cols noLoss
  have ray := endpoint_fair_ray adj noDigon noTri deleted minimal w hw kappa kp rows
    j boundary r fair
  have same : r = fun v => Q adj j v := by
    funext v
    have h := ray v
    rw [cj] at h
    simpa only [neg_neg, one_mul] using h
  have zero : col (coefficient adj) r x = 0 := by
    rw [same]
    have h := inverse_row (CH.CompromiseInverse.matrix adj) unit j x
    change col (coefficient adj) (fun v => Q adj j v) x = _ at h
    simpa only [ite_eq_right xj] using h
  linarith

end CH.CompromiseEndpointSupport

#print axioms CH.CompromiseEndpointSupport.positive_scale_below
#print axioms CH.CompromiseEndpointSupport.fair_on_of_columns_no_loss
#print axioms CH.CompromiseEndpointSupport.other_row_hits_zero
