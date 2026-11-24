module

public import LeanCH.CompromiseCertificateCone

set_option linter.style.header false

/-! At an atom-floor endpoint every induced fair certificate lies on
one ray, and its probability normalization is unique. Thus choosing a
different certificate of this same deletion cannot avoid its parents. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseNoBypass CH.CompromiseSmallIncoming CH.CompromiseMinimumWeight
open CH.CompromiseAtomEndpoint CH.CompromiseEndpointDeletion CH.CompromiseCertificateCone
public section

namespace CH.CompromiseEndpointUnique

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem one_parent_ray (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (j i u : V) (one : inN adj j = {i}) (other : adj i u) (uj : u ≠ j)
    (entry : Q adj j i = 1 / 2) (total : (∑ k, Q adj j k) = 3 / 2)
    (r : V → ℝ) (hr : FairOn adj (univ.erase j) r)
    (bound : ∀ v, r v ≤ (-col (coefficient adj) r j) * Q adj j v) :
    ∀ v, r v = (-col (coefficient adj) r j) * Q adj j v := by
  let t := -col (coefficient adj) r j
  have lower : -2 * r i ≤ col (coefficient adj) r j := by
    rw [col_coefficient]
    have ho := weight_nonneg r hr.1 (outN adj j)
    have hs := weight_nonneg r hr.1 (secondIn adj j)
    simp only [slack, one, mass, sum_singleton]
    simp only [mass] at ho hs
    linarith
  have ri : r i = t / 2 := by
    have hi := bound i
    rw [entry] at hi
    dsimp [t]
    linarith
  have tail := tail_at adj noDigon noTri r hr.1 i u other (retained_column adj j r hr u uj)
  have below : (3 / 2 : ℝ) * t ≤ ∑ v, r v := by rw [ri] at tail; linarith [hr.1 u]
  have above := sum_le_sum (s := (univ : Finset V)) (fun v _ => bound v)
  rw [← mul_sum, total] at above
  have equal : (∑ v, r v) = ∑ v, (-col (coefficient adj) r j) * Q adj j v := by
    rw [← mul_sum, total]
    dsimp [t] at below
    linarith
  exact equality_of_domination_total _ r bound equal

theorem two_parent_ray (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j a b u : V) (pair : inN adj j = {a, b}) (ab : adj a b)
    (bj : b ≠ j) (other : adj b u) (uj : u ≠ j)
    (qa : Q adj j a = 1 / 3) (qb : Q adj j b = 1 / 2)
    (qj : Q adj j j = 0) (total : (∑ k, Q adj j k) = 3 / 2)
    (r : V → ℝ) (hr : FairOn adj (univ.erase j) r)
    (bound : ∀ v, r v ≤ (-col (coefficient adj) r j) * Q adj j v) :
    ∀ v, r v = (-col (coefficient adj) r j) * Q adj j v := by
  let t := -col (coefficient adj) r j
  let d : V → ℝ := fun v => t * Q adj j v - r v
  have dn (v : V) : 0 ≤ d v := sub_nonneg.mpr (bound v)
  have rj : r j = 0 := hr.2.1 j (by simp)
  have dj : d j = 0 := by simp only [d, qj, rj, mul_zero, sub_self]
  have dc : col (coefficient adj) d j = 0 := residual_column adj unit j r
  have ds : (∑ v, d v) = (3 / 2 : ℝ) * t - ∑ v, r v := by
    simp only [d, sum_sub_distrib, ← mul_sum, total]
    ring
  have da : d a = t / 3 - r a := by dsimp [d]; rw [qa]; ring
  have db : d b = t / 2 - r b := by dsimp [d]; rw [qb]; ring
  have abne : a ≠ b := by intro h; subst b; exact noDigon a a ab ab
  have inside : inWeight adj d j = d a + d b := by simp [inWeight, mass, pair, abne]
  have charged := closed_in_at adj noDigon noTri d dn j (by rw [dc])
  rw [inside, dj] at charged
  have first := tail_at adj noDigon noTri r hr.1 a b ab (retained_column adj j r hr b bj)
  have last := tail_at adj noDigon noTri r hr.1 b u other (retained_column adj j r hr u uj)
  have zero : (∑ v, d v) = 0 := by linarith [dn a, dn b, hr.1 u]
  have equal : (∑ v, r v) = ∑ v, (-col (coefficient adj) r j) * Q adj j v := by
    rw [← mul_sum, total]
    dsimp [t] at ds
    linarith
  exact equality_of_domination_total _ r bound equal

/-- Every genuine induced certificate is the same inverse row up to
its negative omitted-column slack. No probability assumption is needed. -/
theorem endpoint_fair_ray [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa)
    (r : V → ℝ) (hr : FairOn adj (univ.erase j) r) :
    ∀ v, r v = (-col (coefficient adj) r j) * Q adj j v := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have bound := (deleted_domination adj deleted w hw bad j r hr).2
  obtain ⟨qj, total, i, ij, nb, qi, _⟩ := atom_endpoint_structure adj noDigon noTri deleted
    minimal w hw kappa kp rows j boundary
  have ip (v : V) : (inN adj v).Nonempty :=
    card_pos.mp (CH.CompromiseUnitMinimal.in_positive adj unit qn v)
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw kappa kp rows
  have branches := low_weight_branches adj noDigon w hw kappa kp rows floor ip j
    (by linarith)
  rcases below_five_thirds_shape adj noDigon noTri deleted minimal w hw kappa kp rows
      j (by linarith) with ⟨a, one⟩ | ⟨a, b, _, pair, ab⟩
  · have ia : i = a := by simpa [one] using (mem_inN adj j i).mpr ij
    have oneI : inN adj j = {i} := by simpa only [ia] using one
    obtain ⟨u, other, uj⟩ := branches i ij
    exact one_parent_ray adj noDigon noTri j i u oneI other uj qi total r hr bound
  · have aj : adj a j := (mem_inN adj j a).mp (by simp [pair])
    have bj : adj b j := (mem_inN adj j b).mp (by simp [pair])
    have ib : i = b := by
      have ni : i ∈ noBypassParents adj j := by
        refine mem_filter.mpr ⟨(mem_inN adj j i).mpr ij, ?_⟩
        intro h
        simp [CH.CompromiseLostArc.newHead, h] at nb
      have sink := (no_bypass_iff adj noLoop j i).mp ni
      have cases : i = a ∨ i = b := by simpa [pair] using (mem_inN adj j i).mpr ij
      rcases cases with ia | ib
      · exact (sink.2 b (by simp [pair]) (by simpa only [ia] using ab)).elim
      · exact ib
    have qb : Q adj j b = 1 / 2 := by simpa only [ib] using qi
    have bne : b ≠ j := by
      intro h
      exact noLoop j (by simpa only [h] using bj)
    have cb : col (coefficient adj) (fun v => Q adj j v) b = 0 := by
      have h := inverse_row (CH.CompromiseInverse.matrix adj) unit j b
      change col (coefficient adj) (fun v => Q adj j v) b = if b = j then -1 else 0 at h
      simpa only [ite_eq_right bne] using h
    have above := tail_at adj noDigon noTri (fun v => Q adj j v) (qn j) a b ab (by rw [cb])
    rw [qb, total] at above
    have below := arc_lower adj deleted minimal w hw bad a j aj
    have qa : Q adj j a = 1 / 3 := by linarith
    obtain ⟨u, other, uj⟩ := branches b bj
    exact two_parent_ray adj noDigon noTri unit j a b u pair ab bne other uj
      qa qb qj total r hr bound

theorem endpoint_probability_unique [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa)
    (r : V → ℝ) (hr : FairOn adj (univ.erase j) r) (prob : r ∈ simplex) :
    ∀ v, r v = (2 / 3) * Q adj j v := by
  have ray := endpoint_fair_ray adj noDigon noTri deleted minimal w hw kappa kp rows
    j boundary r hr
  obtain ⟨_, total, _⟩ := atom_endpoint_structure adj noDigon noTri deleted minimal
    w hw kappa kp rows j boundary
  have sum := prob.2
  simp_rw [ray] at sum
  rw [← mul_sum, total] at sum
  have scale : -col (coefficient adj) r j = 2 / 3 := by linarith
  intro v
  rw [ray v, scale]

theorem endpoint_exists_unique [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa) :
    ∃! p : V → ℝ, p ∈ simplex ∧ FairOn adj (univ.erase j) p := by
  obtain ⟨_, p, hp, fair, shape, _⟩ := endpoint_deleted_certificate adj noDigon noTri
    deleted minimal w hw kappa kp rows j boundary
  refine ⟨p, ⟨hp, fair⟩, ?_⟩
  rintro r ⟨hr, fr⟩
  funext v
  rw [endpoint_probability_unique adj noDigon noTri deleted minimal w hw kappa kp rows
    j boundary r fr hr v, shape v]

end CH.CompromiseEndpointUnique

#print axioms CH.CompromiseEndpointUnique.endpoint_fair_ray
#print axioms CH.CompromiseEndpointUnique.endpoint_probability_unique
#print axioms CH.CompromiseEndpointUnique.endpoint_exists_unique
