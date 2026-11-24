module

public import LeanCH.CompromiseSaturatedArc
public import LeanCH.CompromiseDiagonalLoss

set_option linter.style.header false

/-! No retained two-step path is lost when an atom at the three-halves
floor is deleted. The endpoint now follows directly from the general
zero-diagonal theorem. The earlier independent bypass proof is retained. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseNoBypass CH.CompromiseSmallIncoming CH.CompromiseMinimumWeight
open CH.CompromiseCertificateCharge CH.CompromiseAtomEndpoint CH.CompromiseSaturatedArc
open CH.CompromiseFair CH.CompromiseSubset
public section

namespace CH.CompromiseEndpointLoss

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

/-- The internal edge a->b cannot lose a private endpoint when a->j
is removed at the atom floor and b->j has no bypass. -/
theorem bypass_loss_empty [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (a b j : V)
    (aj : adj a j) (ab : adj a b) (bj : adj b j)
    (nb : newHead adj b j = 0) (boundary : 2 * w j = 3 * kappa) :
    lostSecond adj a j = ∅ := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have ip (v : V) : (inN adj v).Nonempty :=
    card_pos.mp (CH.CompromiseUnitMinimal.in_positive adj unit qn v)
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw kappa kp rows
  have small : w j < 2 * kappa := by linarith
  obtain ⟨u, bu, uj⟩ := low_weight_branches adj noDigon w hw kappa kp rows floor ip j small b bj
  obtain ⟨qjb, _, _, _, _⟩ := endpoint_inverse_row adj noDigon noTri deleted minimal
    w hw kappa kp rows b j u bj bu uj nb boundary
  have bne : b ≠ j := by intro h; subst b; exact noLoop j bj
  have bna : b ≠ a := by intro h; subst b; exact noLoop a ab
  have hsecond : j ∈ second (CH.ArcMinimal.eraseArc adj a j) a := by
    apply (mem_second _ a j).mpr
    refine ⟨?_, ?_, b, ⟨ab, fun h => bne h.2⟩, ⟨bj, fun h => bna h.1⟩⟩
    · intro h; subst j; exact noLoop a aj
    · simp [CH.ArcMinimal.eraseArc]
  have nh : newHead adj a j = 1 := by simp [newHead, hsecond]
  by_contra nonempty
  have ne : (lostSecond adj a j).Nonempty := by
    by_contra hn
    exact nonempty (not_nonempty_iff_eq_empty.mp hn)
  have bound := low_head_lost_bound adj noDigon noTri deleted minimal w hw kappa kp rows
    j small a aj
  rw [ite_eq_left hsecond] at bound
  have card : (lostSecond adj a j).card = 1 := by have hh := card_pos.mpr ne; omega
  obtain ⟨x, lost⟩ := card_eq_one.mp card
  have charge := three_deficit_charge adj noDigon noTri minimal w hw kappa kp rows
    a j b aj ab bne
  rw [nh, lost] at charge
  simp only [mass, sum_singleton] at charge
  have wx : 2 * w x = 3 * kappa := by linarith [floor x]
  obtain ⟨_, total, _⟩ := atom_endpoint_structure adj noDigon noTri deleted minimal
    w hw kappa kp rows x wx
  have gain : (2 + newHead adj a j) * w j - mass w (lostSecond adj a j) = 3 * kappa := by
    rw [nh, lost]
    simp only [mass, sum_singleton]
    linarith
  obtain ⟨p, _, _, _, _, shape, zeros⟩ :=
    saturated_inverse_certificate adj noDigon noTri deleted minimal w hw kappa kp rows
      a j b aj ab bne gain
  have pb := zeros b ab bne
  have relation := shape b
  rw [nh, lost, pb, qjb] at relation
  simp only [mass, sum_singleton] at relation
  have qxb : Q adj x b = 3 / 2 := by linarith
  exact inverse_row_not_concentrated adj noDigon unit qn x b j bj total qxb

/-- Every incoming arc at an atom attaining the floor loses no old
exact second endpoint, including the possible bypass arc. -/
theorem endpoint_arc_losses_empty [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa) :
    ∀ i, adj i j → lostSecond adj i j = ∅ := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨zero, _, _⟩ := atom_endpoint_structure adj noDigon noTri deleted minimal
    w hw kappa kp rows j boundary
  exact CH.CompromiseDiagonalLoss.zero_diagonal_arc_losses adj noLoop deleted minimal
    w hw bad j zero

/-- A retained endpoint lost through a deleted vertex is also lost
through the corresponding first arc. No graph hypothesis is needed. -/
theorem vertex_loss_to_arc (j v u : V) (h : u ∈ lost adj (univ.erase j) v) :
    adj v j ∧ u ∈ lostSecond adj v j :=
  CH.CompromiseDiagonalLoss.vertex_loss_to_arc adj j v u h

theorem endpoint_vertex_losses_empty [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa) :
    ∀ v, lost adj (univ.erase j) v = ∅ := by
  have arc := endpoint_arc_losses_empty adj noDigon noTri deleted minimal w hw kappa kp rows
    j boundary
  intro v
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨edge, loss⟩ := vertex_loss_to_arc adj j v u hu
  rw [arc v edge] at loss
  exact notMem_empty u loss

end CH.CompromiseEndpointLoss

#print axioms CH.CompromiseEndpointLoss.bypass_loss_empty
#print axioms CH.CompromiseEndpointLoss.endpoint_arc_losses_empty
#print axioms CH.CompromiseEndpointLoss.vertex_loss_to_arc
#print axioms CH.CompromiseEndpointLoss.endpoint_vertex_losses_empty
