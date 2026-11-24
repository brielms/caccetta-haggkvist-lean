module

public import LeanCH.CompromiseEndpointLoss

set_option linter.style.header false

/-! The genuine vertex deletion at an atom-floor endpoint is loss-free.
Its normalized inverse row is a fair certificate with zero retained
slacks. This identifies why that deletion supplies no contradiction. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseFair CH.CompromiseSubset CH.CompromiseAtomEndpoint
open CH.CompromiseEndpointLoss
public section

namespace CH.CompromiseEndpointDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem local_second_eq_of_no_loss (j : V)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅) (v : V) :
    localSecond adj (univ.erase j) v = second adj v ∩ univ.erase j := by
  apply subset_antisymm (localSecond_subset adj _ v)
  have h := noLoss v
  exact sdiff_eq_empty_iff_subset.mp h

theorem zero_slack_fair_on (j : V) (p : V → ℝ) (hp : p ∈ simplex) (pj : p j = 0)
    (cols : ∀ u, u ≠ j → col (coefficient adj) p u = 0)
    (noLoss : ∀ v, lost adj (univ.erase j) v = ∅) :
    FairOn adj (univ.erase j) p ∧
      ∀ u, u ≠ j → localSlack adj p (univ.erase j) u = 0 := by
  have support : ∀ v, v ∉ univ.erase j → p v = 0 := by
    intro v hv
    have vj : v = j := by simpa using hv
    simpa only [vj] using pj
  have localZero (u : V) (hu : u ≠ j) : localSlack adj p (univ.erase j) u = 0 := by
    have us : u ∈ univ.erase j := by simp [hu]
    have gained : gainedIn adj (univ.erase j) u = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have vs : v ∈ univ.erase j := (mem_inter.mp (mem_sdiff.mp hv).1).2
      have loss := (lost_gained_transpose adj (univ.erase j) v u vs us).mpr hv
      rw [noLoss v] at loss
      exact notMem_empty u loss
    have old := cols u hu
    rw [col_coefficient] at old
    have ident := fair_deletion_identity adj p (univ.erase j) support u
    rw [gained] at ident
    simp only [mass, sum_empty, add_zero] at ident
    linarith
  refine ⟨⟨hp.1, support, ?_, ?_⟩, localZero⟩
  · obtain ⟨v, hv⟩ := simplex_has_positive hp
    have vj : v ≠ j := by intro h; subst v; linarith
    exact ⟨v, by simp [vj], hv⟩
  · intro u hu
    have hh := localZero u (mem_erase.mp hu).1
    dsimp [localSlack] at hh
    linarith

/-- The canonical row of the full inverse is also a genuine induced
certificate; every retained column is exactly tight. -/
theorem endpoint_deleted_certificate [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa) :
    (∀ v, localSecond adj (univ.erase j) v = second adj v ∩ univ.erase j) ∧
      ∃ p ∈ simplex, FairOn adj (univ.erase j) p ∧
        (∀ v, p v = (2 / 3) * Q adj j v) ∧
        ∀ u, u ≠ j → localSlack adj p (univ.erase j) u = 0 := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  obtain ⟨qj, total, _⟩ := atom_endpoint_structure adj noDigon noTri deleted minimal
    w hw kappa kp rows j boundary
  have noLoss := endpoint_vertex_losses_empty adj noDigon noTri deleted minimal
    w hw kappa kp rows j boundary
  let p : V → ℝ := fun v => (2 / 3) * Q adj j v
  have hp : p ∈ simplex := by
    refine ⟨fun v => mul_nonneg (by norm_num) (qn j v), ?_⟩
    dsimp [p]
    rw [← mul_sum, total]
    norm_num
  have pj : p j = 0 := by dsimp [p]; rw [qj, mul_zero]
  have cols (u : V) (hu : u ≠ j) : col (coefficient adj) p u = 0 := by
    have inv := inverse_row (CH.CompromiseInverse.matrix adj) unit j u
    change col (coefficient adj) (fun v => Q adj j v) u = if u = j then -1 else 0 at inv
    have scale : col (coefficient adj) p u =
        (2 / 3) * col (coefficient adj) (fun v => Q adj j v) u := by
      simp only [col, p, mul_assoc, ← mul_sum]
    rw [scale, inv, ite_eq_right hu, mul_zero]
  obtain ⟨fair, zero⟩ := zero_slack_fair_on adj j p hp pj cols noLoss
  exact ⟨local_second_eq_of_no_loss adj j noLoss, p, hp, fair, fun _ => rfl, zero⟩

end CH.CompromiseEndpointDeletion

#print axioms CH.CompromiseEndpointDeletion.local_second_eq_of_no_loss
#print axioms CH.CompromiseEndpointDeletion.zero_slack_fair_on
#print axioms CH.CompromiseEndpointDeletion.endpoint_deleted_certificate
