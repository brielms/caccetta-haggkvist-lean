module

public import LeanCH.CompromiseZeroDiagonal

set_option linter.style.header false

/-! The exact diagonal accounting keeps induced slack separate from
private paths regained through the omitted vertex. A strict shortfall
in the path term suffices for positive induced slack; no such shortfall
is assumed to follow from minimality. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseSharedPaths CH.CompromiseZeroDiagonal
public section

namespace CH.CompromiseRegainedSlack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

/-- Exact vertex losses equal the first-arc losses. This is a graph
identity; it needs neither triangle-freeness nor a counterweight. -/
theorem singleton_lost_eq_arc (j v : V) :
    lost adj (univ.erase j) v = lostSecond adj v j := by
  ext u
  constructor
  · exact fun h => (CH.CompromiseDiagonalLoss.vertex_loss_to_arc adj j v u h).2
  · intro h
    obtain ⟨hs, unique⟩ := (mem_lost_iff adj v j u).mp h
    obtain ⟨une, nonedge, a, hva, hau⟩ := (mem_second adj v u).mp hs
    have aj : a = j := unique a hva hau
    subst a
    have uj : u ≠ j := by intro he; exact nonedge (by simpa only [he] using hva)
    apply (mem_lost adj (univ.erase j) v u).mpr
    refine ⟨by simp [uj], une, nonedge, ⟨j, by simp, hva, hau⟩, ?_⟩
    intro b hb path
    exact (mem_erase.mp hb).1 (unique b path.1 path.2)

/-- The inverse diagonal is paid by two explicitly distinct terms:
actual induced slack, and actual paths lost through the deleted vertex. -/
theorem diagonal_balance (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (j : V) (r : V → ℝ) (rj : r j = 0) :
    (∑ u ∈ univ.erase j, localSlack adj r (univ.erase j) u * Q adj u j) +
      (∑ v ∈ univ.erase j, r v * mass (fun u => Q adj u j) (lostSecond adj v j)) =
        (-col (coefficient adj) r j) * Q adj j j := by
  have support : ∀ v, v ∉ (univ : Finset V).erase j → r v = 0 := by
    intro v hv
    have vj : v = j := by simpa using hv
    simpa only [vj] using rj
  have transfer := lost_gained_mass adj r (fun u => Q adj u j) (univ.erase j)
  simp_rw [singleton_lost_eq_arc] at transfer
  rw [transfer, ← sum_add_distrib]
  calc
    _ = ∑ u ∈ univ.erase j, col (coefficient adj) r u * Q adj u j := by
      apply sum_congr rfl
      intro u _
      rw [col_coefficient, fair_deletion_identity adj r (univ.erase j) support u]
      ring
    _ = _ := retained_slack_diagonal_identity adj unit j r rj

/-- A precise sufficient condition for positive induced slack. The
strict shortfall is an input, not a consequence of arc minimality. -/
theorem positive_induced_of_shortfall (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (r : V → ℝ)
    (fair : FairOn adj (univ.erase j) r)
    (shortfall : (∑ v ∈ univ.erase j,
      r v * mass (fun u => Q adj u j) (lostSecond adj v j)) <
        (-col (coefficient adj) r j) * Q adj j j) :
    ∃ u, u ≠ j ∧ 0 < localSlack adj r (univ.erase j) u ∧ 0 < Q adj u j := by
  have balance := diagonal_balance adj unit j r (fair.2.1 j (by simp))
  have positive : 0 < ∑ u ∈ univ.erase j,
      localSlack adj r (univ.erase j) u * Q adj u j := by linarith
  have witness : ∃ u ∈ univ.erase j,
      0 < localSlack adj r (univ.erase j) u * Q adj u j := by
    by_contra hn
    push Not at hn
    have nonpos := sum_nonpos (s := univ.erase j) hn
    linarith
  obtain ⟨u, hu, product⟩ := witness
  have cn : 0 ≤ localSlack adj r (univ.erase j) u := by
    have h := fair.2.2.2 u hu
    dsimp [localSlack]
    linarith
  refine ⟨u, (mem_erase.mp hu).1, ?_, ?_⟩ <;> nlinarith [qn u j]

end CH.CompromiseRegainedSlack

#print axioms CH.CompromiseRegainedSlack.singleton_lost_eq_arc
#print axioms CH.CompromiseRegainedSlack.diagonal_balance
#print axioms CH.CompromiseRegainedSlack.positive_induced_of_shortfall
