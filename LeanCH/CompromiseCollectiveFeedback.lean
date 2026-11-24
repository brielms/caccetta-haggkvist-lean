module

public import LeanCH.CompromiseTailCut
public import LeanCH.CompromiseZeroDiagonal

set_option linter.style.header false

/-! Collective path losses obstruct a two-certificate repair at two
zero inverse diagonals. This applies to every actual deletion certificate,
without assuming that its induced retained slacks are flat. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseInverse CH.CompromisePerturbation CH.CompromiseArcMinimal
open CH.CompromiseCertificateCone CH.CompromiseZeroDiagonal CH.CompromiseTailCut
public section

namespace CH.CompromiseCollectiveFeedback

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem positive_slack_zero_inverse (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (j : V) (zero : Q adj j j = 0)
    (r : V → ℝ) (fair : FairOn adj (univ.erase j) r)
    (u : V) (uj : u ≠ j) (positive : 0 < col (coefficient adj) r u) : Q adj u j = 0 := by
  apply le_antisymm _ (qn u j)
  by_contra hn
  have tight := positive_column_tight adj unit qn j zero r fair u uj (lt_of_not_ge hn)
  linarith

/-- If removing both heads loses an endpoint, the two zero-diagonal
vertex deletions cannot have simultaneously positive cross slacks. -/
theorem joint_loss_cross_product_zero (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedSubgraphMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (proper : B ≠ outN adj i)
    (j k : V) (jk : j ≠ k) (heads : removedHeads adj i B = {j, k})
    (lost : (lostEndpoints adj i B).Nonempty)
    (qj : Q adj j j = 0) (qk : Q adj k k = 0)
    (r s : V → ℝ) (rf : FairOn adj (univ.erase j) r) (sf : FairOn adj (univ.erase k) s) :
    col (coefficient adj) r k * col (coefficient adj) s j = 0 := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w0 hw0 bad0
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have rn := retained_column adj j r rf k (Ne.symm jk)
  have sn := retained_column adj k s sf j jk
  by_cases rz : col (coefficient adj) r k = 0
  · rw [rz, zero_mul]
  by_cases sz : col (coefficient adj) s j = 0
  · rw [sz, mul_zero]
  have qkj := positive_slack_zero_inverse adj unit qn j qj r rf k (Ne.symm jk)
    (lt_of_le_of_ne rn (Ne.symm rz))
  have qjk := positive_slack_zero_inverse adj unit qn k qk s sf j jk
    (lt_of_le_of_ne sn (Ne.symm sz))
  have block : ∀ a ∈ removedHeads adj i B, ∀ b ∈ removedHeads adj i B, Q adj a b = 0 := by
    intro a ha b hb
    rw [heads] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  have empty := zero_block_losses_empty adj noDigon deleted minimal
    w0 hw0 bad0 i B subset proper block
  exact (lost.ne_empty empty).elim

end CH.CompromiseCollectiveFeedback

#print axioms CH.CompromiseCollectiveFeedback.positive_slack_zero_inverse
#print axioms CH.CompromiseCollectiveFeedback.joint_loss_cross_product_zero
