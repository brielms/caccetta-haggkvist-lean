module

public import LeanCH.CompromiseArcLoss
public import LeanCH.CompromiseSharedPaths

set_option linter.style.header false

/-! Private two-step paths charge the inverse diagonal at their middle.
A zero diagonal therefore makes the actual vertex deletion loss-free.
No atom-floor, equalization, or triangle-free hypothesis is needed. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseColumnCoupling CH.CompromiseSharedPaths
public section

namespace CH.CompromiseDiagonalLoss

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem lost_endpoint_edge (i j u : V) (hu : u ∈ lostSecond adj i j) : adj j u := by
  obtain ⟨hs, unique⟩ := (mem_lost_iff adj i j u).mp hu
  obtain ⟨_, _, a, hia, hau⟩ := (mem_second adj i u).mp hs
  simpa only [unique a hia hau] using hau

/-- Every private endpoint's inverse row is dominated coordinatewise
by at most three times its unique middle's inverse row. -/
theorem lost_row_bound (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j : V) (edge : adj i j) (u : V) (hu : u ∈ lostSecond adj i j) (k : V) :
    Q adj u k ≤ (2 + newHead adj i j) * Q adj j k := by
  have qn : ∀ v a, 0 ≤ Q adj v a := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w hw bad).2
  have hs : Q adj u k ≤ mass (fun a => Q adj a k) (lostSecond adj i j) :=
    single_le_sum (fun a _ => qn a k) hu
  have bound := all_column_charge adj noLoop deleted minimal w hw bad i j edge k
  split_ifs at bound <;> linarith

theorem lost_count_diagonal (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j : V) (edge : adj i j) :
    ((lostSecond adj i j).card : ℝ) ≤
      3 * (2 + newHead adj i j) * Q adj j j := by
  have charge := all_column_charge adj noLoop deleted minimal w hw bad i j edge j
  have lower := sum_le_sum (s := lostSecond adj i j) (fun u hu =>
    arc_lower adj deleted minimal w hw bad j u (lost_endpoint_edge adj i j u hu))
  simp only [sum_const, nsmul_eq_mul, ← mul_sum] at lower
  change ((lostSecond adj i j).card : ℝ) * 1 ≤
    3 * mass (fun u => Q adj u j) (lostSecond adj i j) at lower
  split_ifs at charge <;> nlinarith

theorem lost_count_le_nine_diagonal (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j : V) (edge : adj i j) :
    ((lostSecond adj i j).card : ℝ) ≤ 9 * Q adj j j := by
  have h := lost_count_diagonal adj noLoop deleted minimal w hw bad i j edge
  have qn : 0 ≤ Q adj j j := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w hw bad).2 j j
  unfold newHead at h
  split_ifs at h <;> nlinarith

theorem zero_diagonal_arc_losses (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (zero : Q adj j j = 0) : ∀ i, adj i j → lostSecond adj i j = ∅ := by
  intro i edge
  have h := lost_count_le_nine_diagonal adj noLoop deleted minimal w hw bad i j edge
  rw [zero, mul_zero] at h
  have hc : (lostSecond adj i j).card ≤ 0 := by exact_mod_cast h
  exact card_eq_zero.mp (by omega)

/-- Transfer from actual vertex deletion to the corresponding first arc. -/
theorem vertex_loss_to_arc (j v u : V) (h : u ∈ lost adj (univ.erase j) v) :
    adj v j ∧ u ∈ lostSecond adj v j := by
  obtain ⟨_, hne, hnon, ⟨a, ha, hva, hau⟩, unique⟩ := (mem_lost adj _ v u).mp h
  have aj : a = j := by simpa using ha
  subst a
  refine ⟨hva, mem_sdiff.mpr ⟨(mem_second adj v u).mpr ⟨hne, hnon, j, hva, hau⟩, ?_⟩⟩
  intro kept
  obtain ⟨_, _, b, hvb, hbu⟩ := (mem_second _ v u).mp kept
  have bj : b ≠ j := fun hb => hvb.2 ⟨rfl, hb⟩
  exact unique b (by simp [bj]) ⟨hvb.1, hbu.1⟩

theorem zero_diagonal_vertex_losses (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (zero : Q adj j j = 0) : ∀ v, lost adj (univ.erase j) v = ∅ := by
  intro v
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨edge, loss⟩ := vertex_loss_to_arc adj j v u hu
  rw [zero_diagonal_arc_losses adj noLoop deleted minimal w hw bad j zero v edge] at loss
  exact notMem_empty u loss

end CH.CompromiseDiagonalLoss

#print axioms CH.CompromiseDiagonalLoss.lost_row_bound
#print axioms CH.CompromiseDiagonalLoss.lost_count_diagonal
#print axioms CH.CompromiseDiagonalLoss.zero_diagonal_vertex_losses
