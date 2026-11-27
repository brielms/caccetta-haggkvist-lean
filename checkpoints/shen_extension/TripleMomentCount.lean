import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset

namespace LeanCH.BR.TripleBank
open Finset

/-- Number of selected rows whose neighbourhood contains a fixed column. -/
def columnDegree (L : Finset ℕ) (N : ℕ → Finset ℕ) (w : ℕ) : ℕ :=
  (L.filter (fun a => w ∈ N a)).card

/-- Count the incidences in a single column pool by rows. -/
theorem columnDegree_sum (L C : Finset ℕ) (N : ℕ → Finset ℕ) :
    (∑ w ∈ C, columnDegree L N w) = ∑ a ∈ L, (N a ∩ C).card := by
  classical
  have h (a) : C.filter (fun w => w ∈ N a) = N a ∩ C := by
    ext w
    simp only [mem_filter, mem_inter, and_comm]
  simp_rw [← h]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun w a => w ∈ N a)

/-- If two disjoint pools contain every head, the two column degree sums
recover the total row degree. -/
theorem columnDegree_sum_split {L A B : Finset ℕ} {N : ℕ → Finset ℕ}
    (dis : Disjoint A B) (support : ∀ a ∈ L, N a ⊆ A ∪ B) :
    (∑ w ∈ A, columnDegree L N w) + (∑ w ∈ B, columnDegree L N w) =
      ∑ a ∈ L, (N a).card := by
  rw [← sum_union dis, columnDegree_sum]
  exact sum_congr rfl (fun a ha => by rw [inter_eq_left.mpr (support a ha)])

/-- Count pairs of a column and a set of k incident rows in either order. -/
theorem columnChoose_sum (L C : Finset ℕ) (N : ℕ → Finset ℕ) (k : ℕ) :
    (∑ w ∈ C, (columnDegree L N w).choose k) =
      ∑ T ∈ L.powersetCard k, (C.filter (fun w => ∀ a ∈ T, w ∈ N a)).card := by
  classical
  let heads (w : ℕ) := L.filter (fun a => w ∈ N a)
  have eq (w : ℕ) : (heads w).powersetCard k =
      (L.powersetCard k).filter (fun T => ∀ a ∈ T, w ∈ N a) := by
    ext T
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨inc, sz⟩
      exact ⟨⟨inc.trans (filter_subset _ _), sz⟩, fun a ha => (mem_filter.mp (inc ha)).2⟩
    · rintro ⟨⟨inc, sz⟩, common⟩
      exact ⟨fun a ha => mem_filter.mpr ⟨inc ha, common a ha⟩, sz⟩
  change (∑ w ∈ C, (heads w).card.choose k) = _
  simp_rw [← card_powersetCard, eq]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (w : ℕ) (T : Finset ℕ) => ∀ a ∈ T, w ∈ N a)

/-- A common-head bound for any k rows controls the combined kth binomial
moment of the column degrees in both pools. -/
theorem columnChoose_sum_split_le {L A B : Finset ℕ} {N : ℕ → Finset ℕ} {k m : ℕ}
    (dis : Disjoint A B)
    (cap : ∀ Q ⊆ A ∪ B, k ≤ (L.filter (fun a => Q ⊆ N a)).card → Q.card ≤ m) :
    (∑ w ∈ A, (columnDegree L N w).choose k) +
      (∑ w ∈ B, (columnDegree L N w).choose k) ≤ m * L.card.choose k := by
  classical
  rw [← sum_union dis, columnChoose_sum]
  have term (T : Finset ℕ) (ht : T ∈ L.powersetCard k) :
      ((A ∪ B).filter (fun w => ∀ a ∈ T, w ∈ N a)).card ≤ m := by
    obtain ⟨inc, sz⟩ := mem_powersetCard.mp ht
    apply cap _ (filter_subset _ _)
    rw [← sz]
    exact card_le_card (fun a ha => mem_filter.mpr ⟨inc ha,
      fun w hw => (mem_filter.mp hw).2 a ha⟩)
  simpa only [sum_const, Nat.nsmul_eq_mul, card_powersetCard, mul_comm] using sum_le_sum term

end LeanCH.BR.TripleBank
