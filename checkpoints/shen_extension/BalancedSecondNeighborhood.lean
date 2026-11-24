import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Balanced Second-Neighborhood Form and Small-Degree Regular Average-Seymour Closure

Self-contained Lean 4 formalization of:
1. Exact algebraic reformulation of the balanced second-neighborhood quadratic form
   `Q_A(k) = k^T (A_2 - A) k = k^T (P_2 - E_nt) k` on any finite oriented graph.
2. Universal non-triangle arc inequality
   `k u + k w ≤ ∑_{z ∈ N⁺(u) ∩ N(w)} k z + ∑_{y ∈ N⁻(w) ∩ N(u)} k y`
   for every balanced nonnegative vector `k` (`A k = A^T k`), with immediate recovery of
   Fisher's tournament domination theorem (`Q_A(k) = 0` identically on tournaments).
3. Fundamental arc-drop identity `|E(B)| + d^2 ≤ |E(H)| + d |B|` for every vertex `v` of a
   `d`-regular oriented graph (`H = N⁺(v)`, `B = N⁺⁺(v) \ N⁺(v)`), and the 2-line bridge
   from `e_2(G) ≥ d |V|` to `|V| ≥ 3d + 1` for `d`-regular `3`-free digraphs.
4. Master integer double-counting discharging theorem `regular_e2_ge_of_surplus_witness` and
   complete elementary proofs (zero `sorry`, standard axioms only) of:
   - `regular_oriented_three_e2` (`e_2(G) ≥ 3 |V|` for every `3`-regular oriented graph),
   - `regular_threeFree_four_e2` & `regular_threeFree_four_order_ge_13`
     (`e_2(G) ≥ 4 |V|` and `|V| ≥ 13` for every `4`-regular `3`-free digraph, closing `n = 12`),
   - `regular_threeFree_five_e2` & `regular_threeFree_five_order_ge_16`
     (`e_2(G) ≥ 5 |V|` and `|V| ≥ 16` for every `5`-regular `3`-free digraph, closing `n = 15`).
-/

namespace LeanCH.BalancedSecondNeighborhood

open Finset
open scoped BigOperators

section Definitions

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An oriented graph: loopless and 2-cycle-free. -/
def IsOriented (A : V → V → Prop) : Prop :=
  (∀ v, ¬ A v v) ∧ (∀ u v, A u v → ¬ A v u)

/-- A 3-free digraph: oriented and free of directed 3-cycles. -/
def IsThreeFree (A : V → V → Prop) : Prop :=
  IsOriented A ∧ (∀ u v w, A u v → A v w → ¬ A w u)

/-- A `d`-regular digraph: every vertex has out-degree and in-degree exactly `d`. -/
def IsRegular (A : V → V → Prop) [DecidableRel A] (d : ℕ) : Prop :=
  (∀ v, (univ.filter (fun w => A v w)).card = d) ∧
  (∀ v, (univ.filter (fun u => A u v)).card = d)

/-- Out-neighborhood `N⁺(u)`. -/
def outN (A : V → V → Prop) [DecidableRel A] (u : V) : Finset V :=
  univ.filter (fun w => A u w)

/-- In-neighborhood `N⁻(u)`. -/
def inN (A : V → V → Prop) [DecidableRel A] (u : V) : Finset V :=
  univ.filter (fun w => A w u)

/-- Non-adjacent distinct vertices `N(u)`. -/
def nonAdj (A : V → V → Prop) [DecidableRel A] (u : V) : Finset V :=
  univ.filter (fun w => w ≠ u ∧ ¬ A u w ∧ ¬ A w u)

/-- Reachable in 2 steps: `∃ v, A u v ∧ A v w`. -/
def hasTwoPath (A : V → V → Prop) (u w : V) : Prop :=
  ∃ v : V, A u v ∧ A v w

instance instDecidableHasTwoPath (A : V → V → Prop) [DecidableRel A] (u w : V) :
    Decidable (hasTwoPath A u w) :=
  Fintype.decidableExistsFintype

/-- Strict second out-neighborhood `N⁺⁺(u) \ N⁺(u)`. -/
def secondN (A : V → V → Prop) [DecidableRel A] (u : V) : Finset V :=
  univ.filter (fun w => w ≠ u ∧ ¬ A u w ∧ hasTwoPath A u w)

/-- Non-adjacent ordered pair at directed distance 2 (`P_2`). -/
def isP2 (A : V → V → Prop) (u w : V) : Prop :=
  w ≠ u ∧ ¬ A u w ∧ ¬ A w u ∧ hasTwoPath A u w

instance instDecidableIsP2 (A : V → V → Prop) [DecidableRel A] (u w : V) :
    Decidable (isP2 A u w) := by
  unfold isP2; infer_instance

/-- Non-triangle arc: `w → u` with no directed 2-path `u → v → w` (`E_nt`). -/
def isEnt (A : V → V → Prop) (w u : V) : Prop :=
  A w u ∧ ¬ hasTwoPath A u w

instance instDecidableIsEnt (A : V → V → Prop) [DecidableRel A] (w u : V) :
    Decidable (isEnt A w u) := by
  unfold isEnt; infer_instance

/-- Total second-neighborhood count `e_2(G) = ∑_v |N⁺⁺(v) \ N⁺(v)|`. -/
def e2 (A : V → V → Prop) [DecidableRel A] : ℕ :=
  ∑ v : V, (secondN A v).card

/-- Internal arc count `|E(S)|` of an induced vertex subset `S`. -/
def inducedArcs (A : V → V → Prop) [DecidableRel A] (S : Finset V) : ℕ :=
  ∑ u ∈ S, (S.filter (fun v => A u v)).card

/-- Balanced (weighted Eulerian) vector `k : V → ℝ`: `A k = A^T k`. -/
def IsBalanced (A : V → V → Prop) [DecidableRel A] (k : V → ℝ) : Prop :=
  ∀ u : V, (∑ v ∈ outN A u, k v) = ∑ v ∈ inN A u, k v

@[simp] lemma mem_outN {A : V → V → Prop} [DecidableRel A] {u w : V} :
    w ∈ outN A u ↔ A u w := by simp [outN]

@[simp] lemma mem_inN {A : V → V → Prop} [DecidableRel A] {u w : V} :
    w ∈ inN A u ↔ A w u := by simp [inN]

@[simp] lemma mem_nonAdj {A : V → V → Prop} [DecidableRel A] {u w : V} :
    w ∈ nonAdj A u ↔ w ≠ u ∧ ¬ A u w ∧ ¬ A w u := by simp [nonAdj]

@[simp] lemma mem_secondN {A : V → V → Prop} [DecidableRel A] {u w : V} :
    w ∈ secondN A u ↔ w ≠ u ∧ ¬ A u w ∧ hasTwoPath A u w := by simp [secondN]

lemma card_outN_eq {A : V → V → Prop} [DecidableRel A] {d : ℕ}
    (hR : IsRegular A d) (v : V) : (outN A v).card = d := hR.1 v

lemma card_inN_eq {A : V → V → Prop} [DecidableRel A] {d : ℕ}
    (hR : IsRegular A d) (v : V) : (inN A v).card = d := hR.2 v

end Definitions

/-! ### Part 1: Exact Quadratic Identity & Universal Non-Triangle Arc Inequality -/

section BalancedQuadratic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pointwise identity underlying `k^T (A_2 - A) k = k^T (P_2 - E_nt) k`:
    for every oriented graph `A` and every `u, w`,
    `1_{w ∈ secondN u} - 1_{A w u} = 1_{isP2 u w} - 1_{isEnt w u}`. -/
lemma pointwise_secondN_sub_adj_eq_P2_sub_Ent (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) (u w : V) :
    ((if w ∈ secondN A u then (1 : ℝ) else 0) - (if A w u then 1 else 0)) =
    ((if isP2 A u w then (1 : ℝ) else 0) - (if isEnt A w u then 1 else 0)) := by
  by_cases hwu : w = u
  · subst hwu
    have hloop := hO.1 w
    simp [mem_secondN, isP2, isEnt, hloop]
  · by_cases hA_wu : A w u
    · have hA_uw : ¬ A u w := hO.2 w u hA_wu
      by_cases h2 : hasTwoPath A u w
      · simp [mem_secondN, isP2, isEnt, hwu, hA_wu, hA_uw, h2]
      · simp [mem_secondN, isP2, isEnt, hwu, hA_wu, hA_uw, h2]
    · by_cases hA_uw : A u w
      · simp [mem_secondN, isP2, isEnt, hwu, hA_wu, hA_uw]
      · by_cases h2 : hasTwoPath A u w
        · simp [mem_secondN, isP2, isEnt, hwu, hA_wu, hA_uw, h2]
        · simp [mem_secondN, isP2, isEnt, hwu, hA_wu, hA_uw, h2]

/-- Exact quadratic identity `k^T (A_2 - A) k = k^T (P_2 - E_nt) k` for every oriented graph `A`
    and every real vector `k : V → ℝ` (no nonnegativity or balance hypothesis needed). -/
theorem quadratic_eq_P2_sub_Ent (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) (k : V → ℝ) :
    (∑ u : V, ∑ w : V, if w ∈ secondN A u then k u * k w else 0) -
    (∑ u : V, ∑ w : V, if A u w then k u * k w else 0) =
    (∑ u : V, ∑ w : V, if isP2 A u w then k u * k w else 0) -
    (∑ w : V, ∑ u : V, if isEnt A w u then k w * k u else 0) := by
  have hswap1 :
      (∑ u : V, ∑ w : V, if A u w then k u * k w else 0) =
      (∑ u : V, ∑ w : V, if A w u then k u * k w else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> ring
  have hswap2 :
      (∑ w : V, ∑ u : V, if isEnt A w u then k w * k u else 0) =
      (∑ u : V, ∑ w : V, if isEnt A w u then k u * k w else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> ring
  rw [hswap1, hswap2]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  have hp := pointwise_secondN_sub_adj_eq_P2_sub_Ent A hO u w
  have hmul := congrArg (fun x : ℝ => k u * k w * x) hp
  simp only [mul_sub, mul_ite, mul_one, mul_zero] at hmul
  exact hmul

/-- Partition of `univ` relative to `u` in an oriented graph:
    `{u} ⊔ outN A u ⊔ inN A u ⊔ nonAdj A u = univ`. -/
lemma sum_univ_partition_oriented (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) (k : V → ℝ) (u : V) :
    (∑ v : V, k v) = k u + (∑ v ∈ outN A u, k v) + (∑ v ∈ inN A u, k v) +
      (∑ v ∈ nonAdj A u, k v) := by
  have hsplit : ∀ v : V,
      k v = (if v = u then k v else 0) + (if v ∈ outN A u then k v else 0) +
            (if v ∈ inN A u then k v else 0) + (if v ∈ nonAdj A u then k v else 0) := by
    intro v
    by_cases hvu : v = u
    · subst hvu; simp [hO.1 v]
    · by_cases huv : A u v
      · have hvu' : ¬ A v u := hO.2 u v huv
        simp [hvu, huv, hvu']
      · by_cases hvu' : A v u
        · simp [hvu, huv, hvu']
        · simp [hvu, huv, hvu']
  calc
    (∑ v : V, k v)
        = ∑ v : V, ((if v = u then k v else 0) + (if v ∈ outN A u then k v else 0) +
            (if v ∈ inN A u then k v else 0) + (if v ∈ nonAdj A u then k v else 0)) :=
          Finset.sum_congr rfl fun v _ => hsplit v
    _ = (∑ v : V, if v = u then k v else 0) +
        (∑ v : V, if v ∈ outN A u then k v else 0) +
        (∑ v : V, if v ∈ inN A u then k v else 0) +
        (∑ v : V, if v ∈ nonAdj A u then k v else 0) := by
          simp only [Finset.sum_add_distrib]
    _ = k u + (∑ v ∈ outN A u, k v) + (∑ v ∈ inN A u, k v) + (∑ v ∈ nonAdj A u, k v) := by
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_mem,
            Finset.univ_inter]

/-- For a balanced vector `k` (`A k = A^T k`) on an oriented graph,
    `2 (A k)_u = (∑ k) - k_u - (N k)_u`. -/
theorem balanced_out_eq_half_sub_nonAdj (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {k : V → ℝ} (hB : IsBalanced A k) (u : V) :
    2 * (∑ v ∈ outN A u, k v) = (∑ v : V, k v) - k u - (∑ v ∈ nonAdj A u, k v) := by
  have hp := sum_univ_partition_oriented A hO k u
  have hb := hB u
  linarith

/-- Forward half of the non-triangle arc inequality:
    for `w → u` with no 2-path `u → v → w`,
    `k u + k w ≤ (N k)_u - (N k)_w + 2 ∑_{z ∈ N⁺(u) ∩ N(w)} k z`. -/
lemma nonTriangle_arc_forward_bound (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {k : V → ℝ} (hk : ∀ v, 0 ≤ k v) (hB : IsBalanced A k)
    {w u : V} (hEnt : isEnt A w u) :
    k u + k w ≤ (∑ v ∈ nonAdj A u, k v) - (∑ v ∈ nonAdj A w, k v) +
      2 * (∑ z ∈ outN A u ∩ nonAdj A w, k z) := by
  have hsub : outN A u ⊆ (outN A w).erase u ∪ (outN A u ∩ nonAdj A w) := by
    intro z hz
    simp only [mem_outN] at hz
    have hzu : z ≠ u := fun h => hO.1 u (h ▸ hz)
    have hzw : z ≠ w := fun h => hO.2 w u hEnt.1 (h ▸ hz)
    have hnot_zw : ¬ A z w := fun hzw' => hEnt.2 ⟨z, hz, hzw'⟩
    by_cases hwz : A w z
    · exact mem_union_left _ (mem_erase.mpr ⟨hzu, mem_outN.mpr hwz⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨mem_outN.mpr hz, mem_nonAdj.mpr ⟨hzw, hwz, hnot_zw⟩⟩)
  have hsum_le :
      (∑ z ∈ outN A u, k z) ≤
        (∑ z ∈ (outN A w).erase u, k z) + (∑ z ∈ outN A u ∩ nonAdj A w, k z) := by
    calc
      (∑ z ∈ outN A u, k z)
          ≤ ∑ z ∈ (outN A w).erase u ∪ (outN A u ∩ nonAdj A w), k z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hk _
      _ ≤ (∑ z ∈ (outN A w).erase u, k z) + (∑ z ∈ outN A u ∩ nonAdj A w, k z) := by
            have hui := Finset.sum_union_inter (s₁ := (outN A w).erase u)
              (s₂ := outN A u ∩ nonAdj A w) (f := k)
            have hnn : 0 ≤ ∑ z ∈ (outN A w).erase u ∩ (outN A u ∩ nonAdj A w), k z :=
              Finset.sum_nonneg fun _ _ => hk _
            linarith
  have hu_mem : u ∈ outN A w := mem_outN.mpr hEnt.1
  have herase : (∑ z ∈ (outN A w).erase u, k z) + k u = ∑ z ∈ outN A w, k z :=
    Finset.sum_erase_add _ _ hu_mem
  have hbu := balanced_out_eq_half_sub_nonAdj A hO hB u
  have hbw := balanced_out_eq_half_sub_nonAdj A hO hB w
  linarith

/-- Backward half of the non-triangle arc inequality (by graph reversal):
    `k u + k w ≤ (N k)_w - (N k)_u + 2 ∑_{y ∈ N⁻(w) ∩ N(u)} k y`. -/
lemma nonTriangle_arc_backward_bound (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {k : V → ℝ} (hk : ∀ v, 0 ≤ k v) (hB : IsBalanced A k)
    {w u : V} (hEnt : isEnt A w u) :
    k u + k w ≤ (∑ v ∈ nonAdj A w, k v) - (∑ v ∈ nonAdj A u, k v) +
      2 * (∑ y ∈ inN A w ∩ nonAdj A u, k y) := by
  have hsub : inN A w ⊆ (inN A u).erase w ∪ (inN A w ∩ nonAdj A u) := by
    intro y hy
    simp only [mem_inN] at hy
    have hyw : y ≠ w := fun h => hO.1 w (h ▸ hy)
    have hyu : y ≠ u := fun h => hO.2 w u hEnt.1 (h ▸ hy)
    have hnot_uy : ¬ A u y := fun huy => hEnt.2 ⟨y, huy, hy⟩
    by_cases hyu' : A y u
    · exact mem_union_left _ (mem_erase.mpr ⟨hyw, mem_inN.mpr hyu'⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨mem_inN.mpr hy, mem_nonAdj.mpr ⟨hyu, hnot_uy, hyu'⟩⟩)
  have hsum_le :
      (∑ y ∈ inN A w, k y) ≤
        (∑ y ∈ (inN A u).erase w, k y) + (∑ y ∈ inN A w ∩ nonAdj A u, k y) := by
    calc
      (∑ y ∈ inN A w, k y)
          ≤ ∑ y ∈ (inN A u).erase w ∪ (inN A w ∩ nonAdj A u), k y :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hk _
      _ ≤ (∑ y ∈ (inN A u).erase w, k y) + (∑ y ∈ inN A w ∩ nonAdj A u, k y) := by
            have hui := Finset.sum_union_inter (s₁ := (inN A u).erase w)
              (s₂ := inN A w ∩ nonAdj A u) (f := k)
            have hnn : 0 ≤ ∑ y ∈ (inN A u).erase w ∩ (inN A w ∩ nonAdj A u), k y :=
              Finset.sum_nonneg fun _ _ => hk _
            linarith
  have hw_mem : w ∈ inN A u := mem_inN.mpr hEnt.1
  have herase : (∑ y ∈ (inN A u).erase w, k y) + k w = ∑ y ∈ inN A u, k y :=
    Finset.sum_erase_add _ _ hw_mem
  have hbu := balanced_out_eq_half_sub_nonAdj A hO hB u
  have hbw := balanced_out_eq_half_sub_nonAdj A hO hB w
  have hb_u := hB u
  have hb_w := hB w
  linarith

/-- **Universal Non-Triangle Arc Inequality:**
    For every oriented graph `A`, every balanced `k ≥ 0`, and every non-triangle arc `w → u`,
    `k u + k w ≤ ∑_{z ∈ N⁺(u) ∩ N(w)} k z + ∑_{y ∈ N⁻(w) ∩ N(u)} k y`.
    Moreover, every `z ∈ N⁺(u) ∩ N(w)` satisfies `isP2 A w z`, and every `y ∈ N⁻(w) ∩ N(u)`
    satisfies `isP2 A y u`. -/
theorem nonTriangle_arc_P2_bound (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {k : V → ℝ} (hk : ∀ v, 0 ≤ k v) (hB : IsBalanced A k)
    {w u : V} (hEnt : isEnt A w u) :
    (k u + k w ≤ (∑ z ∈ outN A u ∩ nonAdj A w, k z) + (∑ y ∈ inN A w ∩ nonAdj A u, k y)) ∧
    (∀ z ∈ outN A u ∩ nonAdj A w, isP2 A w z) ∧
    (∀ y ∈ inN A w ∩ nonAdj A u, isP2 A y u) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := nonTriangle_arc_forward_bound A hO hk hB hEnt
    have h2 := nonTriangle_arc_backward_bound A hO hk hB hEnt
    linarith
  · intro z hz
    rcases mem_inter.mp hz with ⟨huz, hzw⟩
    rw [mem_outN] at huz
    rw [mem_nonAdj] at hzw
    exact ⟨hzw.1, hzw.2.1, hzw.2.2, ⟨u, hEnt.1, huz⟩⟩
  · intro y hy
    rcases mem_inter.mp hy with ⟨hyw, hyu⟩
    rw [mem_inN] at hyw
    rw [mem_nonAdj] at hyu
    exact ⟨hyu.1.symm, hyu.2.2, hyu.2.1, ⟨w, hyw, hEnt.1⟩⟩

/-- **Fisher's Tournament Theorem (4-line corollary):**
    On any tournament `A` and any balanced `k ≥ 0`, no non-triangle arc exists between
    positive-weight vertices, and `Q_A(k) = k^T (A_2 - A) k = 0` identically. -/
theorem tournament_balanced_quadratic_eq_zero (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) (hT : ∀ u v, u ≠ v → A u v ∨ A v u)
    {k : V → ℝ} (hk : ∀ v, 0 ≤ k v) (hB : IsBalanced A k) :
    (∑ u : V, ∑ w : V, if w ∈ secondN A u then k u * k w else 0) =
    (∑ u : V, ∑ w : V, if A u w then k u * k w else 0) := by
  have hnonAdj : ∀ v, nonAdj A v = ∅ := by
    intro v
    ext x
    simp only [mem_nonAdj, notMem_empty, iff_false, not_and]
    intro hxv h1 h2
    rcases hT v x hxv.symm with h | h
    · exact h1 h
    · exact h2 h
  have hP2_zero : (∑ u : V, ∑ w : V, if isP2 A u w then k u * k w else 0) = 0 := by
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun w _ => ?_
    split_ifs with h
    · exfalso
      rcases hT u w h.1.symm with h1 | h2
      · exact h.2.1 h1
      · exact h.2.2.1 h2
    · rfl
  have hEnt_zero : (∑ w : V, ∑ u : V, if isEnt A w u then k w * k u else 0) = 0 := by
    refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h
    · have hb := (nonTriangle_arc_P2_bound A hO hk hB h).1
      simp only [hnonAdj, inter_empty, sum_empty, add_zero] at hb
      have hku : k u = 0 := by linarith [hk u, hk w]
      rw [hku, mul_zero]
    · rfl
  have hq := quadratic_eq_P2_sub_Ent A hO k
  rw [hP2_zero, hEnt_zero] at hq
  linarith

end BalancedQuadratic

/-! ### Part 2: Regular `3`-Free CH Bridge & Fundamental Arc-Drop Identity -/

section RegularBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **2-line Bridge from Average Second Neighborhood to Regular `q = 3` CH:**
    If a nonempty `d`-regular `3`-free digraph satisfies `e_2(G) ≥ d |V|`, then `3 d + 1 ≤ |V|`. -/
theorem regular_threeFree_order_ge_of_e2 (A : V → V → Prop) [DecidableRel A] {d : ℕ}
    (h3 : IsThreeFree A) (hR : IsRegular A d) (hne : Nonempty V)
    (he2 : d * Fintype.card V ≤ e2 A) :
    3 * d + 1 ≤ Fintype.card V := by
  have hrow : ∀ v : V, (outN A v).card + (inN A v).card + (secondN A v).card + 1 ≤
      Fintype.card V := by
    intro v
    have hd1 : Disjoint (outN A v) (inN A v) := by
      rw [disjoint_left]
      intro x hx1 hx2
      exact h3.1.2 v x (mem_outN.mp hx1) (mem_inN.mp hx2)
    have hd2 : Disjoint (outN A v ∪ inN A v) (secondN A v) := by
      rw [disjoint_left]
      intro x hx1 hx2
      rcases mem_secondN.mp hx2 with ⟨_, hnot_vx, ⟨m, hvm, hmx⟩⟩
      rcases mem_union.mp hx1 with h1 | h2
      · exact hnot_vx (mem_outN.mp h1)
      · exact h3.2 v m x hvm hmx (mem_inN.mp h2)
    have hv_not : v ∉ (outN A v ∪ inN A v) ∪ secondN A v := by
      simp [mem_outN, mem_inN, mem_secondN, h3.1.1 v]
    have hcard :
        ((outN A v ∪ inN A v) ∪ secondN A v).card + 1 ≤ Fintype.card V := by
      have h1 : (insert v ((outN A v ∪ inN A v) ∪ secondN A v)).card ≤ Fintype.card V :=
        card_le_univ _
      rwa [card_insert_of_notMem hv_not] at h1
    rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1] at hcard
    exact hcard
  have hsum :
      (∑ v : V, ((outN A v).card + (inN A v).card + (secondN A v).card + 1)) ≤
        ∑ _v : V, Fintype.card V :=
    Finset.sum_le_sum fun v _ => hrow v
  have hout : (∑ v : V, (outN A v).card) = d * Fintype.card V := by
    simp [outN, hR.1, mul_comm]
  have hin : (∑ v : V, (inN A v).card) = d * Fintype.card V := by
    simp [inN, hR.2, mul_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one] at hsum
  change (∑ v : V, (outN A v).card) + (∑ v : V, (inN A v).card) + e2 A + Fintype.card V ≤
    Fintype.card V * Fintype.card V at hsum
  rw [hout, hin] at hsum
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hne
  have hmul : (3 * d + 1) * Fintype.card V ≤ Fintype.card V * Fintype.card V := by
    nlinarith
  exact Nat.le_of_mul_le_mul_right hmul hpos

/-- For any vertex `v` of an oriented graph and any `a ∈ N⁺(v)`, every out-neighbor of `a`
    outside `N⁺(v)` lies in `N⁺⁺(v) \ N⁺(v)`. -/
lemma outN_sdiff_subset_secondN (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {v a : V} (ha : a ∈ outN A v) :
    outN A a \ outN A v ⊆ secondN A v := by
  intro w hw
  rcases mem_sdiff.mp hw with ⟨haw, hnot_vw⟩
  rw [mem_outN] at ha haw hnot_vw
  refine mem_secondN.mpr ⟨?_, hnot_vw, ⟨a, ha, haw⟩⟩
  intro h
  subst h
  exact hO.2 w a ha haw

/-- Every out-neighbor of `a ∈ N⁺(v)` lies in `N⁺(v) ∪ secondN A v`. -/
lemma outN_subset_outN_union_secondN (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {v a : V} (ha : a ∈ outN A v) :
    outN A a ⊆ outN A v ∪ secondN A v := by
  intro w haw
  by_cases hvw : w ∈ outN A v
  · exact mem_union_left _ hvw
  · exact mem_union_right _ (outN_sdiff_subset_secondN A hO ha (mem_sdiff.mpr ⟨haw, hvw⟩))

/-- `secondN A v` is disjoint from `outN A v`. -/
lemma disjoint_outN_secondN (A : V → V → Prop) [DecidableRel A] (v : V) :
    Disjoint (outN A v) (secondN A v) := by
  rw [disjoint_left]
  intro w hw1 hw2
  exact (mem_secondN.mp hw2).2.1 (mem_outN.mp hw1)

/-- For `a ∈ H = outN A v` in a `d`-regular oriented graph,
    `|N⁺(a) ∩ H| + |N⁺(a) ∩ B| = d` where `B = secondN A v`. -/
lemma card_outN_inter_H_add_B (A : V → V → Prop) [DecidableRel A] {d : ℕ}
    (hO : IsOriented A) (hR : IsRegular A d) {v a : V} (ha : a ∈ outN A v) :
    ((outN A v).filter (fun w => A a w)).card +
      ((secondN A v).filter (fun w => A a w)).card = d := by
  have h1 : (outN A v).filter (fun w => A a w) = outN A v ∩ outN A a := by
    ext w; simp [mem_outN]
  have h2 : (secondN A v).filter (fun w => A a w) = secondN A v ∩ outN A a := by
    ext w; simp [mem_outN]
  rw [h1, h2]
  have hd : Disjoint (outN A v ∩ outN A a) (secondN A v ∩ outN A a) :=
    (disjoint_outN_secondN A v).mono inter_subset_left inter_subset_left
  rw [← card_union_of_disjoint hd]
  have hun : (outN A v ∩ outN A a) ∪ (secondN A v ∩ outN A a) = outN A a := by
    ext w
    simp only [mem_union, mem_inter]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hw
      rcases mem_union.mp (outN_subset_outN_union_secondN A hO ha hw) with h1 | h2
      · exact Or.inl ⟨h1, hw⟩
      · exact Or.inr ⟨h2, hw⟩
  rw [hun]
  exact hR.1 a

/-- **Fundamental Arc-Drop Identity:**
    For any `d`-regular oriented graph `A` and any vertex `v`, letting `H = outN A v` and
    `B = secondN A v`,
    `|E(B)| + d * d ≤ |E(H)| + d * |B|`.
    In particular, if `v` has deficit `s = d - |B| > 0`, internal arcs drop by at least `d * s`. -/
theorem arc_drop_identity (A : V → V → Prop) [DecidableRel A] {d : ℕ}
    (hO : IsOriented A) (hR : IsRegular A d) (v : V) :
    inducedArcs A (secondN A v) + d * d ≤
      inducedArcs A (outN A v) + d * (secondN A v).card := by
  set H := outN A v
  set B := secondN A v
  -- Step 1: Total arcs from H to B equals d^2 - |E(H)|
  have hHB_eq : inducedArcs A H + (∑ a ∈ H, (B.filter (fun b => A a b)).card) = d * d := by
    unfold inducedArcs
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ a ∈ H,
        (H.filter (fun w => A a w)).card + (B.filter (fun b => A a b)).card = d :=
      fun a ha => card_outN_inter_H_add_B A hO hR ha
    have hHcard : H.card = d := card_outN_eq hR v
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hHcard]
  -- Step 2: Double-count arcs into B from H and from B (disjoint subsets!)
  have hHB_comm :
      (∑ a ∈ H, (B.filter (fun b => A a b)).card) =
        ∑ b ∈ B, (H.filter (fun a => A a b)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hBB_comm :
      inducedArcs A B = ∑ b ∈ B, (B.filter (fun b' => A b' b)).card := by
    unfold inducedArcs
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- For each b ∈ B, in-neighbors in H and in B are disjoint subsets of inN A b (size d)
  have hb_le : ∀ b ∈ B,
      (B.filter (fun b' => A b' b)).card + (H.filter (fun a => A a b)).card ≤ d := by
    intro b _
    have hdisj : Disjoint (B.filter (fun b' => A b' b)) (H.filter (fun a => A a b)) :=
      (disjoint_outN_secondN A v).symm.mono (filter_subset _ _) (filter_subset _ _)
    rw [← card_union_of_disjoint hdisj]
    have hsub : B.filter (fun b' => A b' b) ∪ H.filter (fun a => A a b) ⊆ inN A b := by
      intro x hx
      rcases mem_union.mp hx with h1 | h2
      · exact mem_inN.mpr (mem_filter.mp h1).2
      · exact mem_inN.mpr (mem_filter.mp h2).2
    exact (card_le_card hsub).trans (le_of_eq (hR.2 b))
  have hsum_B :
      inducedArcs A B + (∑ a ∈ H, (B.filter (fun b => A a b)).card) ≤ d * B.card := by
    rw [hBB_comm, hHB_comm, ← Finset.sum_add_distrib]
    calc
      (∑ b ∈ B, ((B.filter (fun b' => A b' b)).card + (H.filter (fun a => A a b)).card))
          ≤ ∑ _b ∈ B, d := Finset.sum_le_sum hb_le
      _ = d * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- **Master Discharging Theorem (pure `ℕ` double counting):**
    Let `A` be a `d`-regular graph (`d ≥ 2`). Suppose:
    1. Every vertex has `|secondN A v| ≥ d - 1` (deficit at most `1`).
    2. Every deficit vertex `v` (`|secondN A v| = d - 1`) has a witness set `C v ⊆ outN A v`
       of size `≥ d - 1` such that every `a ∈ C v` satisfies:
       - `d + 1 ≤ |secondN A a|` (surplus at least `+1`), and
       - `∃ p, A p a ∧ d ≤ |secondN A p|` (`a` has at least one non-deficit in-neighbor).
    Then `d * |V| ≤ e2 A`. -/
theorem regular_e2_ge_of_surplus_witness (A : V → V → Prop) [DecidableRel A] {d : ℕ}
    (hd : 2 ≤ d) (hR : IsRegular A d)
    (hfloor : ∀ v, d - 1 ≤ (secondN A v).card)
    (hwit : ∀ v, (secondN A v).card = d - 1 →
      ∃ C : Finset V, C ⊆ outN A v ∧ d - 1 ≤ C.card ∧
        ∀ a ∈ C, d + 1 ≤ (secondN A a).card ∧ ∃ p, A p a ∧ d ≤ (secondN A p).card) :
    d * Fintype.card V ≤ e2 A := by
  classical
  set D : Finset V := univ.filter (fun v => (secondN A v).card = d - 1)
  set S : Finset V := univ.filter (fun a => d + 1 ≤ (secondN A a).card)
  set Sstar : Finset V := S.filter (fun a => ∃ p, A p a ∧ d ≤ (secondN A p).card)
  -- Double count edges from D to Sstar:
  -- Lower bound: every v ∈ D has ≥ d - 1 out-neighbors in Sstar
  have hlow : (d - 1) * D.card ≤ ∑ v ∈ D, (Sstar.filter (fun a => A v a)).card := by
    have hrow : ∀ v ∈ D, d - 1 ≤ (Sstar.filter (fun a => A v a)).card := by
      intro v hv
      have hdv : (secondN A v).card = d - 1 := (mem_filter.mp hv).2
      obtain ⟨C, hCsub, hCcard, hCprop⟩ := hwit v hdv
      refine hCcard.trans (card_le_card ?_)
      intro a ha
      have ha_out : A v a := mem_outN.mp (hCsub ha)
      have ha_prop := hCprop a ha
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ha_prop.1⟩, ha_prop.2⟩,
        ha_out⟩
    calc
      (d - 1) * D.card = ∑ _v ∈ D, (d - 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ D, (Sstar.filter (fun a => A v a)).card := Finset.sum_le_sum hrow
  -- Upper bound: every a ∈ Sstar has a non-deficit in-neighbor, hence ≤ d - 1 in-neighbors in D
  have hhigh : (∑ v ∈ D, (Sstar.filter (fun a => A v a)).card) ≤ (d - 1) * Sstar.card := by
    have hcomm :
        (∑ v ∈ D, (Sstar.filter (fun a => A v a)).card) =
          ∑ a ∈ Sstar, (D.filter (fun v => A v a)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hcomm]
    have hcol : ∀ a ∈ Sstar, (D.filter (fun v => A v a)).card ≤ d - 1 := by
      intro a ha
      obtain ⟨p, hpa, hpd⟩ := (mem_filter.mp ha).2
      have hp_notD : p ∉ D := by
        simp only [D, mem_filter, mem_univ, true_and]
        omega
      have hsub : D.filter (fun v => A v a) ⊆ (inN A a).erase p := by
        intro v hv
        rcases mem_filter.mp hv with ⟨hvD, hva⟩
        refine mem_erase.mpr ⟨?_, mem_inN.mpr hva⟩
        intro hvp
        exact hp_notD (hvp ▸ hvD)
      have hp_in : p ∈ inN A a := mem_inN.mpr hpa
      have hcard := (card_le_card hsub).trans (le_of_eq (card_erase_of_mem hp_in))
      rw [card_inN_eq hR a] at hcard
      exact hcard
    calc
      (∑ a ∈ Sstar, (D.filter (fun v => A v a)).card)
          ≤ ∑ _a ∈ Sstar, (d - 1) := Finset.sum_le_sum hcol
      _ = (d - 1) * Sstar.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Hence |D| ≤ |Sstar| ≤ |S|
  have hD_le_S : D.card ≤ S.card := by
    have h1 : D.card ≤ Sstar.card := Nat.le_of_mul_le_mul_left (hlow.trans hhigh) (by omega)
    exact h1.trans (card_le_card (filter_subset _ _))
  -- Split e2 A into D, S, and the rest M = univ \ (D ∪ S)
  have hdisj : Disjoint D S := by
    rw [disjoint_left]
    intro v hvD hvS
    have h1 := (mem_filter.mp hvD).2
    have h2 := (mem_filter.mp hvS).2
    omega
  set M : Finset V := univ \ (D ∪ S)
  have huniv : D ∪ S ∪ M = univ := by
    ext v; simp [M]
  have hdisjM : Disjoint (D ∪ S) M := disjoint_sdiff_self_right
  have hcard_univ : Fintype.card V = D.card + S.card + M.card := by
    have h := congr_arg Finset.card huniv.symm
    rw [card_univ, card_union_of_disjoint hdisjM, card_union_of_disjoint hdisj] at h
    exact h
  have hsum_split :
      e2 A = (∑ v ∈ D, (secondN A v).card) + (∑ v ∈ S, (secondN A v).card) +
        (∑ v ∈ M, (secondN A v).card) := by
    unfold e2
    rw [← huniv, sum_union hdisjM, sum_union hdisj]
  have hsumD : (d - 1) * D.card ≤ ∑ v ∈ D, (secondN A v).card := by
    calc
      (d - 1) * D.card = ∑ _v ∈ D, (d - 1) := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ D, (secondN A v).card := sum_le_sum fun v hv => le_of_eq (mem_filter.mp hv).2.symm
  have hsumS : (d + 1) * S.card ≤ ∑ v ∈ S, (secondN A v).card := by
    calc
      (d + 1) * S.card = ∑ _v ∈ S, (d + 1) := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ S, (secondN A v).card := sum_le_sum fun v hv => (mem_filter.mp hv).2
  have hsumM : d * M.card ≤ ∑ v ∈ M, (secondN A v).card := by
    calc
      d * M.card = ∑ _v ∈ M, d := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ M, (secondN A v).card := by
        refine sum_le_sum fun v hv => ?_
        have hnotDS : v ∉ D ∪ S := (mem_sdiff.mp hv).2
        have hnotD : (secondN A v).card ≠ d - 1 := by
          intro h; exact hnotDS (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩))
        have hnotS : ¬ d + 1 ≤ (secondN A v).card := by
          intro h; exact hnotDS (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩))
        have hfl := hfloor v
        omega
  -- Combine: d*(|D|+|S|+|M|) ≤ (d-1)*|D| + (d+1)*|S| + d*|M| since |D| ≤ |S|
  rw [hcard_univ, hsum_split]
  have hD_term : d * D.card = (d - 1) * D.card + D.card := by
    have : d = (d - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  have hS_term : (d + 1) * S.card = d * S.card + S.card := by ring
  linarith

end RegularBasics

/-! ### Part 3: Small-Subset Graph Lemmas (Sinks, Cycles, Min Out-Degree) -/

section SmallGraphLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If every vertex in a finite nonempty subset `S` has at least one out-neighbor in `S`,
    then `S` contains a directed walk of arbitrary length — in particular a simple directed cycle
    inside `S` (and if `A` is oriented / 3-free, its length is `≥ 3` / `≥ 4`). -/
lemma exists_sink_of_card_lt_girth_oriented (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {S : Finset V} (hS : S.Nonempty) (hcard : S.card ≤ 2) :
    ∃ x ∈ S, (S.filter (fun y => A x y)).card = 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := hS
  have hxpos : 0 < (S.filter (fun y => A x y)).card := Nat.pos_of_ne_zero (hno x hx)
  obtain ⟨y, hy⟩ := card_pos.mp hxpos
  rcases mem_filter.mp hy with ⟨hyS, hxy⟩
  have hxy_ne : x ≠ y := fun h => hO.1 x (h ▸ hxy)
  have hypos : 0 < (S.filter (fun z => A y z)).card := Nat.pos_of_ne_zero (hno y hyS)
  obtain ⟨z, hz⟩ := card_pos.mp hypos
  rcases mem_filter.mp hz with ⟨hzS, hyz⟩
  have hzy_ne : z ≠ y := fun h => hO.1 y (h ▸ hyz)
  have hzx_ne : z ≠ x := fun h => hO.2 x y hxy (h ▸ hyz)
  have hsub : ({x, y, z} : Finset V) ⊆ S := by
    intro w hw; simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have h3 : ({x, y, z} : Finset V).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hzy_ne.symm]
    · simp [hxy_ne, hzx_ne.symm]
  have := card_le_card hsub
  omega

/-- Every nonempty `3`-free subset of size `≤ 3` has a sink. -/
lemma exists_sink_threeFree_of_card_le_three (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) {S : Finset V} (hS : S.Nonempty) (hcard : S.card ≤ 3) :
    ∃ x ∈ S, (S.filter (fun y => A x y)).card = 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := card_pos.mp (Nat.pos_of_ne_zero (hno a ha))
  rcases mem_filter.mp hb with ⟨hbS, hab⟩
  obtain ⟨c, hc⟩ := card_pos.mp (Nat.pos_of_ne_zero (hno b hbS))
  rcases mem_filter.mp hc with ⟨hcS, hbc⟩
  obtain ⟨d, hd⟩ := card_pos.mp (Nat.pos_of_ne_zero (hno c hcS))
  rcases mem_filter.mp hd with ⟨hdS, hcd⟩
  have hab_ne : a ≠ b := fun h => h3.1.1 a (h ▸ hab)
  have hbc_ne : b ≠ c := fun h => h3.1.1 b (h ▸ hbc)
  have hca_ne : c ≠ a := fun h => h3.1.2 a b hab (h ▸ hbc)
  have hdc_ne : d ≠ c := fun h => h3.1.1 c (h ▸ hcd)
  have hdb_ne : d ≠ b := fun h => h3.1.2 b c hbc (h ▸ hcd)
  have hda_ne : d ≠ a := fun h => h3.2 a b c hab hbc (h ▸ hcd)
  have hsub : ({a, b, c, d} : Finset V) ⊆ S := by
    intro w hw; simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a, b, c, d} : Finset V).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hdc_ne.symm]
    · simp [hbc_ne, hdb_ne.symm]
    · simp [hab_ne, hca_ne.symm, hda_ne.symm]
  have := card_le_card hsub
  omega

/-- Every nonempty `3`-free subset of size `≤ 4` with `inducedArcs A S ≤ 3` has a sink. -/
lemma exists_sink_threeFree_of_card_four_arcs_le_three (A : V → V → Prop) [DecidableRel A]
    {S : Finset V} (hcard : S.card = 4) (harcs : inducedArcs A S ≤ 3) :
    ∃ x ∈ S, (S.filter (fun y => A x y)).card = 0 := by
  by_contra hno
  push Not at hno
  have hge : 4 ≤ inducedArcs A S := by
    calc
      4 = ∑ _x ∈ S, 1 := by rw [sum_const, hcard, smul_eq_mul, mul_one]
      _ ≤ ∑ x ∈ S, (S.filter (fun y => A x y)).card :=
        sum_le_sum fun x hx => Nat.one_le_iff_ne_zero.mpr (hno x hx)
  omega

/-- Every subset `S` of size `4` with `inducedArcs A S ≤ 2` has at least two sinks. -/
lemma exists_two_sinks_of_card_four_arcs_le_two (A : V → V → Prop) [DecidableRel A]
    {S : Finset V} (hcard : S.card = 4) (harcs : inducedArcs A S ≤ 2) :
    2 ≤ (S.filter (fun x => (S.filter (fun y => A x y)).card = 0)).card := by
  set Z := S.filter (fun x => (S.filter (fun y => A x y)).card = 0)
  set P := S.filter (fun x => (S.filter (fun y => A x y)).card ≠ 0)
  have hZP : Z.card + P.card = 4 := by
    have hdisj : Disjoint Z P := by
      rw [disjoint_left]
      intro x hxZ hxP
      exact (mem_filter.mp hxP).2 (mem_filter.mp hxZ).2
    have hun : Z ∪ P = S := by
      ext x; simp only [Z, P, mem_union, mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx; by_cases h : (S.filter (fun y => A x y)).card = 0
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hun, hcard]
  have hP_le : P.card ≤ inducedArcs A S := by
    calc
      P.card = ∑ _x ∈ P, 1 := by rw [sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ x ∈ P, (S.filter (fun y => A x y)).card :=
        sum_le_sum fun x hx => Nat.one_le_iff_ne_zero.mpr (mem_filter.mp hx).2
      _ ≤ ∑ x ∈ S, (S.filter (fun y => A x y)).card :=
        sum_le_sum_of_subset (filter_subset _ _)
  omega

/-- Every oriented subset of size `≤ 3` has a vertex of internal out-degree `≤ 1`. -/
lemma oriented_exists_outdeg_le_one_of_card_le_three (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {S : Finset V} (hS : S.Nonempty) (hcard : S.card ≤ 3) :
    ∃ x ∈ S, (S.filter (fun y => A x y)).card ≤ 1 := by
  by_contra hno
  push Not at hno
  -- Total internal arcs ≥ 2 * |S|, while max arcs in an oriented graph is |S|*(|S|-1)/2
  have hlow : 2 * S.card ≤ inducedArcs A S := by
    calc
      2 * S.card = ∑ _x ∈ S, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ S, (S.filter (fun y => A x y)).card := sum_le_sum fun x hx => hno x hx
  have hpair : 2 * inducedArcs A S ≤ S.card * (S.card - 1) := by
    -- Each unordered pair in S contributes at most 1 to (A x y) + (A y x)
    have hsum :
        (∑ x ∈ S, ∑ y ∈ S, ((if A x y then 1 else 0) + (if A y x then 1 else 0))) ≤
          ∑ x ∈ S, ∑ y ∈ S, (if x = y then 0 else 1) := by
      refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
      by_cases hxy : x = y
      · subst hxy; simp [hO.1 x]
      · by_cases h1 : A x y
        · have h2 : ¬ A y x := hO.2 x y h1
          simp [hxy, h1, h2]
        · by_cases h2 : A y x <;> simp [hxy, h1, h2]
    have hlhs :
        (∑ x ∈ S, ∑ y ∈ S, ((if A x y then 1 else 0) + (if A y x then 1 else 0))) =
          2 * inducedArcs A S := by
      simp only [Finset.sum_add_distrib]
      have h1 : (∑ x ∈ S, ∑ y ∈ S, if A x y then 1 else 0) = inducedArcs A S := by
        unfold inducedArcs
        refine sum_congr rfl fun x _ => ?_
        rw [Finset.card_filter]
      have h2 : (∑ x ∈ S, ∑ y ∈ S, if A y x then 1 else 0) = inducedArcs A S := by
        rw [Finset.sum_comm]
        exact h1
      rw [h1, h2, two_mul]
    have hrhs :
        (∑ x ∈ S, ∑ y ∈ S, (if x = y then 0 else 1)) = S.card * (S.card - 1) := by
      have hinner : ∀ x ∈ S, (∑ y ∈ S, if x = y then 0 else 1) = S.card - 1 := by
        intro x hx
        have h : (∑ y ∈ S, if x = y then 0 else 1) = (S.erase x).card := by
          rw [← Finset.sum_erase_add _ _ hx]
          simp only [ite_true, add_zero]
          rw [Finset.card_eq_sum_ones]
          refine Finset.sum_congr rfl fun y hy => ?_
          have hyx : x ≠ y := (mem_erase.mp hy).1.symm
          simp [hyx]
        rw [h, card_erase_of_mem hx]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    rw [hlhs, hrhs] at hsum
    exact hsum
  have h1 : 4 * S.card ≤ S.card * (S.card - 1) := by omega
  have hpos : 0 < S.card := card_pos.mpr hS
  have : S.card ≤ 3 := hcard
  interval_cases h : S.card <;> omega

/-- Every `3`-free subset `S` of size `≤ 5` has a vertex of internal out-degree `≤ 1`
    (in fact holds up to size `6`, proved here cleanly for `|S| ≤ 5`). -/
lemma threeFree_exists_outdeg_le_one_of_card_le_five (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) {S : Finset V} (hS : S.Nonempty) (hcard : S.card ≤ 5) :
    ∃ x ∈ S, (S.filter (fun y => A x y)).card ≤ 1 := by
  by_contra hno
  push Not at hno
  -- Pick a vertex x with minimum internal out-degree (still ≥ 2), look at N⁺_S(x) (size ≥ 2)
  obtain ⟨x, hxS⟩ := hS
  have hdx : 2 ≤ (S.filter (fun y => A x y)).card := hno x hxS
  set Nx := S.filter (fun y => A x y)
  -- Since Nx ⊆ S \ {x} and 3-free, Nx has size ≥ 2; pick two distinct y₁, y₂ ∈ Nx
  obtain ⟨y₁, hy₁⟩ := card_pos.mp (by omega : 0 < Nx.card)
  have hrem : 0 < (Nx.erase y₁).card := by rw [card_erase_of_mem hy₁]; omega
  obtain ⟨y₂, hy₂⟩ := card_pos.mp hrem
  have hy₁S : y₁ ∈ S := (mem_filter.mp hy₁).1
  have hxy₁ : A x y₁ := (mem_filter.mp hy₁).2
  have hy₂_ne : y₂ ≠ y₁ := (mem_erase.mp hy₂).1
  have hy₂_mem : y₂ ∈ Nx := (mem_erase.mp hy₂).2
  have hy₂S : y₂ ∈ S := (mem_filter.mp hy₂_mem).1
  have hxy₂ : A x y₂ := (mem_filter.mp hy₂_mem).2
  -- Actually even cleaner: take a sink w of Nx? Better: Nx has size ≤ 4, consider S \ ({x} ∪ Nx)
  -- Wait: if |Nx| ≥ 3, pick sink of Nx (size 3 => has sink by 3-free? Yes! If |Nx| = 4, Nx = S \ {x} so
  -- every y ∈ Nx has NO out-neighbors outside Nx (cannot hit x!), so y has outdeg ≥ 2 inside Nx,
  -- giving 2*4 = 8 arcs in 4-vertex oriented graph, impossible since 4*3/2 = 6!)
  have hNx_le_3 : Nx.card ≤ 3 := by
    by_contra hge4
    have hNx4 : Nx.card = 4 := by
      have hsub : Nx ⊆ S.erase x := by
        intro y hy
        exact mem_erase.mpr ⟨fun h => h3.1.1 x (h ▸ (mem_filter.mp hy).2), (mem_filter.mp hy).1⟩
      have := (card_le_card hsub).trans (le_of_eq (card_erase_of_mem hxS))
      omega
    -- Every y ∈ Nx cannot point to x (2-free) and S = insert x Nx, so all out-neighbors of y in S lie in Nx!
    have hS_eq : insert x Nx = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hxS
        · exact (mem_filter.mp hw).1
      · rw [card_insert_of_notMem (by simp [Nx, h3.1.1 x]), hNx4]; omega
    have hlow : 8 ≤ inducedArcs A Nx := by
      calc
        8 = ∑ _y ∈ Nx, 2 := by rw [sum_const, hNx4, smul_eq_mul]
        _ ≤ ∑ y ∈ Nx, (Nx.filter (fun z => A y z)).card := by
          refine sum_le_sum fun y hy => ?_
          have hyS : y ∈ S := (mem_filter.mp hy).1
          have heq : S.filter (fun z => A y z) = Nx.filter (fun z => A y z) := by
            ext z
            simp only [mem_filter]
            constructor
            · rintro ⟨hzS, hyz⟩
              have hzx : z ≠ x := fun h => h3.1.2 x y (mem_filter.mp hy).2 (h ▸ hyz)
              rw [← hS_eq] at hzS
              exact ⟨(mem_insert.mp hzS).resolve_left hzx, hyz⟩
            · rintro ⟨hzNx, hyz⟩
              exact ⟨(mem_filter.mp hzNx).1, hyz⟩
          rw [← heq]
          exact hno y hyS
    have hpair : 2 * inducedArcs A Nx ≤ Nx.card * (Nx.card - 1) := by
      have hsum :
          (∑ u ∈ Nx, ∑ w ∈ Nx, ((if A u w then 1 else 0) + (if A w u then 1 else 0))) ≤
            ∑ u ∈ Nx, ∑ w ∈ Nx, (if u = w then 0 else 1) := by
        refine sum_le_sum fun u _ => sum_le_sum fun w _ => ?_
        by_cases huw : u = w
        · subst huw; simp [h3.1.1 u]
        · by_cases h1 : A u w
          · have h2 : ¬ A w u := h3.1.2 u w h1
            simp [huw, h1, h2]
          · by_cases h2 : A w u <;> simp [huw, h1, h2]
      have hlhs :
          (∑ u ∈ Nx, ∑ w ∈ Nx, ((if A u w then 1 else 0) + (if A w u then 1 else 0))) =
            2 * inducedArcs A Nx := by
        simp only [Finset.sum_add_distrib]
        have h1 : (∑ u ∈ Nx, ∑ w ∈ Nx, if A u w then 1 else 0) = inducedArcs A Nx := by
          unfold inducedArcs; refine sum_congr rfl fun u _ => ?_; rw [Finset.card_filter]
        have h2 : (∑ u ∈ Nx, ∑ w ∈ Nx, if A w u then 1 else 0) = inducedArcs A Nx := by
          rw [Finset.sum_comm]; exact h1
        rw [h1, h2, two_mul]
      have hrhs : (∑ u ∈ Nx, ∑ w ∈ Nx, if u = w then 0 else 1) = Nx.card * (Nx.card - 1) := by
        have hi : ∀ u ∈ Nx, (∑ w ∈ Nx, if u = w then 0 else 1) = Nx.card - 1 := by
          intro u hu
          have h : (∑ w ∈ Nx, if u = w then 0 else 1) = (Nx.erase u).card := by
            rw [← Finset.sum_erase_add _ _ hu]; simp only [ite_true, add_zero]
            rw [Finset.card_eq_sum_ones]
            exact Finset.sum_congr rfl fun w hw => by simp [(mem_erase.mp hw).1.symm]
          rw [h, card_erase_of_mem hu]
        rw [Finset.sum_congr rfl hi, sum_const, smul_eq_mul]
      rw [hlhs, hrhs] at hsum; exact hsum
    rw [hNx4] at hpair
    omega
  -- Now |Nx| ≤ 3 and Nx is nonempty, so by exists_sink_threeFree_of_card_le_three Nx has a sink y₀!
  obtain ⟨y₀, hy₀Nx, hy₀sink⟩ := exists_sink_threeFree_of_card_le_three A h3
    (card_pos.mp (by omega)) hNx_le_3
  have hy₀S : y₀ ∈ S := (mem_filter.mp hy₀Nx).1
  have hxy₀ : A x y₀ := (mem_filter.mp hy₀Nx).2
  -- All out-neighbors of y₀ in S lie in R := S \ (insert x Nx), which has size ≤ 5 - 3 = 2!
  set R := S \ insert x Nx
  have hR_sub : S.filter (fun z => A y₀ z) ⊆ R := by
    intro z hz
    rcases mem_filter.mp hz with ⟨hzS, hy₀z⟩
    refine mem_sdiff.mpr ⟨hzS, ?_⟩
    simp only [mem_insert, not_or]
    refine ⟨fun h => h3.1.2 x y₀ hxy₀ (h ▸ hy₀z), fun hzNx => ?_⟩
    have h0 : z ∈ Nx.filter (fun w => A y₀ w) := mem_filter.mpr ⟨hzNx, hy₀z⟩
    rw [Finset.card_eq_zero.mp hy₀sink] at h0
    exact notMem_empty z h0
  have hy₀_ge2 : 2 ≤ (S.filter (fun z => A y₀ z)).card := by have := hno y₀ hy₀S; omega
  have hR_ge2 : 2 ≤ R.card := hy₀_ge2.trans (card_le_card hR_sub)
  have hx_not_Nx : x ∉ Nx := by simp [Nx, h3.1.1 x]
  have hins_sub : insert x Nx ⊆ S := by
    intro w hw; rcases mem_insert.mp hw with rfl | hw; exact hxS; exact (mem_filter.mp hw).1
  have hR_card : R.card = S.card - (Nx.card + 1) := by
    rw [card_sdiff_of_subset hins_sub, card_insert_of_notMem hx_not_Nx]
  -- So |R| = 2, |Nx| = 2, |S| = 5!
  have hR_le2 : R.card ≤ 2 := by omega
  -- By exists_sink_of_card_lt_girth_oriented, R (size 2) has a sink z₀!
  obtain ⟨z₀, hz₀R, hz₀sink⟩ := exists_sink_of_card_lt_girth_oriented A h3.1
    (card_pos.mp (by omega)) hR_le2
  -- Notice y₀ points to ALL of R (since |S.filter (A y₀ ·)| ≥ 2 and subset of R of size 2), so y₀ → z₀!
  have hR_eq : S.filter (fun z => A y₀ z) = R :=
    Finset.eq_of_subset_of_card_le hR_sub (by omega)
  have hy₀z₀ : A y₀ z₀ := (mem_filter.mp (hR_eq.symm ▸ hz₀R)).2
  have hz₀S : z₀ ∈ S := (mem_sdiff.mp hz₀R).1
  -- Where can z₀ send its ≥ 2 out-neighbors in S?
  -- Not into R (sink of R!), not to x (3-free: x → y₀ → z₀ → x!), not to y₀ (2-free: y₀ → z₀)!
  -- So ALL out-neighbors of z₀ in S must lie in Nx.erase y₀, which has size |Nx| - 1 = 1! Contradiction!
  have hz₀_sub : S.filter (fun w => A z₀ w) ⊆ Nx.erase y₀ := by
    intro w hw
    rcases mem_filter.mp hw with ⟨hwS, hz₀w⟩
    have hw_notR : w ∉ R := by
      intro hwR
      have h0 : w ∈ R.filter (fun u => A z₀ u) := mem_filter.mpr ⟨hwR, hz₀w⟩
      rw [Finset.card_eq_zero.mp hz₀sink] at h0
      exact notMem_empty w h0
    have hw_ins : w ∈ insert x Nx := by
      by_contra hnot
      exact hw_notR (mem_sdiff.mpr ⟨hwS, hnot⟩)
    have hwx : w ≠ x := fun h => h3.2 x y₀ z₀ hxy₀ hy₀z₀ (h ▸ hz₀w)
    have hwy₀ : w ≠ y₀ := fun h => h3.1.2 y₀ z₀ hy₀z₀ (h ▸ hz₀w)
    exact mem_erase.mpr ⟨hwy₀, (mem_insert.mp hw_ins).resolve_left hwx⟩
  have hle1 : (S.filter (fun w => A z₀ w)).card ≤ 1 := by
    have := (card_le_card hz₀_sub).trans (le_of_eq (card_erase_of_mem hy₀Nx))
    omega
  have hge2 := hno z₀ hz₀S
  omega

/-- Every `d`-regular oriented graph has `|secondN A v| ≥ d - k` whenever `N⁺(v)` has a vertex of
    internal out-degree `≤ k`. -/
lemma secondN_card_ge_of_internal_outdeg (A : V → V → Prop) [DecidableRel A] {d k : ℕ}
    (hO : IsOriented A) (hR : IsRegular A d) {v a : V} (ha : a ∈ outN A v)
    (hdeg : ((outN A v).filter (fun w => A a w)).card ≤ k) :
    d - k ≤ (secondN A v).card := by
  have hsum := card_outN_inter_H_add_B A hO hR ha
  have hle : ((secondN A v).filter (fun w => A a w)).card ≤ (secondN A v).card :=
    card_le_card (filter_subset _ _)
  omega

/-- In a `d`-regular oriented graph, if `|secondN A v| = d - 1`, then every `a ∈ outN A v`
    has internal out-degree `≥ 1`. -/
lemma deficit_one_internal_outdeg_ge_one (A : V → V → Prop) [DecidableRel A] {d : ℕ}
    (hd : 1 ≤ d) (hO : IsOriented A) (hR : IsRegular A d) {v : V} (hdef : (secondN A v).card = d - 1) :
    ∀ a ∈ outN A v, 1 ≤ ((outN A v).filter (fun w => A a w)).card := by
  intro a ha
  have hsum := card_outN_inter_H_add_B A hO hR ha
  have hle : ((secondN A v).filter (fun w => A a w)).card ≤ (secondN A v).card :=
    card_le_card (filter_subset _ _)
  omega

/-- Extract a directed cycle inside a finite subset `H` with `δ⁺(H) ≥ 1`:
    we obtain a nonempty subset `C ⊆ H` such that every `a ∈ C` has both an in-neighbor
    and an out-neighbor in `C` (a simple cycle of length `≥ 3` if oriented, `≥ 4` if 3-free). -/
lemma exists_cycle_core_oriented (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) {H : Finset V} (hHne : H.Nonempty)
    (hmin : ∀ a ∈ H, 1 ≤ (H.filter (fun w => A a w)).card) :
    ∃ C : Finset V, C ⊆ H ∧ 3 ≤ C.card ∧
      ∀ a ∈ C, (∃ p ∈ C, A p a) ∧ (∃ q ∈ C, A a q) := by
  -- Follow a deterministic successor map f : H → H until first repeat!
  have hf_ex : ∀ a : V, ∃ b : V, a ∈ H → b ∈ H ∧ A a b := by
    intro a
    by_cases ha : a ∈ H
    · obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (H.filter (fun w => A a w)).card by
        have := hmin a ha; omega)
      exact ⟨b, fun _ => mem_filter.mp hb⟩
    · exact ⟨a, fun h => (ha h).elim⟩
  choose f hf using hf_ex
  obtain ⟨x0, hx0⟩ := hHne
  have hmem : ∀ n, f^[n] x0 ∈ H := by
    intro n; induction n with
    | zero => simpa using hx0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hf _ ih).1
  have hstep : ∀ n, A (f^[n] x0) (f^[n + 1] x0) := by
    intro n
    rw [Function.iterate_succ_apply']
    exact (hf _ (hmem n)).2
  -- Pigeonhole on n ∈ {0, ..., |H|} yields i < j with f^[i] x0 = f^[j] x0
  have hnotinj : ¬ Set.InjOn (fun n => f^[n] x0) (Finset.range (H.card + 1) : Set ℕ) := by
    intro hinj
    have hmap_sub : (Finset.range (H.card + 1)).image (fun n => f^[n] x0) ⊆ H := by
      intro y hy
      rcases mem_image.mp hy with ⟨n, _, rfl⟩
      exact hmem n
    have hcard := card_le_card hmap_sub
    rw [card_image_of_injOn hinj, card_range] at hcard
    omega
  simp only [Set.InjOn, mem_coe, mem_range, not_forall] at hnotinj
  obtain ⟨i, hi, j, hj, heq, hne⟩ := hnotinj
  -- Ensure i < j
  wlog hij : i < j generalizing i j
  · exact this j hj i hi heq.symm (Ne.symm hne) (lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hne))
  -- Let C = { f^[t] x0 | t ∈ Ico i j }
  set C : Finset V := (Finset.Ico i j).image (fun t => f^[t] x0)
  have hCsub : C ⊆ H := by
    intro y hy; rcases mem_image.mp hy with ⟨t, _, rfl⟩; exact hmem t
  have hC_step : ∀ a ∈ C, (∃ p ∈ C, A p a) ∧ (∃ q ∈ C, A a q) := by
    intro a ha
    rcases mem_image.mp ha with ⟨t, ht, rfl⟩
    rcases mem_Ico.mp ht with ⟨hit, htj⟩
    constructor
    · by_cases hti : t = i
      · subst hti
        refine ⟨f^[j - 1] x0, mem_image.mpr ⟨j - 1, mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
        have h1 : j - 1 + 1 = j := by omega
        have := hstep (j - 1)
        rwa [h1, ← heq] at this
      · refine ⟨f^[t - 1] x0, mem_image.mpr ⟨t - 1, mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
        have h1 : t - 1 + 1 = t := by omega
        have := hstep (t - 1)
        rwa [h1] at this
    · by_cases ht1 : t + 1 = j
      · refine ⟨f^[i] x0, mem_image.mpr ⟨i, mem_Ico.mpr ⟨le_refl i, hij⟩, rfl⟩, ?_⟩
        have := hstep t
        rwa [ht1, ← heq] at this
      · refine ⟨f^[t + 1] x0, mem_image.mpr ⟨t + 1, mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
        exact hstep t
  have hC_ge3 : 3 ≤ C.card := by
    by_contra hlt
    have hle2 : C.card ≤ 2 := by omega
    have hCne : C.Nonempty := ⟨f^[i] x0, mem_image.mpr ⟨i, mem_Ico.mpr ⟨le_refl i, hij⟩, rfl⟩⟩
    obtain ⟨x, hxC, hxsink⟩ := exists_sink_of_card_lt_girth_oriented A hO hCne hle2
    obtain ⟨q, hqC, hxq⟩ := (hC_step x hxC).2
    have h0 : q ∈ C.filter (fun y => A x y) := mem_filter.mpr ⟨hqC, hxq⟩
    rw [Finset.card_eq_zero.mp hxsink] at h0
    exact notMem_empty q h0
  exact ⟨C, hCsub, hC_ge3, hC_step⟩

/-- Same cycle-core extraction for `3`-free subsets: gives `4 ≤ C.card`. -/
lemma exists_cycle_core_threeFree (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) {H : Finset V} (hHne : H.Nonempty)
    (hmin : ∀ a ∈ H, 1 ≤ (H.filter (fun w => A a w)).card) :
    ∃ C : Finset V, C ⊆ H ∧ 4 ≤ C.card ∧
      ∀ a ∈ C, (∃ p ∈ C, A p a) ∧ (∃ q ∈ C, A a q) := by
  obtain ⟨C, hCsub, hC3, hCstep⟩ := exists_cycle_core_oriented A h3.1 hHne hmin
  have hC4 : 4 ≤ C.card := by
    by_contra hlt
    have hle3 : C.card ≤ 3 := by omega
    have hCne : C.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hxC, hxsink⟩ := exists_sink_threeFree_of_card_le_three A h3 hCne hle3
    obtain ⟨q, hqC, hxq⟩ := (hCstep x hxC).2
    have h0 : q ∈ C.filter (fun y => A x y) := mem_filter.mpr ⟨hqC, hxq⟩
    rw [Finset.card_eq_zero.mp hxsink] at h0
    exact notMem_empty q h0
  exact ⟨C, hCsub, hC4, hCstep⟩

end SmallGraphLemmas

/-! ### Part 4: Elementary Discharging Closures (`d=3` Oriented, `d=4, 5` Three-Free) -/

section DischargingClosures

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 3.1:** Every `3`-regular oriented (`2`-free) graph satisfies `e_2(G) ≥ 3 |V|`. -/
theorem regular_oriented_three_e2 (A : V → V → Prop) [DecidableRel A]
    (hO : IsOriented A) (hR : IsRegular A 3) :
    3 * Fintype.card V ≤ e2 A := by
  have hfloor : ∀ v, 2 ≤ (secondN A v).card := by
    intro v
    have hHne : (outN A v).Nonempty := card_pos.mp (by rw [card_outN_eq hR v]; omega)
    obtain ⟨a, ha, hdeg⟩ := oriented_exists_outdeg_le_one_of_card_le_three A hO hHne
      (le_of_eq (card_outN_eq hR v))
    exact secondN_card_ge_of_internal_outdeg A hO hR ha hdeg
  apply regular_e2_ge_of_surplus_witness A (d := 3) (by omega) hR hfloor
  intro v hdef
  set H := outN A v
  set B := secondN A v
  have hHcard : H.card = 3 := card_outN_eq hR v
  have hBcard : B.card = 2 := hdef
  have hmin : ∀ a ∈ H, 1 ≤ (H.filter (fun w => A a w)).card :=
    deficit_one_internal_outdeg_ge_one A (by omega) hO hR hdef
  -- On 3 vertices, oriented with δ⁺(H) ≥ 1 forces |E(H)| = 3 and d_H⁺(a) = 1 for all a ∈ H!
  have hpair : 2 * inducedArcs A H ≤ H.card * (H.card - 1) := by
    have hsum :
        (∑ u ∈ H, ∑ w ∈ H, ((if A u w then 1 else 0) + (if A w u then 1 else 0))) ≤
          ∑ u ∈ H, ∑ w ∈ H, (if u = w then 0 else 1) := by
      refine sum_le_sum fun u _ => sum_le_sum fun w _ => ?_
      by_cases huw : u = w
      · subst huw; simp [hO.1 u]
      · by_cases h1 : A u w
        · simp [huw, h1, hO.2 u w h1]
        · by_cases h2 : A w u <;> simp [huw, h1, h2]
    have hlhs :
        (∑ u ∈ H, ∑ w ∈ H, ((if A u w then 1 else 0) + (if A w u then 1 else 0))) =
          2 * inducedArcs A H := by
      simp only [Finset.sum_add_distrib]
      have h1 : (∑ u ∈ H, ∑ w ∈ H, if A u w then 1 else 0) = inducedArcs A H := by
        unfold inducedArcs; refine sum_congr rfl fun u _ => ?_; rw [Finset.card_filter]
      have h2 : (∑ u ∈ H, ∑ w ∈ H, if A w u then 1 else 0) = inducedArcs A H := by
        rw [Finset.sum_comm]; exact h1
      rw [h1, h2, two_mul]
    have hrhs : (∑ u ∈ H, ∑ w ∈ H, if u = w then 0 else 1) = H.card * (H.card - 1) := by
      have hi : ∀ u ∈ H, (∑ w ∈ H, if u = w then 0 else 1) = H.card - 1 := by
        intro u hu
        have h : (∑ w ∈ H, if u = w then 0 else 1) = (H.erase u).card := by
          rw [← Finset.sum_erase_add _ _ hu]; simp only [ite_true, add_zero]
          rw [Finset.card_eq_sum_ones]
          exact Finset.sum_congr rfl fun w hw => by simp [(mem_erase.mp hw).1.symm]
        rw [h, card_erase_of_mem hu]
      rw [Finset.sum_congr rfl hi, sum_const, smul_eq_mul]
    rw [hlhs, hrhs] at hsum; exact hsum
  have harcsH : inducedArcs A H ≤ 3 := by rw [hHcard] at hpair; omega
  have hdeg1 : ∀ a ∈ H, (H.filter (fun w => A a w)).card = 1 := by
    intro a ha
    have hrest : 2 ≤ ∑ x ∈ H.erase a, (H.filter (fun w => A x w)).card := by
      calc
        2 = ∑ _x ∈ H.erase a, 1 := by
          rw [sum_const, card_erase_of_mem ha, hHcard, smul_eq_mul, mul_one]
        _ ≤ ∑ x ∈ H.erase a, (H.filter (fun w => A x w)).card :=
          sum_le_sum fun x hx => hmin x (mem_of_mem_erase hx)
    have hsplit : (H.filter (fun w => A a w)).card +
        ∑ x ∈ H.erase a, (H.filter (fun w => A x w)).card = inducedArcs A H :=
      Finset.add_sum_erase H (fun x => (H.filter (fun w => A x w)).card) ha
    have h1 := hmin a ha
    omega
  -- Hence every a ∈ H points to ALL of B!
  have hHB_all : ∀ a ∈ H, ∀ b ∈ B, A a b := by
    intro a ha b hb
    have hsum : (H.filter (fun w => A a w)).card + (B.filter (fun w => A a w)).card = 3 :=
      card_outN_inter_H_add_B A hO hR ha
    rw [hdeg1 a ha] at hsum
    have heq : B.filter (fun w => A a w) = B :=
      Finset.eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact (mem_filter.mp (heq.symm ▸ hb)).2
  -- Arc-drop gives |E(B)| = 0!
  have harcsB : inducedArcs A B = 0 := by
    have hdrop := arc_drop_identity A hO hR v
    change inducedArcs A B + 3 * 3 ≤ inducedArcs A H + 3 * B.card at hdrop
    omega
  -- Cycle core C ⊆ H has size 3, so C = H
  obtain ⟨C, hCsub, hC3, hCstep⟩ := exists_cycle_core_oriented A hO
    (card_pos.mp (by omega)) hmin
  -- Every a ∈ C has |secondN A a| ≥ 4!
  have hsurp : ∀ a ∈ C, 4 ≤ (secondN A a).card := by
    intro a haC
    have haH : a ∈ H := hCsub haC
    obtain ⟨q, hqC, haq⟩ := (hCstep a haC).2
    obtain ⟨r, hrC, hqr⟩ := (hCstep q hqC).2
    have hqH : q ∈ H := hCsub hqC
    have hrH : r ∈ H := hCsub hrC
    have hra_ne : r ≠ a := fun h => hO.2 a q haq (h ▸ hqr)
    have hnot_ar : ¬ A a r := by
      intro har
      have hsub : ({q, r} : Finset V) ⊆ H.filter (fun w => A a w) := by
        intro w hw; simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_filter.mpr ⟨hqH, haq⟩
        · exact mem_filter.mpr ⟨hrH, har⟩
      have hqr_ne : q ≠ r := fun h => hO.1 q (h ▸ hqr)
      have h2 : ({q, r} : Finset V).card = 2 := by rw [card_pair hqr_ne]
      have := card_le_card hsub
      rw [h2, hdeg1 a haH] at this; omega
    -- Pick any b0 ∈ B; outN A b0 (size 3) is disjoint from H ∪ B, hence ⊆ secondN A a, and r ∉ outN A b0!
    obtain ⟨b0, hb0B⟩ := card_pos.mp (by omega : 0 < B.card)
    have hsub : insert r (outN A b0) ⊆ secondN A a := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hwb0
      · exact mem_secondN.mpr ⟨hra_ne, hnot_ar, ⟨q, haq, hqr⟩⟩
      · rw [mem_outN] at hwb0
        have hw_notH : w ∉ H := fun hwH => hO.2 w b0 (hHB_all w hwH b0 hb0B) hwb0
        have hw_notB : w ∉ B := by
          intro hwB
          have hpos : 0 < (B.filter (fun u => A b0 u)).card :=
            card_pos.mpr ⟨w, mem_filter.mpr ⟨hwB, hwb0⟩⟩
          have hle : (B.filter (fun u => A b0 u)).card ≤ inducedArcs A B :=
            Finset.single_le_sum (f := fun x => (B.filter (fun u => A x u)).card)
              (fun _ _ => Nat.zero_le _) hb0B
          omega
        have hwa : w ≠ a := fun h => hw_notH (h ▸ haH)
        have hnot_aw : ¬ A a w := fun haw => by
          rcases mem_union.mp (outN_subset_outN_union_secondN A hO haH (mem_outN.mpr haw)) with
            h1 | h2
          · exact hw_notH h1
          · exact hw_notB h2
        exact mem_secondN.mpr ⟨hwa, hnot_aw, ⟨b0, hHB_all a haH b0 hb0B, hwb0⟩⟩
    have hr_not_b0 : r ∉ outN A b0 := fun hr => hO.2 r b0 (hHB_all r hrH b0 hb0B) (mem_outN.mp hr)
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hr_not_b0, card_outN_eq hR b0] at hcard
    exact hcard
  refine ⟨C, hCsub, by omega, fun a haC => ⟨hsurp a haC, ?_⟩⟩
  obtain ⟨p, hpC, hpa⟩ := (hCstep a haC).1
  exact ⟨p, hpa, by have := hsurp p hpC; omega⟩

/-- **Theorem 3.2:** Every `4`-regular `3`-free digraph satisfies `e_2(G) ≥ 4 |V|`. -/
theorem regular_threeFree_four_e2 (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) (hR : IsRegular A 4) :
    4 * Fintype.card V ≤ e2 A := by
  have hfloor : ∀ v, 3 ≤ (secondN A v).card := by
    intro v
    have hHne : (outN A v).Nonempty := card_pos.mp (by rw [card_outN_eq hR v]; omega)
    obtain ⟨a, ha, hdeg⟩ := threeFree_exists_outdeg_le_one_of_card_le_five A h3 hHne
      (by rw [card_outN_eq hR v]; omega)
    exact secondN_card_ge_of_internal_outdeg A h3.1 hR ha hdeg
  apply regular_e2_ge_of_surplus_witness A (d := 4) (by omega) hR hfloor
  intro v hdef
  set H := outN A v
  set B := secondN A v
  have hHcard : H.card = 4 := card_outN_eq hR v
  have hBcard : B.card = 3 := hdef
  have hmin : ∀ a ∈ H, 1 ≤ (H.filter (fun w => A a w)).card :=
    deficit_one_internal_outdeg_ge_one A (by omega) h3.1 hR hdef
  obtain ⟨C, hCsub, hC4, hCstep⟩ := exists_cycle_core_threeFree A h3
    (card_pos.mp (by omega)) hmin
  have hCeq : C = H := Finset.eq_of_subset_of_card_le hCsub (by omega)
  -- Every vertex x ∈ H = C has a 2-path q → p → x in C (with q ≠ x since 2-free!),
  -- so x cannot point to x, p (2-free), or q (3-free) => d_H⁺(x) ≤ 4 - 3 = 1!
  have hdeg1 : ∀ x ∈ H, (H.filter (fun w => A x w)).card = 1 := by
    intro x hxH
    have hxC : x ∈ C := hCeq.symm ▸ hxH
    obtain ⟨p, hpC, hpx⟩ := (hCstep x hxC).1
    obtain ⟨q, hqC, hqp⟩ := (hCstep p hpC).1
    have hpH : p ∈ H := hCsub hpC
    have hqH : q ∈ H := hCsub hqC
    have hxp : x ≠ p := fun h => h3.1.1 p (h ▸ hpx)
    have hpq : p ≠ q := fun h => h3.1.1 q (h ▸ hqp)
    have hxq : x ≠ q := fun h => h3.1.2 p x hpx (h ▸ hqp)
    have hsub : H.filter (fun w => A x w) ⊆ H \ ({x, p, q} : Finset V) := by
      intro w hw
      rcases mem_filter.mp hw with ⟨hwH, hxw⟩
      refine mem_sdiff.mpr ⟨hwH, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨fun h => h3.1.1 x (h ▸ hxw), fun h => h3.1.2 p x hpx (h ▸ hxw),
        fun h => h3.2 q p x hqp hpx (h ▸ hxw)⟩
    have h3sub : ({x, p, q} : Finset V) ⊆ H := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have h3card : ({x, p, q} : Finset V).card = 3 := by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [hpq]
      · simp [hxp, hxq]
    have hle1 : (H.filter (fun w => A x w)).card ≤ 1 := by
      have := card_le_card hsub
      rw [card_sdiff_of_subset h3sub, hHcard, h3card] at this
      exact this
    have hge1 := hmin x hxH
    omega
  have harcsH : inducedArcs A H = 4 := by
    unfold inducedArcs
    rw [Finset.sum_congr rfl fun x hx => hdeg1 x hx, sum_const, hHcard, smul_eq_mul, mul_one]
  have harcsB : inducedArcs A B = 0 := by
    have hdrop := arc_drop_identity A h3.1 hR v
    change inducedArcs A B + 4 * 4 ≤ inducedArcs A H + 4 * B.card at hdrop
    omega
  have hHB_all : ∀ a ∈ H, ∀ b ∈ B, A a b := by
    intro a ha b hb
    have hsum : (H.filter (fun w => A a w)).card + (B.filter (fun w => A a w)).card = 4 :=
      card_outN_inter_H_add_B A h3.1 hR ha
    rw [hdeg1 a ha] at hsum
    have heq : B.filter (fun w => A a w) = B :=
      Finset.eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact (mem_filter.mp (heq.symm ▸ hb)).2
  have hsurp : ∀ a ∈ C, 5 ≤ (secondN A a).card := by
    intro a haC
    have haH : a ∈ H := hCsub haC
    obtain ⟨q, hqC, haq⟩ := (hCstep a haC).2
    obtain ⟨r, hrC, hqr⟩ := (hCstep q hqC).2
    have hqH : q ∈ H := hCsub hqC
    have hrH : r ∈ H := hCsub hrC
    have hra_ne : r ≠ a := fun h => h3.1.2 a q haq (h ▸ hqr)
    have hnot_ar : ¬ A a r := by
      intro har
      have hqr_ne : q ≠ r := fun h => h3.1.1 q (h ▸ hqr)
      have hsub : ({q, r} : Finset V) ⊆ H.filter (fun w => A a w) := by
        intro w hw; simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_filter.mpr ⟨hqH, haq⟩
        · exact mem_filter.mpr ⟨hrH, har⟩
      have := card_le_card hsub
      rw [card_pair hqr_ne, hdeg1 a haH] at this; omega
    obtain ⟨b0, hb0B⟩ := card_pos.mp (by omega : 0 < B.card)
    have hsub : insert r (outN A b0) ⊆ secondN A a := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hwb0
      · exact mem_secondN.mpr ⟨hra_ne, hnot_ar, ⟨q, haq, hqr⟩⟩
      · rw [mem_outN] at hwb0
        have hw_notH : w ∉ H := fun hwH => h3.1.2 w b0 (hHB_all w hwH b0 hb0B) hwb0
        have hw_notB : w ∉ B := by
          intro hwB
          have hpos : 0 < (B.filter (fun u => A b0 u)).card :=
            card_pos.mpr ⟨w, mem_filter.mpr ⟨hwB, hwb0⟩⟩
          have hle : (B.filter (fun u => A b0 u)).card ≤ inducedArcs A B :=
            Finset.single_le_sum (f := fun x => (B.filter (fun u => A x u)).card)
              (fun _ _ => Nat.zero_le _) hb0B
          omega
        have hwa : w ≠ a := fun h => hw_notH (h ▸ haH)
        have hnot_aw : ¬ A a w := fun haw => by
          rcases mem_union.mp (outN_subset_outN_union_secondN A h3.1 haH (mem_outN.mpr haw)) with
            h1 | h2
          · exact hw_notH h1
          · exact hw_notB h2
        exact mem_secondN.mpr ⟨hwa, hnot_aw, ⟨b0, hHB_all a haH b0 hb0B, hwb0⟩⟩
    have hr_not_b0 : r ∉ outN A b0 :=
      fun hr => h3.1.2 r b0 (hHB_all r hrH b0 hb0B) (mem_outN.mp hr)
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hr_not_b0, card_outN_eq hR b0] at hcard
    exact hcard
  refine ⟨C, hCsub, by omega, fun a haC => ⟨hsurp a haC, ?_⟩⟩
  obtain ⟨p, hpC, hpa⟩ := (hCstep a haC).1
  exact ⟨p, hpa, by have := hsurp p hpC; omega⟩

/-- **Corollary 3.2 (Regular `d = 4` CH, all residues including `n = 12`):**
    Every nonempty `4`-regular `3`-free digraph has at least `13` vertices. -/
theorem regular_threeFree_four_order_ge_13 (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) (hR : IsRegular A 4) (hne : Nonempty V) :
    13 ≤ Fintype.card V :=
  regular_threeFree_order_ge_of_e2 A h3 hR hne (regular_threeFree_four_e2 A h3 hR)

/-- **Structural Lemma for `5`-vertex `3`-free digraphs with `δ⁺(H) ≥ 1`:**
    At most `2` vertices of `H` have internal out-degree `≥ 2`. -/
lemma threeFree_card_five_at_most_two_high (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) {H : Finset V} (hHcard : H.card = 5)
    (hmin : ∀ a ∈ H, 1 ≤ (H.filter (fun w => A a w)).card) :
    (H.filter (fun a => 2 ≤ (H.filter (fun w => A a w)).card)).card ≤ 2 := by
  by_contra hgt
  set High := H.filter (fun a => 2 ≤ (H.filter (fun w => A a w)).card)
  have hge3 : 3 ≤ High.card := by omega
  -- Extract a 3-element subset T ⊆ High
  obtain ⟨u1, hu1⟩ := card_pos.mp (by omega : 0 < High.card)
  obtain ⟨u2, hu2⟩ := card_pos.mp (by rw [card_erase_of_mem hu1]; omega : 0 < (High.erase u1).card)
  obtain ⟨u3, hu3⟩ := card_pos.mp (by
    rw [card_erase_of_mem hu2, card_erase_of_mem hu1]; omega : 0 < ((High.erase u1).erase u2).card)
  have hu2_ne1 : u2 ≠ u1 := (mem_erase.mp hu2).1
  have hu2H : u2 ∈ High := (mem_erase.mp hu2).2
  have hu3_ne2 : u3 ≠ u2 := (mem_erase.mp hu3).1
  have hu3_ne1 : u3 ≠ u1 := (mem_erase.mp (mem_erase.mp hu3).2).1
  have hu3H : u3 ∈ High := (mem_erase.mp (mem_erase.mp hu3).2).2
  set T : Finset V := {u1, u2, u3}
  have hT_sub : T ⊆ High := by
    intro w hw; simp only [T, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hT_subH : T ⊆ H := hT_sub.trans (filter_subset _ _)
  have hT_card : T.card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hu3_ne2.symm]
    · simp [hu2_ne1.symm, hu3_ne1.symm]
  -- R := H \ T has size 2
  set R : Finset V := H \ T
  have hR_card : R.card = 2 := by rw [card_sdiff_of_subset hT_subH, hHcard, hT_card]
  -- Pick a sink w of T (size 3, 3-free => has a sink!)
  obtain ⟨w, hwT, hwsink⟩ := exists_sink_threeFree_of_card_le_three A h3 (S := T)
    (card_pos.mp (by omega)) (by omega)
  have hwH : w ∈ H := hT_subH hwT
  have hwHigh : 2 ≤ (H.filter (fun z => A w z)).card := (mem_filter.mp (hT_sub hwT)).2
  -- All out-neighbors of w in H lie in R (size 2), so w → s for ALL s ∈ R!
  have hw_allR : ∀ s ∈ R, A w s := by
    have hsub : H.filter (fun z => A w z) ⊆ R := by
      intro z hz
      rcases mem_filter.mp hz with ⟨hzH, hwz⟩
      refine mem_sdiff.mpr ⟨hzH, fun hzT => ?_⟩
      have h0 : z ∈ T.filter (fun u => A w u) := mem_filter.mpr ⟨hzT, hwz⟩
      rw [Finset.card_eq_zero.mp hwsink] at h0
      exact notMem_empty z h0
    have heq : H.filter (fun z => A w z) = R :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    intro s hs
    exact (mem_filter.mp (heq.symm ▸ hs)).2
  -- Pick a sink v of T \ {w} (size 2, oriented => has a sink!), and let u be the unique remaining vertex of T!
  set T2 := T.erase w
  have hT2_card : T2.card = 2 := by rw [card_erase_of_mem hwT, hT_card]
  obtain ⟨v, hvT2, hvsink⟩ := exists_sink_of_card_lt_girth_oriented A h3.1 (S := T2)
    (card_pos.mp (by omega)) (by omega)
  have hvw : v ≠ w := (mem_erase.mp hvT2).1
  have hvT : v ∈ T := (mem_erase.mp hvT2).2
  have hvH : v ∈ H := hT_subH hvT
  have hvHigh : 2 ≤ (H.filter (fun z => A v z)).card := (mem_filter.mp (hT_sub hvT)).2
  have hu_card : (T2.erase v).card = 1 := by rw [card_erase_of_mem hvT2, hT2_card]
  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hu_card
  have hu_mem : u ∈ T2.erase v := hu_eq.symm ▸ mem_singleton_self u
  have huv : u ≠ v := (mem_erase.mp hu_mem).1
  have huT2 : u ∈ T2 := (mem_erase.mp hu_mem).2
  have huw : u ≠ w := (mem_erase.mp huT2).1
  have huT : u ∈ T := (mem_erase.mp huT2).2
  have huH : u ∈ H := hT_subH huT
  have huHigh : 2 ≤ (H.filter (fun z => A u z)).card := (mem_filter.mp (hT_sub huT)).2
  have hT_eq : T = {w, v, u} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_cases hxw : x = w
      · simp [hxw]
      · have hxT2 : x ∈ T2 := mem_erase.mpr ⟨hxw, hx⟩
        by_cases hxv : x = v
        · simp [hxv]
        · have hxu : x = u := mem_singleton.mp (hu_eq ▸ mem_erase.mpr ⟨hxv, hxT2⟩)
          simp [hxu]
    · rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton, hT_card]
      · simp [huv.symm]
      · simp [hvw.symm, huw.symm]
  -- Pick a sink s1 of R (size 2), and let s2 be the other vertex of R!
  obtain ⟨s1, hs1R, hs1sink⟩ := exists_sink_of_card_lt_girth_oriented A h3.1 (S := R)
    (card_pos.mp (by omega)) (by omega)
  have hs2_card : (R.erase s1).card = 1 := by rw [card_erase_of_mem hs1R, hR_card]
  obtain ⟨s2, hs2_eq⟩ := Finset.card_eq_one.mp hs2_card
  have hs2_mem : s2 ∈ R.erase s1 := hs2_eq.symm ▸ mem_singleton_self s2
  have hs2_ne1 : s2 ≠ s1 := (mem_erase.mp hs2_mem).1
  have hs2R : s2 ∈ R := (mem_erase.mp hs2_mem).2
  have hR_eq : R = {s1, s2} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_cases h1 : x = s1
      · simp [h1]
      · have h2 : x = s2 := mem_singleton.mp (hs2_eq ▸ mem_erase.mpr ⟨h1, hx⟩)
        simp [h2]
    · rw [card_pair hs2_ne1.symm, hR_card]
  have hs1H : s1 ∈ H := (mem_sdiff.mp hs1R).1
  have hs2H : s2 ∈ H := (mem_sdiff.mp hs2R).1
  have hws1 : A w s1 := hw_allR s1 hs1R
  have hws2 : A w s2 := hw_allR s2 hs2R
  have hH_eq : H = {w, v, u, s1, s2} := by
    have hun : T ∪ R = H := Finset.union_sdiff_of_subset hT_subH
    rw [← hun, hT_eq, hR_eq]
    ext x; simp; tauto
  -- Helper: v cannot point to u (since v is a sink of T2 = {v, u})!
  have hnot_vu : ¬ A v u := by
    intro hvu
    have h0 : u ∈ T2.filter (fun z => A v z) := mem_filter.mpr ⟨huT2, hvu⟩
    rw [Finset.card_eq_zero.mp hvsink] at h0
    exact notMem_empty u h0
  -- Helper: s1 cannot point to s2 (since s1 is a sink of R = {s1, s2})!
  have hnot_s1s2 : ¬ A s1 s2 := by
    intro hs1s2
    have h0 : s2 ∈ R.filter (fun z => A s1 z) := mem_filter.mpr ⟨hs2R, hs1s2⟩
    rw [Finset.card_eq_zero.mp hs1sink] at h0
    exact notMem_empty s2 h0
  -- Case split on whether v → w!
  by_cases hvw_arc : A v w
  · -- Case 1: v → w. Since w → s1 and w → s2, 3-free forbids s1 → v and s2 → v.
    -- Also 2-free forbids s1 → w and s2 → w, and s1 is a sink of R, so s1 MUST point to u!
    have hs1u : A s1 u := by
      obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (H.filter (fun z => A s1 z)).card by
        have := hmin s1 hs1H; omega)
      rcases mem_filter.mp hz with ⟨hzH, hs1z⟩
      rw [hH_eq] at hzH
      simp only [mem_insert, mem_singleton] at hzH
      rcases hzH with h | h | h | h | h
      · rw [h] at hs1z; exact (h3.1.2 w s1 hws1 hs1z).elim
      · rw [h] at hs1z; exact (h3.2 v w s1 hvw_arc hws1 hs1z).elim
      · rw [h] at hs1z; exact hs1z
      · rw [h] at hs1z; exact (h3.1.1 s1 hs1z).elim
      · rw [h] at hs1z; exact (hnot_s1s2 hs1z).elim
    -- Since w → s1 → u, 3-free forbids u → w! Also 2-free forbids u → s1!
    -- Since d_H⁺(u) ≥ 2 and H = {w, v, u, s1, s2}, u MUST point to BOTH v and s2!
    have hu_sub : H.filter (fun z => A u z) ⊆ {v, s2} := by
      intro z hz
      rcases mem_filter.mp hz with ⟨hzH, huz⟩
      rw [hH_eq] at hzH
      simp only [mem_insert, mem_singleton] at hzH ⊢
      rcases hzH with h | h | h | h | h
      · rw [h] at huz; exact (h3.2 w s1 u hws1 hs1u huz).elim
      · exact Or.inl h
      · rw [h] at huz; exact (h3.1.1 u huz).elim
      · rw [h] at huz; exact (h3.1.2 s1 u hs1u huz).elim
      · exact Or.inr h
    have hus2_ne : v ≠ s2 := fun h => (mem_sdiff.mp hs2R).2 (h ▸ hvT)
    have hu_eq2 : H.filter (fun z => A u z) = {v, s2} :=
      Finset.eq_of_subset_of_card_le hu_sub (by rw [card_pair hus2_ne]; omega)
    have hus2 : A u s2 := (mem_filter.mp (hu_eq2.symm ▸ (by simp : s2 ∈ ({v, s2} : Finset V)))).2
    -- Now where can s2 point? Not w (2-free), not v (3-free: v→w→s2→v), not u (2-free: u→s2),
    -- not s2 (loopless), not s1 (3-free: u→s2→s1→u)! Contradiction to δ⁺(H) ≥ 1!
    obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (H.filter (fun z => A s2 z)).card by
      have := hmin s2 hs2H; omega)
    rcases mem_filter.mp hz with ⟨hzH, hs2z⟩
    rw [hH_eq] at hzH
    simp only [mem_insert, mem_singleton] at hzH
    rcases hzH with h | h | h | h | h
    · rw [h] at hs2z; exact h3.1.2 w s2 hws2 hs2z
    · rw [h] at hs2z; exact h3.2 v w s2 hvw_arc hws2 hs2z
    · rw [h] at hs2z; exact h3.1.2 u s2 hus2 hs2z
    · rw [h] at hs2z; exact h3.2 u s2 s1 hus2 hs2z hs1u
    · rw [h] at hs2z; exact h3.1.1 s2 hs2z
  · -- Case 2: ¬ A v w. Since ¬ A v u and v ∉ {s1, s2}, ALL out-neighbors of v in H lie in R = {s1, s2}!
    have hv_sub : H.filter (fun z => A v z) ⊆ {s1, s2} := by
      intro z hz
      rcases mem_filter.mp hz with ⟨hzH, hvz⟩
      rw [hH_eq] at hzH
      simp only [mem_insert, mem_singleton] at hzH ⊢
      rcases hzH with h | h | h | h | h
      · rw [h] at hvz; exact (hvw_arc hvz).elim
      · rw [h] at hvz; exact (h3.1.1 v hvz).elim
      · rw [h] at hvz; exact (hnot_vu hvz).elim
      · exact Or.inl h
      · exact Or.inr h
    have hv_eq2 : H.filter (fun z => A v z) = {s1, s2} :=
      Finset.eq_of_subset_of_card_le hv_sub (by rw [card_pair hs2_ne1.symm]; omega)
    have hvs1 : A v s1 := (mem_filter.mp (hv_eq2.symm ▸ (by simp : s1 ∈ ({s1, s2} : Finset V)))).2
    -- Where can s1 point? Not w (2-free), not v (2-free), not s1 (loopless), not s2 (sink of R) => s1 → u!
    have hs1u : A s1 u := by
      obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (H.filter (fun z => A s1 z)).card by
        have := hmin s1 hs1H; omega)
      rcases mem_filter.mp hz with ⟨hzH, hs1z⟩
      rw [hH_eq] at hzH
      simp only [mem_insert, mem_singleton] at hzH
      rcases hzH with h | h | h | h | h
      · rw [h] at hs1z; exact (h3.1.2 w s1 hws1 hs1z).elim
      · rw [h] at hs1z; exact (h3.1.2 v s1 hvs1 hs1z).elim
      · rw [h] at hs1z; exact hs1z
      · rw [h] at hs1z; exact (h3.1.1 s1 hs1z).elim
      · rw [h] at hs1z; exact (hnot_s1s2 hs1z).elim
    -- Now u cannot point to w (3-free: w→s1→u→w), v (3-free: v→s1→u→v), u (loopless), s1 (2-free)!
    -- So u has at most 1 out-neighbor in H (only s2), contradicting d_H⁺(u) ≥ 2!
    have hu_sub : H.filter (fun z => A u z) ⊆ {s2} := by
      intro z hz
      rcases mem_filter.mp hz with ⟨hzH, huz⟩
      rw [hH_eq] at hzH
      simp only [mem_insert, mem_singleton] at hzH ⊢
      rcases hzH with h | h | h | h | h
      · rw [h] at huz; exact (h3.2 w s1 u hws1 hs1u huz).elim
      · rw [h] at huz; exact (h3.2 v s1 u hvs1 hs1u huz).elim
      · rw [h] at huz; exact (h3.1.1 u huz).elim
      · rw [h] at huz; exact (h3.1.2 s1 u hs1u huz).elim
      · exact h
    have hle1 : (H.filter (fun z => A u z)).card ≤ 1 := by
      have := card_le_card hu_sub; rwa [card_singleton] at this
    omega

/-- **Theorem 3.3:** Every `5`-regular `3`-free digraph satisfies `e_2(G) ≥ 5 |V|`. -/
theorem regular_threeFree_five_e2 (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) (hR : IsRegular A 5) :
    5 * Fintype.card V ≤ e2 A := by
  have hfloor : ∀ v, 4 ≤ (secondN A v).card := by
    intro v
    have hHne : (outN A v).Nonempty := card_pos.mp (by rw [card_outN_eq hR v]; omega)
    obtain ⟨a, ha, hdeg⟩ := threeFree_exists_outdeg_le_one_of_card_le_five A h3 hHne
      (le_of_eq (card_outN_eq hR v))
    exact secondN_card_ge_of_internal_outdeg A h3.1 hR ha hdeg
  apply regular_e2_ge_of_surplus_witness A (d := 5) (by omega) hR hfloor
  intro v hdef
  set H := outN A v
  set B := secondN A v
  have hHcard : H.card = 5 := card_outN_eq hR v
  have hBcard : B.card = 4 := hdef
  have hmin : ∀ a ∈ H, 1 ≤ (H.filter (fun w => A a w)).card :=
    deficit_one_internal_outdeg_ge_one A (by omega) h3.1 hR hdef
  -- Cycle core C ⊆ H has size ≥ 4
  obtain ⟨C, hCsub, hC4, hCstep⟩ := exists_cycle_core_threeFree A h3
    (card_pos.mp (by omega)) hmin
  -- Partition H into S (internal outdeg = 1) and High (internal outdeg ≥ 2)
  set High := H.filter (fun x => 2 ≤ (H.filter (fun w => A x w)).card)
  set S := H.filter (fun x => (H.filter (fun w => A x w)).card = 1)
  have hHigh_le2 : High.card ≤ 2 := threeFree_card_five_at_most_two_high A h3 hHcard hmin
  -- Every x ∈ S sends ALL 4 remaining arcs to B!
  have hS_allB : ∀ s ∈ S, ∀ b ∈ B, A s b := by
    intro s hs b hb
    rcases mem_filter.mp hs with ⟨hsH, hs1⟩
    have hsum : (H.filter (fun w => A s w)).card + (B.filter (fun w => A s w)).card = 5 :=
      card_outN_inter_H_add_B A h3.1 hR hsH
    rw [hs1] at hsum
    have heq : B.filter (fun w => A s w) = B :=
      Finset.eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact (mem_filter.mp (heq.symm ▸ hb)).2
  -- Every x ∈ High has an out-neighbor s ∈ S (since d_H⁺(x) ≥ 2 and |High \ {x}| ≤ 1)!
  have hHigh_hits_S : ∀ x ∈ High, ∃ s ∈ S, A x s := by
    intro x hx
    have hxH : x ∈ H := (mem_filter.mp hx).1
    have hdx : 2 ≤ (H.filter (fun w => A x w)).card := (mem_filter.mp hx).2
    by_contra hno
    push Not at hno
    have hsub : H.filter (fun w => A x w) ⊆ High.erase x := by
      intro w hw
      rcases mem_filter.mp hw with ⟨hwH, hxw⟩
      have hwx : w ≠ x := fun h => h3.1.1 x (h ▸ hxw)
      refine mem_erase.mpr ⟨hwx, mem_filter.mpr ⟨hwH, ?_⟩⟩
      have h1 := hmin w hwH
      have hne1 : (H.filter (fun z => A w z)).card ≠ 1 := fun h =>
        hno w (mem_filter.mpr ⟨hwH, h⟩) hxw
      omega
    have hle1 : (H.filter (fun w => A x w)).card ≤ 1 := by
      have := (card_le_card hsub).trans (le_of_eq (card_erase_of_mem hx))
      omega
    omega
  -- Consequently, NO arc goes from B to H!
  have hno_BH : ∀ b ∈ B, ∀ x ∈ H, ¬ A b x := by
    intro b hb x hxH hbx
    by_cases hx1 : (H.filter (fun w => A x w)).card = 1
    · exact h3.1.2 x b (hS_allB x (mem_filter.mpr ⟨hxH, hx1⟩) b hb) hbx
    · have hxHigh : x ∈ High := mem_filter.mpr ⟨hxH, by have := hmin x hxH; omega⟩
      obtain ⟨s, hsS, hxs⟩ := hHigh_hits_S x hxHigh
      exact h3.2 x s b hxs (hS_allB s hsS b hb) hbx
  -- Every x ∈ C has internal out-degree ≤ 2 (since q → p → x in C forbids x → x, p, q)
  have hC_deg_le2 : ∀ x ∈ C, (H.filter (fun w => A x w)).card ≤ 2 := by
    intro x hxC
    have hxH : x ∈ H := hCsub hxC
    obtain ⟨p, hpC, hpx⟩ := (hCstep x hxC).1
    obtain ⟨q, hqC, hqp⟩ := (hCstep p hpC).1
    have hpH : p ∈ H := hCsub hpC
    have hqH : q ∈ H := hCsub hqC
    have hxp : x ≠ p := fun h => h3.1.1 p (h ▸ hpx)
    have hpq : p ≠ q := fun h => h3.1.1 q (h ▸ hqp)
    have hxq : x ≠ q := fun h => h3.1.2 p x hpx (h ▸ hqp)
    have hsub : H.filter (fun w => A x w) ⊆ H \ ({x, p, q} : Finset V) := by
      intro w hw
      rcases mem_filter.mp hw with ⟨hwH, hxw⟩
      refine mem_sdiff.mpr ⟨hwH, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => h3.1.1 x (h ▸ hxw), fun h => h3.1.2 p x hpx (h ▸ hxw),
        fun h => h3.2 q p x hqp hpx (h ▸ hxw)⟩
    have h3sub : ({x, p, q} : Finset V) ⊆ H := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have h3card : ({x, p, q} : Finset V).card = 3 := by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [hpq]
      · simp [hxp, hxq]
    have := card_le_card hsub
    rw [card_sdiff_of_subset h3sub, hHcard, h3card] at this
    exact this
  -- Bound on |E(H)|:
  -- (a) Always |E(H)| ≤ 8;
  -- (b) If any a ∈ C belongs to High (d_H⁺(a) = 2), then |E(H)| ≤ 7!
  have hS_union_High : S ∪ High = H := by
    ext x
    simp only [S, High, mem_union, mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases h1 : (H.filter (fun w => A x w)).card = 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, by have := hmin x hx; omega⟩
  have hS_disj_High : Disjoint S High := by
    rw [disjoint_left]
    intro x hxS hxH
    have h1 := (mem_filter.mp hxS).2
    have h2 := (mem_filter.mp hxH).2
    omega
  have harcsH_split :
      inducedArcs A H = S.card + ∑ x ∈ High, (H.filter (fun w => A x w)).card := by
    unfold inducedArcs
    have hsplit : (∑ x ∈ H, (H.filter (fun w => A x w)).card) =
        (∑ x ∈ S, (H.filter (fun w => A x w)).card) +
        (∑ x ∈ High, (H.filter (fun w => A x w)).card) := by
      calc
        (∑ x ∈ H, (H.filter (fun w => A x w)).card)
            = ∑ x ∈ S ∪ High, (H.filter (fun w => A x w)).card :=
              Finset.sum_congr hS_union_High.symm fun _ _ => rfl
        _ = (∑ x ∈ S, (H.filter (fun w => A x w)).card) +
            (∑ x ∈ High, (H.filter (fun w => A x w)).card) := sum_union hS_disj_High
    rw [hsplit]
    congr 1
    have hS1 : (∑ x ∈ S, (H.filter (fun w => A x w)).card) = ∑ _x ∈ S, 1 :=
      Finset.sum_congr rfl fun x hx => (mem_filter.mp hx).2
    rw [hS1, sum_const, smul_eq_mul, mul_one]
  have hS_add_High : S.card + High.card = 5 := by
    have := congr_arg Finset.card hS_union_High
    rw [card_union_of_disjoint hS_disj_High, hHcard] at this
    exact this
  -- Helper: if a ∈ C ∩ High, then every y ∈ High has d_H⁺(y) ≤ 2!
  have hHigh_deg_le2_of_C : ∀ a ∈ C, a ∈ High → ∀ y ∈ High, (H.filter (fun w => A y w)).card ≤ 2 := by
    intro a haC haHigh y hyHigh
    by_cases hyC : y ∈ C
    · exact hC_deg_le2 y hyC
    · -- Then |C| = 4 and H = insert y C!
      have hCeq4 : C.card = 4 := by
        have hsub : C ⊆ H.erase y := by
          intro w hw
          exact mem_erase.mpr ⟨fun h => hyC (h ▸ hw), hCsub hw⟩
        have := (card_le_card hsub).trans (le_of_eq (card_erase_of_mem (mem_filter.mp hyHigh).1))
        omega
      -- Every vertex of C has internal outdeg ≤ 1 inside C (exact same 3-free 4-cycle argument!)
      have ha_Cdeg1 : (C.filter (fun w => A a w)).card ≤ 1 := by
        obtain ⟨p, hpC, hpa⟩ := (hCstep a haC).1
        obtain ⟨q, hqC, hqp⟩ := (hCstep p hpC).1
        have hap : a ≠ p := fun h => h3.1.1 p (h ▸ hpa)
        have hpq : p ≠ q := fun h => h3.1.1 q (h ▸ hqp)
        have haq : a ≠ q := fun h => h3.1.2 p a hpa (h ▸ hqp)
        have hsub : C.filter (fun w => A a w) ⊆ C \ ({a, p, q} : Finset V) := by
          intro w hw
          rcases mem_filter.mp hw with ⟨hwC, haw⟩
          refine mem_sdiff.mpr ⟨hwC, ?_⟩
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨fun h => h3.1.1 a (h ▸ haw), fun h => h3.1.2 p a hpa (h ▸ haw),
            fun h => h3.2 q p a hqp hpa (h ▸ haw)⟩
        have h3sub : ({a, p, q} : Finset V) ⊆ C := by
          intro w hw; simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption
        have h3card : ({a, p, q} : Finset V).card = 3 := by
          rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
          · simp [hpq]
          · simp [hap, haq]
        have := card_le_card hsub
        rw [card_sdiff_of_subset h3sub, hCeq4, h3card] at this
        exact this
      -- Since a ∈ High has d_H⁺(a) ≥ 2 while d_C⁺(a) ≤ 1 and H = insert y C, we MUST have A a y!
      have hH_ins : insert y C = H := by
        apply Finset.eq_of_subset_of_card_le
        · intro w hw; rcases mem_insert.mp hw with rfl | hw
          · exact (mem_filter.mp hyHigh).1
          · exact hCsub hw
        · rw [card_insert_of_notMem hyC, hCeq4, hHcard]
      have hay : A a y := by
        by_contra hnot
        have hsub : H.filter (fun w => A a w) ⊆ C.filter (fun w => A a w) := by
          intro w hw
          rcases mem_filter.mp hw with ⟨hwH, haw⟩
          rw [← hH_ins] at hwH
          rcases mem_insert.mp hwH with rfl | hwC
          · exact (hnot haw).elim
          · exact mem_filter.mpr ⟨hwC, haw⟩
        have := (card_le_card hsub).trans ha_Cdeg1
        have h2 := (mem_filter.mp haHigh).2
        omega
      -- Now p → a → y (with p ∈ C, p ≠ a, p ≠ y, a ≠ y), so y cannot point to y, a (2-free), or p (3-free)!
      obtain ⟨p, hpC, hpa⟩ := (hCstep a haC).1
      have hpH : p ∈ H := hCsub hpC
      have haH : a ∈ H := hCsub haC
      have hyH : y ∈ H := (mem_filter.mp hyHigh).1
      have hya : y ≠ a := fun h => h3.1.1 a (h ▸ hay)
      have hyp : y ≠ p := fun h => hyC (h ▸ hpC)
      have hap : a ≠ p := fun h => h3.1.1 p (h ▸ hpa)
      have hsub : H.filter (fun w => A y w) ⊆ H \ ({y, a, p} : Finset V) := by
        intro w hw
        rcases mem_filter.mp hw with ⟨hwH, hyw⟩
        refine mem_sdiff.mpr ⟨hwH, ?_⟩
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => h3.1.1 y (h ▸ hyw), fun h => h3.1.2 a y hay (h ▸ hyw),
          fun h => h3.2 p a y hpa hay (h ▸ hyw)⟩
      have h3sub : ({y, a, p} : Finset V) ⊆ H := by
        intro w hw; simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have h3card : ({y, a, p} : Finset V).card = 3 := by
        rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
        · simp [hap]
        · simp [hya, hyp]
      have := card_le_card hsub
      rw [card_sdiff_of_subset h3sub, hHcard, h3card] at this
      exact this
  have harcsH_le8 : inducedArcs A H ≤ 8 := by
    by_cases hC_hit : ∃ a ∈ C, a ∈ High
    · obtain ⟨a, haC, haHigh⟩ := hC_hit
      have hsum : (∑ y ∈ High, (H.filter (fun w => A y w)).card) ≤ 2 * High.card := by
        calc
          (∑ y ∈ High, (H.filter (fun w => A y w)).card)
              ≤ ∑ _y ∈ High, 2 := sum_le_sum fun y hy => hHigh_deg_le2_of_C a haC haHigh y hy
          _ = 2 * High.card := by rw [sum_const, smul_eq_mul, mul_comm]
      omega
    · -- No vertex of C lies in High, so High ⊆ H \ C has size ≤ 1!
      have hHigh_le1 : High.card ≤ 1 := by
        have hsub : High ⊆ H \ C := by
          intro y hy
          exact mem_sdiff.mpr ⟨(mem_filter.mp hy).1, fun hyC => hC_hit ⟨y, hyC, hy⟩⟩
        have := card_le_card hsub
        rw [card_sdiff_of_subset hCsub, hHcard] at this
        omega
      have hdeg_le4 : ∀ y ∈ High, (H.filter (fun w => A y w)).card ≤ 4 := by
        intro y hy
        have hsub : H.filter (fun w => A y w) ⊆ H.erase y := by
          intro w hw
          exact mem_erase.mpr ⟨fun h => h3.1.1 y (h ▸ (mem_filter.mp hw).2), (mem_filter.mp hw).1⟩
        have := (card_le_card hsub).trans (le_of_eq (card_erase_of_mem (mem_filter.mp hy).1))
        omega
      have hsum : (∑ y ∈ High, (H.filter (fun w => A y w)).card) ≤ 4 * High.card := by
        calc
          (∑ y ∈ High, (H.filter (fun w => A y w)).card)
              ≤ ∑ _y ∈ High, 4 := sum_le_sum hdeg_le4
          _ = 4 * High.card := by rw [sum_const, smul_eq_mul, mul_comm]
      omega
  -- Now prove 6 ≤ |secondN A a| for EVERY a ∈ C!
  have hsurp : ∀ a ∈ C, 6 ≤ (secondN A a).card := by
    intro a haC
    have haH : a ∈ H := hCsub haC
    -- Step 1: Find a sink bstar of B inside N⁺(a) ∩ B!
    have hsink_ex : ∃ bstar ∈ B, A a bstar ∧ (B.filter (fun u => A bstar u)).card = 0 := by
      by_cases haS : a ∈ S
      · have harcsB : inducedArcs A B ≤ 3 := by
          have hdrop := arc_drop_identity A h3.1 hR v
          change inducedArcs A B + 5 * 5 ≤ inducedArcs A H + 5 * B.card at hdrop
          omega
        obtain ⟨bstar, hbB, hbsink⟩ := exists_sink_threeFree_of_card_four_arcs_le_three A hBcard harcsB
        exact ⟨bstar, hbB, hS_allB a haS bstar hbB, hbsink⟩
      · have haHigh : a ∈ High := mem_filter.mpr ⟨haH, by
          have h1 := hmin a haH
          have hne1 : (H.filter (fun w => A a w)).card ≠ 1 :=
            fun h => haS (mem_filter.mpr ⟨haH, h⟩)
          omega⟩
        have harcsH_le7 : inducedArcs A H ≤ 7 := by
          have hsum : (∑ y ∈ High, (H.filter (fun w => A y w)).card) ≤ 2 * High.card := by
            calc
              (∑ y ∈ High, (H.filter (fun w => A y w)).card)
                  ≤ ∑ _y ∈ High, 2 := sum_le_sum fun y hy => hHigh_deg_le2_of_C a haC haHigh y hy
              _ = 2 * High.card := by rw [sum_const, smul_eq_mul, mul_comm]
          omega
        have harcsB_le2 : inducedArcs A B ≤ 2 := by
          have hdrop := arc_drop_identity A h3.1 hR v
          change inducedArcs A B + 5 * 5 ≤ inducedArcs A H + 5 * B.card at hdrop
          omega
        have htwo := exists_two_sinks_of_card_four_arcs_le_two A hBcard harcsB_le2
        set Z := B.filter (fun x => (B.filter (fun y => A x y)).card = 0)
        set Ba := B.filter (fun b => A a b)
        have hBa_card : 3 ≤ Ba.card := by
          have hsum : (H.filter (fun w => A a w)).card + Ba.card = 5 :=
            card_outN_inter_H_add_B A h3.1 hR haH
          have hle2 := hC_deg_le2 a haC
          omega
        -- Z ⊆ B (size ≥ 2) and Ba ⊆ B (size ≥ 3) inside B (size 4) => Z ∩ Ba is nonempty!
        have hinter_pos : 0 < (Z ∩ Ba).card := by
          have hun : (Z ∪ Ba).card ≤ 4 := by
            rw [← hBcard]
            exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
          have hadd := Finset.card_union_add_card_inter Z Ba
          omega
        obtain ⟨bstar, hb⟩ := card_pos.mp hinter_pos
        rcases mem_inter.mp hb with ⟨hbZ, hbBa⟩
        exact ⟨bstar, (mem_filter.mp hbZ).1, (mem_filter.mp hbBa).2, (mem_filter.mp hbZ).2⟩
    obtain ⟨bstar, hbB, habstar, hbsink⟩ := hsink_ex
    -- Step 2: outN A bstar (size 5) is disjoint from H ∪ B, hence ⊆ secondN A a!
    have hbstar_sub : outN A bstar ⊆ secondN A a := by
      intro w hwb
      rw [mem_outN] at hwb
      have hw_notH : w ∉ H := fun hwH => hno_BH bstar hbB w hwH hwb
      have hw_notB : w ∉ B := by
        intro hwB
        have h0 : w ∈ B.filter (fun u => A bstar u) := mem_filter.mpr ⟨hwB, hwb⟩
        rw [Finset.card_eq_zero.mp hbsink] at h0
        exact notMem_empty w h0
      have hwa : w ≠ a := fun h => hw_notH (h ▸ haH)
      have hnot_aw : ¬ A a w := fun haw => by
        rcases mem_union.mp (outN_subset_outN_union_secondN A h3.1 haH (mem_outN.mpr haw)) with
          h1 | h2
        · exact hw_notH h1
        · exact hw_notB h2
      exact mem_secondN.mpr ⟨hwa, hnot_aw, ⟨bstar, habstar, hwb⟩⟩
    -- Step 3: Find ONE extra vertex r ∈ (H ∪ B) ∩ secondN A a (automatically outside outN A bstar!)
    have hextra : ∃ r ∈ H ∪ B, r ∈ secondN A a := by
      by_cases haS : a ∈ S
      · -- a has unique out-neighbor q in H; pick q → r in C!
        obtain ⟨q, hqC, haq⟩ := (hCstep a haC).2
        obtain ⟨r, hrC, hqr⟩ := (hCstep q hqC).2
        have hqH : q ∈ H := hCsub hqC
        have hrH : r ∈ H := hCsub hrC
        have hra_ne : r ≠ a := fun h => h3.1.2 a q haq (h ▸ hqr)
        have hnot_ar : ¬ A a r := by
          intro har
          have hqr_ne : q ≠ r := fun h => h3.1.1 q (h ▸ hqr)
          have hsub : ({q, r} : Finset V) ⊆ H.filter (fun w => A a w) := by
            intro w hw; simp only [mem_insert, mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact mem_filter.mpr ⟨hqH, haq⟩
            · exact mem_filter.mpr ⟨hrH, har⟩
          have := card_le_card hsub
          rw [card_pair hqr_ne, (mem_filter.mp haS).2] at this; omega
        exact ⟨r, mem_union_left _ hrH, mem_secondN.mpr ⟨hra_ne, hnot_ar, ⟨q, haq, hqr⟩⟩⟩
      · -- a ∈ High has |N⁺(a) ∩ B| ≤ 3 < 4 = |B|, so pick b0 ∈ B \ N⁺(a); a hits s ∈ S and s → b0!
        have haHigh : a ∈ High := mem_filter.mpr ⟨haH, by
          have h1 := hmin a haH
          have hne1 : (H.filter (fun w => A a w)).card ≠ 1 :=
            fun h => haS (mem_filter.mpr ⟨haH, h⟩)
          omega⟩
        have hBa_lt4 : (B.filter (fun b => A a b)).card < B.card := by
          have hsum : (H.filter (fun w => A a w)).card + (B.filter (fun b => A a b)).card = 5 :=
            card_outN_inter_H_add_B A h3.1 hR haH
          have h2 := (mem_filter.mp haHigh).2
          omega
        have hdiff_pos : 0 < (B \ B.filter (fun b => A a b)).card := by
          rw [card_sdiff_of_subset (filter_subset _ _)]; omega
        obtain ⟨b0, hb0⟩ := card_pos.mp hdiff_pos
        rcases mem_sdiff.mp hb0 with ⟨hb0B, hb0_not⟩
        have hnot_ab0 : ¬ A a b0 := fun hab0 => hb0_not (mem_filter.mpr ⟨hb0B, hab0⟩)
        have hb0_ne : b0 ≠ a := fun h =>
          Finset.disjoint_left.mp (disjoint_outN_secondN A v) haH (h ▸ hb0B)
        obtain ⟨s, hsS, has⟩ := hHigh_hits_S a haHigh
        exact ⟨b0, mem_union_right _ hb0B,
          mem_secondN.mpr ⟨hb0_ne, hnot_ab0, ⟨s, has, hS_allB s hsS b0 hb0B⟩⟩⟩
    obtain ⟨r, hrHB, hr2⟩ := hextra
    have hr_not_bstar : r ∉ outN A bstar := by
      intro hrb
      rw [mem_outN] at hrb
      rcases mem_union.mp hrHB with hrH | hrB
      · exact hno_BH bstar hbB r hrH hrb
      · have h0 : r ∈ B.filter (fun u => A bstar u) := mem_filter.mpr ⟨hrB, hrb⟩
        rw [Finset.card_eq_zero.mp hbsink] at h0
        exact notMem_empty r h0
    have hsub : insert r (outN A bstar) ⊆ secondN A a := insert_subset hr2 hbstar_sub
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hr_not_bstar, card_outN_eq hR bstar] at hcard
    exact hcard
  refine ⟨C, hCsub, hC4, fun a haC => ⟨hsurp a haC, ?_⟩⟩
  obtain ⟨p, hpC, hpa⟩ := (hCstep a haC).1
  exact ⟨p, hpa, by have := hsurp p hpC; omega⟩

/-- **Corollary 3.3 (Regular `d = 5` CH, all residues including `n = 15`):**
    Every nonempty `5`-regular `3`-free digraph has at least `16` vertices. -/
theorem regular_threeFree_five_order_ge_16 (A : V → V → Prop) [DecidableRel A]
    (h3 : IsThreeFree A) (hR : IsRegular A 5) (hne : Nonempty V) :
    16 ≤ Fintype.card V :=
  regular_threeFree_order_ge_of_e2 A h3 hR hne (regular_threeFree_five_e2 A h3 hR)

end DischargingClosures

#print axioms quadratic_eq_P2_sub_Ent
#print axioms nonTriangle_arc_P2_bound
#print axioms tournament_balanced_quadratic_eq_zero
#print axioms regular_threeFree_order_ge_of_e2
#print axioms arc_drop_identity
#print axioms regular_e2_ge_of_surplus_witness
#print axioms regular_oriented_three_e2
#print axioms regular_threeFree_four_e2
#print axioms regular_threeFree_four_order_ge_13
#print axioms regular_threeFree_five_e2
#print axioms regular_threeFree_five_order_ge_16

end LeanCH.BalancedSecondNeighborhood
