import LeanCH.BR.BRWeightedDeletionThreshold
import checkpoints.shen_extension.SharedArcFlatResponse

/-! The flat four-index test reads arc criticality. After a safe insertion a→b into a
flat graph, deleting any arc x→y of the child is payable exactly when the entry T(y,x)
reaches p_a w_b. At the tail and the head the entry is explicit, so the exchange of an
old arc for the new one is decided by the flat laws alone. All orders, every cutoff. -/
namespace LeanCH.BR.Closure.FlatExchange
open Finset Matrix FiniteCutInverse WeightedSD BRq2 SharedArcFlatResponse
open scoped Matrix

/-- Criticality of every arc of the child, in old-graph data. -/
theorem critical_iff {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (x y : V) (arc : insertArc E a b x y = true) :
    SmallRow q (eraseArc (insertArc E a b) x y) V ↔
      (p a : ℝ) * (w b : ℝ) ≤
        test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b y x := by
  obtain ⟨H, inv, eq⟩ := inverse_test hq small a b off safe wp wm wr pc
  rw [deletion_smallRow_iff inv x y arc, eq y x]
  have pa : (0 : ℝ) < (p a : ℝ) := by exact_mod_cast (wp a a.property).2
  have wb : (0 : ℝ) < (w b : ℝ) := by exact_mod_cast (wp b b.property).1
  have s : 0 < (p a : ℝ) * (w b : ℝ) := mul_pos pa wb
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h s.le
    nlinarith [this]
  · intro h
    by_contra! lt
    have := mul_lt_mul_of_pos_left lt s
    nlinarith [this]

/-- Exchange at the tail. Trading an old arc a→v for the new arc a→b gives a payable
graph exactly when v is at least as heavy as b in the old row law. -/
theorem tail_exchange {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (v : V) (old : E a v = true) :
    SmallRow q (eraseArc (insertArc E a b) a v) V ↔ w b ≤ w v := by
  rw [critical_iff hq small a b off safe wp wm wr pc a v (insertArc_mono E a b a v old)]
  have col : test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ))
      q a b v a = (w v : ℝ) * (p a : ℝ) := by simp only [test]; ring
  rw [col]
  have pa : (0 : ℝ) < (p a : ℝ) := by exact_mod_cast (wp a a.property).2
  constructor
  · intro h
    have h' : (p a : ℝ) * (w b : ℝ) ≤ (p a : ℝ) * (w v : ℝ) := by nlinarith [h]
    exact_mod_cast le_of_mul_le_mul_left h' pa
  · intro h
    have h' : (w b : ℝ) ≤ (w v : ℝ) := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left h' pa.le]

/-- Exchange at the head. Trading an old arc k→b for the new arc a→b gives a payable
graph exactly when k is at least as expensive as a in the old column law. -/
theorem head_exchange {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (k : V) (old : E k b = true) :
    SmallRow q (eraseArc (insertArc E a b) k b) V ↔ p a ≤ p k := by
  rw [critical_iff hq small a b off safe wp wm wr pc k b (insertArc_mono E a b k b old)]
  have rowb : test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ))
      q a b b k = (w b : ℝ) * (p k : ℝ) := by simp only [test]; ring
  rw [rowb]
  have wb : (0 : ℝ) < (w b : ℝ) := by exact_mod_cast (wp b b.property).1
  constructor
  · intro h
    have h' : (w b : ℝ) * (p a : ℝ) ≤ (w b : ℝ) * (p k : ℝ) := by nlinarith [h]
    exact_mod_cast le_of_mul_le_mul_left h' wb
  · intro h
    have h' : (p a : ℝ) ≤ (p k : ℝ) := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left h' wb.le]

end LeanCH.BR.Closure.FlatExchange

#print axioms LeanCH.BR.Closure.FlatExchange.critical_iff
#print axioms LeanCH.BR.Closure.FlatExchange.tail_exchange
#print axioms LeanCH.BR.Closure.FlatExchange.head_exchange
