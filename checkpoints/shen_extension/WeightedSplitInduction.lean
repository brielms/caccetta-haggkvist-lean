import checkpoints.shen_extension.WeightedOneVertexSplit
import LeanCH.BR.BRWeightedCycleStructure

namespace LeanCH.BR.Closure.WeightedSplitInduction
open Finset BRq2 BRq3 BR45 ShenPrimeTransition WeightedOneVertexSplit

/-- A finite graph-family derivation. Along each edge the labels and the
weights are inherited, and the opposite nonempty side is removed. -/
inductive Tree (q : ℕ) (D : CH.Digraph) (w : ℕ→ℕ) : Finset ℕ → Prop where
  | leaf {V} (size : V.card≤q+2) : Tree q D w V
  | fork {L B r} (dis : Disjoint L B) (rL : r∉L) (rB : r∉B)
      (ll : L.Nonempty) (bl : B.Nonempty) (left : ∀a∈L,paid q D w B a)
      (right : ∀b∈B,paid q D w L b) (tl : Tree q D w (insert r L))
      (tb : Tree q D w (insert r B)) : Tree q D w (insert r (L∪B))

theorem excludes {q D w V} (hq : 2≤q) (tree : Tree q D w V) (vf : QFree D V q)
    (live : V.Nonempty) : ¬Strict q D V w := by
  induction tree with
  | leaf size =>
    exact fun st => (WeightedSD.smallRow_of_card_le_add_two hq vf size).no_strict live _
      (fun _ _ => Nat.cast_nonneg _) st
  | @fork L B r dis rL rB ll bl left right tl tb ihl ihb =>
    intro st
    have loop := Bool.eq_false_iff.mpr (loopfree vf (by omega) (mem_insert_self r (L∪B)))
    rcases split dis rL rB loop st left right with a | b
    · exact ihl (vf.mono_set (insert_subset_insert r subset_union_left)) ⟨r,mem_insert_self _ _⟩ a
    · exact ihb (vf.mono_set (insert_subset_insert r subset_union_right)) ⟨r,mem_insert_self _ _⟩ b

/-- Literal CH on every input admitting a paid split tree. -/
theorem cycle {q n s D} (hq : 2≤q) (hn : 0<n) (ord : n≤q*s)
    (loop : CH.Loopless D n) (deg : CH.MinOutdegreeAtLeast D n s)
    (tree : Tree q D (fun _ => 1) (range n)) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  apply excludes hq tree (qfree_of_noShort loop no) ⟨0,mem_range.mpr hn⟩
  intro x hx
  have dg : s≤(outN D (range n) x).card := Compose.FloorSix.out_card deg (mem_range.mp hx)
  have le := Nat.mul_le_mul_left q dg
  have hi : n<1+q*(outN D (range n) x).card := by omega
  simp only [WeightedSD.row,WeightedSD.outW_unit,WeightedSD.mass,Nat.cast_one,sum_const,card_range,
    nsmul_eq_mul,mul_one]
  exact_mod_cast hi

#print axioms excludes
#print axioms cycle
end LeanCH.BR.Closure.WeightedSplitInduction
