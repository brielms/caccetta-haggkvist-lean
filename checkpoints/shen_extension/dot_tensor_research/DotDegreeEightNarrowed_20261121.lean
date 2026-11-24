
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightFrontier_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightOrder51_20261121

namespace LeanCH.BR.DotDegreeEight
open Finset BRq2 BRq3 BR45 CHRuleCatalog

theorem ch_at_51 {D : CH.Digraph} (loop : CH.Loopless D 51)
    (deg : CH.MinOutdegreeAtLeast D 51 8) :
    CH.HasDirectedCycleAtMost D 51 (CH.ceilDiv 51 8) := by
  change CH.HasDirectedCycleAtMost D 51 7
  by_contra no
  exact order51_q7 (qfree_of_noShort loop no) (card_range 51)
    (fun _ hv => Compose.FloorSix.out_card deg (mem_range.mp hv))

def Narrowed (n q : ℕ) : Prop :=
  (q=4 ∧ 31≤n ∧ n≤32) ∨ (q=5 ∧ 37≤n ∧ n≤40) ∨
  (q=6 ∧ 44≤n ∧ n≤48) ∨ (q=7 ∧ 52≤n ∧ n≤56) ∨
  (q=8 ∧ n=64) ∨ (q=9 ∧ 69≤n ∧ n≤72) ∨ (q=10 ∧ n=80)

theorem narrowed_eight {n : ℕ} {D : CH.Digraph} (bad : Bad ⟨n,8,D⟩) :
    Narrowed n (CH.ceilDiv n 8) := by
  have no : n≠51 := by
    intro e
    subst n
    exact bad.missing (ch_at_51 bad.loopless bad.degree)
  have r := remaining_eight bad
  unfold Remaining at r
  unfold Narrowed
  rcases r with a|b|c|d|e|f|g
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d.1,by have h := d.2.1; omega,d.2.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl f)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr g)))))

#print axioms ch_at_51
#print axioms narrowed_eight
end LeanCH.BR.DotDegreeEight


