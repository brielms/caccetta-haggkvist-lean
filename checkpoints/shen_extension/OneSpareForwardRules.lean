import checkpoints.shen_extension.CHForwardCatalog
import checkpoints.shen_extension.OneSpareTurns
import checkpoints.shen_extension.CHRuleCatalog

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 CHRuleCatalog

def BelowFour (n r q : ℕ) : Prop :=
  4≤q ∧ 2≤r ∧ r≤2*q ∧ (r+(r-1))*(r+(r-1)+1)<2*(r*(r+3)+(r-1)*7) ∧ n<4*r

@[aesop safe forward (rule_sets := [CHGraphFamilies])]
theorem exclude_below_four {p} (bad : Bad p) : ¬BelowFour p.n p.s (cutoff p) := by
  rintro ⟨hq,pos,room,budget,small⟩
  have order := below_four_times (qfree_of_noShort bad.loopless bad.missing) hq
    (nonempty_range_iff.mpr bad.order.ne') (fun v hv=>Compose.FloorSix.out_card bad.degree (mem_range.mp hv))
    pos room budget
  rw [card_range] at order
  omega

theorem cycle31 {D : CH.Digraph} (loop : CH.Loopless D 31) (deg : CH.MinOutdegreeAtLeast D 31 8) :
    CH.HasDirectedCycleAtMost D 31 4 := by
  by_contra miss
  have min8 v (vm : v∈range 31) := Compose.FloorSix.out_card deg (mem_range.mp vm)
  have cap := below_four_times (qfree_of_noShort loop miss) (by decide)
    (nonempty_range_iff.mpr (by decide : 31≠0)) min8 (by decide) (by decide) (by decide)
  rw [card_range] at cap
  omega

#print axioms cycle31
#print axioms exclude_below_four
end LeanCH.BR.OneSpareGrowth
