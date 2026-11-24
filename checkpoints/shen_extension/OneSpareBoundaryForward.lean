import checkpoints.shen_extension.OneSpareBoundary
import checkpoints.shen_extension.OneSpareForwardRules
import checkpoints.shen_extension.PackingForwardRules
import checkpoints.shen_extension.dot_tensor_research.DegreeEightPaperInterface

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 CHRuleCatalog

attribute [aesop safe forward (immediate := [free,hq,two,cut,degree,sub,marked,room])
  (rule_sets := [CHGraphFamilies])] marked_capacity
attribute [aesop safe forward (immediate := [free,av,dist,sub,pairs])
  (rule_sets := [CHGraphFamilies])] ParentCutPacking.covers_outside_ball
attribute [aesop safe forward (immediate := [degree,cover])
  (rule_sets := [CHGraphFamilies])] ParentCutPacking.cross_capacity

/-- Any affordable retained degree may witness this region. The size
of the prefix that keeps that degree is chosen in the proof. -/
def Window (n r q : ℕ) : Prop :=
  4≤q ∧ ∃d,3≤d ∧ d≤r ∧ d≤2*q ∧
    (d+(d-1))*(d+(d-1)+1)<2*(d*(d+3)+(d-1)*7) ∧ n≤r+3*d

@[aesop safe forward (rule_sets := [CHGraphFamilies])]
theorem exclude_window {p} (bad : Bad p) : ¬Window p.n p.s (cutoff p) := by
  rintro ⟨hq,d,three,le,room,profile,fit⟩
  let m := min p.n (4*d)
  have pos : 0<m := lt_min bad.order (by omega)
  have small : m≤4*d := min_le_right .. 
  have within : m≤p.n := min_le_left ..
  have quota : CH.ceilDiv m d≤4 := by
    unfold CH.ceilDiv
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<d)).mpr
    omega
  have loss : d+(p.n-m)≤p.s := by dsimp only [m]; omega
  have child := PrefixFrontier.prefix_child p bad pos (by omega : 0<d) within loss (quota.trans hq)
  have free := (qfree_of_noShort bad.loopless bad.missing).mono_set (range_mono within)
  have size := above_four_times free hq (nonempty_range_iff.mpr pos.ne')
    (fun v (hv : v∈range m)=>Compose.FloorSix.out_card child.degree (mem_range.mp hv)) three room profile
  rw [card_range] at size
  exact (Nat.not_lt_of_ge small) (show 4*d<m from size)

theorem packed_four {d} (three : 3≤d) (fit : d≤2*4)
    (cap : (d+(d-1))*(d+(d-1)+1)<2*(d*(d+3)+(d-1)*7)) :
    DotDegreeSeven.Endpoint 4 d := by
  intro D V free live order degree
  have size := above_four_times free (by decide) live degree three fit cap
  omega

theorem packed_four_eight : DotDegreeSeven.Endpoint 4 8 :=
  packed_four (by decide) (by decide) (by decide)

/-- Checked degree-eight assembly after the cutoff-four endpoint. -/
theorem degree_eight_of_remaining
    (remaining : ∀q,5≤q → q≤10 → DotDegreeSeven.Endpoint q 8)
    {n} (D : CH.Digraph) (hn : 0<n) (loop : CH.Loopless D n) (deg : CH.MinOutdegreeAtLeast D n 8) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 8) := by
  refine PrefixFrontier.degree_eight_of_packed ?_ D hn loop deg
  intro q low high
  by_cases equal : q=4
  · exact equal ▸ packed_four_eight
  · exact remaining q (by omega) high

#print axioms exclude_window
#print axioms packed_four_eight
#print axioms degree_eight_of_remaining
end LeanCH.BR.OneSpareGrowth
