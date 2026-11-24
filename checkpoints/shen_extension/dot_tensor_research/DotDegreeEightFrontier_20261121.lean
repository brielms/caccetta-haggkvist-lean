
import checkpoints.shen_extension.dot_tensor_research.DiagonalEight
import checkpoints.shen_extension.SevenDegreeCapstoneEntry
import checkpoints.shen_extension.OneLossCutoffDescent

namespace LeanCH.BR.DotDegreeEight
open Finset BRq2 BRq3 BR45 CHRuleCatalog

/-- This is a certified frontier, not a claim of impossibility inside it. -/
def Remaining (n q : ℕ) : Prop :=
  (q=4 ∧ 31≤n ∧ n≤32) ∨ (q=5 ∧ 37≤n ∧ n≤40) ∨
  (q=6 ∧ 44≤n ∧ n≤48) ∨ (q=7 ∧ 51≤n ∧ n≤56) ∨
  (q=8 ∧ n=64) ∨ (q=9 ∧ 69≤n ∧ n≤72) ∨ (q=10 ∧ n=80)

theorem remaining_eight {n : ℕ} {D : CH.Digraph} (bad : Bad ⟨n,8,D⟩) :
    Remaining n (CH.ceilDiv n 8) := by
  let p : Input := ⟨n,8,D⟩
  let q := cutoff p
  change Remaining n q
  have ord := remaining_from_run p bad
  change 3≤q ∧ 6≤(8:ℕ) ∧
    ((q=2*8-6 ∧ 7≤(8:ℕ) ∧ 8≤11 ∧ (n=q*8 ∨ 8=7 ∧ n+1=q*8)) ∨
       (q≤2*8-7 ∧ (59≤(8:ℕ) → q≤2*8-8) ∧ (8192≤(8:ℕ) → q≤2*8-9))) at ord
  have eq : q=(n+7)/8 := rfl
  have lim : n≤q*8 := by omega
  have qmin : 4≤q := by
    by_contra! c
    have q3 : q=3 := by omega
    exact exclusion_from_run p bad .triangle24 ⟨q3,by change n≤24; omega⟩
  have room : 7*q+1<n := by
    by_contra! w
    exact bad.missing (SevenDegreeCapstoneEntry.seven_window bad.order
      (show 0<q by omega) (by decide : 7≤8) (by omega : n+7≤7*q+8) bad.loopless bad.degree)
  have four : q=4 → 31≤n := by
    intro e
    by_contra! lt
    apply OneLossCutoffDescent.cutoff_four (p:=p) e ?_ bad
    change 8≤2*q ∧ n≤(q/2)*(2*8-1)
    omega
  have diag : q=8 → n=64 := by
    intro e
    by_contra ne
    exact bad.missing (show CH.HasDirectedCycleAtMost D n q by
      rw [e]
      exact DiagonalEight.cycle_at_most_eight D bad.order (by omega) bad.loopless bad.degree)
  have ninth : q=9 → 69≤n := by
    intro e
    by_contra! lt
    apply exclusion_from_run p bad .fifthLow
    change 7≤(8:ℕ) ∧ q=2*8-7 ∧ n+4≤q*8
    omega
  unfold Remaining
  rcases ord.2.2 with top | lower
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
  · have maxq : q≤9 := by omega
    interval_cases q <;> first | contradiction | omega

#print axioms remaining_eight
end LeanCH.BR.DotDegreeEight



