import checkpoints.shen_extension.OneLossCutoffDescent

namespace LeanCH.BR.OneLossCutoffDescent
open CHRuleCatalog

/-- Direct CH conclusion for the two cutoffs where the smaller child
already meets an unconditional exclusion. -/
theorem literal_direct {n s : ℕ} {D : CH.Digraph} (hn : 0<n) (hs : 0<s)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (window : Window n s (CH.ceilDiv n s))
    (covered : CH.ceilDiv n s=4 ∨ CH.ceilDiv n s=6 ∧
       3*(n-1)*(n-1)≤6*(n-1)*(2*s-1)+7*(2*s-1)*(2*s-1)) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  by_contra missing
  let p : Input := ⟨n,s,D⟩
  have bad : Bad p := ⟨hn,hs,loopless,degree,missing⟩
  rcases covered with four | ⟨six,ratio⟩
  · exact cutoff_four (p:=p) four window bad
  · exact cutoff_six (p:=p) six window ratio bad

/-- Finite arithmetic regression for the directly paid orders at cutoffs 4
and 6 in the old reduced region. The general window theorem is unbounded. -/
private def orders (q s : ℕ) : List ℕ :=
  (List.range (q*s+1)).filter (fun n=>decide (CH.ceilDiv n s=q ∧ 6≤s ∧ q<s ∧ s≤2*q ∧
    n≤q/2*(2*s-1) ∧ (q=4 ∨ q=6 ∧ 3*(n-1)*(n-1)≤6*(n-1)*(2*s-1)+7*(2*s-1)*(2*s-1))))

theorem direct_tables :
    ([6,7,8].map (orders 4) = [[19,20,21,22],[22,23,24,25,26],[25,26,27,28,29,30]]) ∧
    ([7,8,9,10,11,12].map (orders 6) =
      [[36,37],[41,42,43],[46,47,48,49],[51,52,53,54],[56,57,58,59,60],[61,62,63,64,65]]) := by
  decide

example : ¬ Window 23 6 4 := by unfold Window; decide
example : Window 38 7 6 := by unfold Window; decide
example : ¬(3*(38-1)*(38-1)≤6*(38-1)*(2*7-1)+7*(2*7-1)*(2*7-1)) := by decide

#print axioms literal_direct
#print axioms direct_tables
end LeanCH.BR.OneLossCutoffDescent
