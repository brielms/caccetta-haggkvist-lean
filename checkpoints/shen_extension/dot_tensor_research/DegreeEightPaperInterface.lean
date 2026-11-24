import checkpoints.shen_extension.VerifiedDegreeFrontier
import checkpoints.shen_extension.PrefixOrderFrontier
import checkpoints.shen_extension.SevenDegreeCapstoneEntry

namespace LeanCH.BR.PrefixFrontier
open DotDegreeSeven

/-- A packed endpoint supplies the entire affordable higher-degree window. -/
theorem endpoint_window {n r d q} (solved : Endpoint q d) (hd : 0<d) (hq : 0<q)
    (D : CH.Digraph) (hn : 0<n) (degree : d≤r) (budget : n+d≤d*q+r)
    (loop : CH.Loopless D n) (go : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n q :=
  SevenDegreeCapstoneEntry.transfer hd hq
    (fun m G mp fit lp deg=>from_endpoint solved mp (by simpa only [Nat.mul_comm d q] using fit) lp deg)
    D hn degree budget loop go

/-- At degree eight only the seven maximum orders need to be independently supplied.
The checked finite frontier supplies all cutoffs outside this interval. -/
theorem degree_eight_of_packed (packed : ∀q,4≤q → q≤10 → Endpoint q 8)
    {n} (D : CH.Digraph) (hn : 0<n) (loop : CH.Loopless D n) (deg : CH.MinOutdegreeAtLeast D n 8) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 8) := by
  by_contra miss
  have live := DotDegreeEight.narrowed_eight (D:=D) (n:=n) ⟨hn,(by change 0<(8:ℕ); decide),loop,deg,miss⟩
  let q := CH.ceilDiv n 8
  have bounds : 4≤q ∧ q≤10 := by
    change DotDegreeEight.Narrowed n q at live
    unfold DotDegreeEight.Narrowed at live
    omega
  have size : n≤q*8 := by dsimp [q,CH.ceilDiv]; omega
  exact miss (from_endpoint (packed q bounds.1 bounds.2) hn size loop deg)

/-- Order 48 alone suffices to discharge every degree-eight order at cutoff six
and the corresponding higher-degree window. -/
theorem from_order_48 (packed : Endpoint 6 8)
    {n r} (hn : 0<n) (hr : 8≤r) (budget : n≤r+40)
    (D : CH.Digraph) (loop : CH.Loopless D n) (go : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n 6 :=
  endpoint_window packed (by decide) (by decide) D hn hr (by omega) loop go

#print axioms endpoint_window
#print axioms degree_eight_of_packed
#print axioms from_order_48
/-- Consequence for the exact hypotheses shared by the six live root contexts,
conditional on formal proofs of the seven paper endpoints. -/
theorem paper_frontier (packed : ∀q,4≤q → q≤10 → Endpoint q 8)
    {n r : ℕ} (D : CH.Digraph) (hn : 0<n) (loop : CH.Loopless D n)
    (deg : CH.MinOutdegreeAtLeast D n r) (floor : 8≤r)
    (hq : 0<CH.ceilDiv n r) (miss : ¬CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r)) :
    9≤r ∧ 8*CH.ceilDiv n r+r<n+8 := by
  let q := CH.ceilDiv n r
  have next : 9≤r := by
    by_contra low
    have eq : r=8 := by omega
    subst r
    exact miss (degree_eight_of_packed packed D hn loop deg)
  refine ⟨next,lt_of_not_ge (fun budget=>miss ?_)⟩
  apply SevenDegreeCapstoneEntry.transfer (d:=8) (by decide) hq _ D hn floor budget loop deg
  intro m G mp bound lp dg
  obtain ⟨cycle,valid,length⟩ := degree_eight_of_packed packed G mp lp dg
  exact ⟨cycle,valid,length.trans (by change (m+8-1)/8≤CH.ceilDiv n r; omega)⟩

#print axioms paper_frontier
end LeanCH.BR.PrefixFrontier
