import checkpoints.shen_extension.dot_tensor_research.DegreeSevenVerified_20261121

namespace LeanCH.BR.SevenDegreeCapstoneEntry
open Finset BRq3

theorem at_cutoff {n r q} {D : CH.Digraph} (hn : 0 < n) (degree : 7 ≤ r)
    (order : n ≤ 7*q) (loop : CH.Loopless D n) (minimum : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨cycle,hc,length⟩ := DotDegreeSeven.ch_degree_seven n D hn loop (Triangle24.minOut_mono degree minimum)
  exact ⟨cycle,hc,length.trans (by unfold CH.ceilDiv; omega)⟩

/-- Deleting k labels loses at most k distinct heads per retained vertex. -/
private theorem restrict_degree {D : CH.Digraph} {m n d r : ℕ}
    (sub : m ≤ n) (room : d+(n-m) ≤ r) (deg : CH.MinOutdegreeAtLeast D n r) :
    CH.MinOutdegreeAtLeast D m d := by
  classical
  intro v hv
  let A := outN D (range n) v
  let B := outN D (range m) v
  have inc : B ⊆ A := fun j hj => mem_outN.mpr
    ⟨range_mono sub (mem_outN.mp hj).1,(mem_outN.mp hj).2⟩
  have lost : A \ B ⊆ range n \ range m := by
    intro j hj
    obtain ⟨ja,jb⟩ := mem_sdiff.mp hj
    obtain ⟨jn,edge⟩ := mem_outN.mp ja
    exact mem_sdiff.mpr ⟨jn,fun jm => jb (mem_outN.mpr ⟨jm,edge⟩)⟩
  have cap := card_le_card lost
  rw [card_sdiff_of_subset (range_mono sub),card_range,card_range] at cap
  have sum := card_sdiff_add_card_eq_card inc
  have low : r ≤ A.card := Compose.FloorSix.out_card deg (hv.trans_le sub)
  obtain ⟨S,ss,sz⟩ := exists_subset_card_eq (show d ≤ B.card by omega)
  refine ⟨S.toList,by simpa using sz,S.nodup_toList,?_⟩
  intro j hj
  obtain ⟨jm,edge⟩ := mem_outN.mp (ss (mem_toList.mp hj))
  exact ⟨mem_range.mp jm,edge⟩

/-- A proof at degree d and cutoff q transfers to every r ≥ d whose excess
degree can cover all vertices beyond the solved order d*q. -/
theorem transfer {n r d q} (hd : 0 < d) (hq : 0 < q)
    (solved : ∀ m (G : CH.Digraph), 0 < m → m ≤ d*q → CH.Loopless G m →
      CH.MinOutdegreeAtLeast G m d → CH.HasDirectedCycleAtMost G m q)
    (D : CH.Digraph) (hn : 0 < n) (degree : d ≤ r) (room : n+d ≤ d*q+r)
    (loop : CH.Loopless D n) (minimum : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n q := by
  let m := min n (d*q)
  have pos : 0 < m := lt_min hn (Nat.mul_pos hd hq)
  have within : m ≤ n := min_le_left .. 
  have budget : m ≤ d*q := min_le_right ..
  have deg := restrict_degree (d:=d) within (by dsimp [m]; omega) minimum
  obtain ⟨L,cycle,length⟩ := solved m D pos budget (fun i hi => loop i (hi.trans_le within)) deg
  cases L with
  | nil => exact cycle.elim
  | cons h t =>
    exact ⟨h::t,⟨cycle.1,cycle.2.1,fun i hi => (cycle.2.2.1 i hi).trans_le within,
      cycle.2.2.2⟩,length⟩

theorem seven_window {n r q} {D : CH.Digraph} (hn : 0 < n) (hq : 0 < q)
    (degree : 7 ≤ r) (room : n+7 ≤ 7*q+r)
    (loop : CH.Loopless D n) (minimum : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n q :=
  transfer (by decide : 0<7) hq (fun _ _ hm bound => at_cutoff hm le_rfl bound)
    D hn degree room loop minimum

#print axioms at_cutoff
#print axioms transfer
#print axioms seven_window
end LeanCH.BR.SevenDegreeCapstoneEntry
