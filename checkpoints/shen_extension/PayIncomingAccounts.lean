import checkpoints.shen_extension.CompleteArrivalBill

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

theorem bounded_booked_length {D V q r target K} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target) (km : K∈booked t) : K.card≤r := by
  obtain ⟨Y,ym,rfl⟩ := mem_image.mp km
  have uv := rep_native t ym
  rcases t.located Y ym with first|later
  · exact (card_le_card first).trans (reg _ uv).le
  obtain ⟨hq,a,b,c,d,_⟩ := ready.cycle
  have low := (mem_filter.mp (mem_filter.mp (t.represents Y ym)).1).2
  have hi := low_third_second free hq reg uv a b c d low
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at one
  have two := @card_B2 D V (t.rep Y)
  rw [rep_key t ym] at two
  have := card_le_card later
  change (ball D V (t.rep Y) 2).card≤2*r+1 at hi
  omega

theorem incoming_accounts_paid {D V q r target δ cap C A} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap A) (account : CompleteAccount t C A)
    (near : r≤fullRowFloor q r+(q-3)) (enough : fullRowFloor q r≤r-1)
    (affordable : δ+8+cap<3*(r-1)+fullRowFloor q r) : A=∅ := by
  classical
  by_contra nonempty
  have live := nonempty_iff_ne_empty.mpr nonempty
  obtain ⟨Z,zm⟩ := live
  have ⟨zk,_,_,_,term,route⟩ := mark.routed Z zm
  have ⟨stock,headroom⟩ := arrival_reserves_parents free reg ready route
    ((bounded_booked_length free reg t ready zk).trans near) enough
  have ceiling := terminal_direct_budget free reg t policy ready term
  have due := account.received ⟨Z,zm⟩
  have h : (fullRowFloor q r:ℚ)≤(highParents D V C 3 (3*r)).card := by exact_mod_cast stock
  have lim : ((allParents D V C).card:ℚ)≤δ := by exact_mod_cast headroom
  have count : (A.card:ℚ)≤cap := by exact_mod_cast mark.bounded
  have total : (δ:ℚ)+8+cap<((3*(r-1):ℕ):ℚ)+fullRowFloor q r := by exact_mod_cast affordable
  linarith only [ceiling,due,h,lim,count,total]

attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,account,near,enough,affordable]) (rule_sets := [CHGraphFamilies])] incoming_accounts_paid
#print axioms bounded_booked_length
#print axioms incoming_accounts_paid
end LeanCH.BR.LowShellCycleSelection
