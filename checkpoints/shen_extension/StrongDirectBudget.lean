import checkpoints.shen_extension.CyclicExteriorEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- A complete cycle with all its rows strong needs enough physical common
parents to absorb its direct stock. Any reserve of high parents remains
unavailable to the representatives, at the very same cycle. -/
theorem strong_direct_demand {D V q r target C δ cap} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap ∅) (term : StrongTerminal D V r C)
    (sparse : r-q+1<r-1) :
    3*(r-1)+(highParents D V C 3 (3*r)).card≤(allParents D V C).card+8 := by
  have roots K (km : K∈booked t) : ∀x∈K,Rooted D V x K := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp km; exact t.rooted _ (t.assigned _ ym)
  have cost K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ ym)
  have stock := terminal_stock free (by have := ready.cycle.1; omega) reg term mark.bookedHere roots cost sparse
  have due := mark.due
  rw [sum_empty,add_zero] at due
  have budget := terminal_direct_budget free reg t policy ready term
  have needed := stock.trans due
  have exactBill : ((3*(r-1):ℕ):ℚ)+(highParents D V C 3 (3*r)).card≤((allParents D V C).card:ℚ)+8 := by linarith only [needed,budget]
  exact_mod_cast exactBill

/-- The parent count and the stock bound apply at the original direct
claim even if no routed claim arrives. The output names an actual row. -/
theorem direct_low_cycle_row {D V q r target g mid top C δ cap}
    (free : QFree D V q) (reg : OutEq r D V) (t : Selection D V q r 3 (3*r))
    (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap ∅) (account : CompleteAccount t C ∅)
    (length : C.card=r-1) (next : ∀z∈exterior D V C,Rooted D V z (exterior D V C))
    (score : ScoreRoom q r (r-1) g) (step : GrowthRoom q r g mid) (again : GrowthRoom q r mid top)
    (sparse : r-q+1<r-1) (cost : V.card+8<C.card+top+3*(r-1)) :
    ∃c∈C,(ball D V c 3).card=3*r+1 := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have space := ready.space
  have width := account.width
  have roots : ∀c∈C,Rooted D V c C := by
    obtain ⟨Y,ym,eq⟩ := mem_image.mp mark.bookedHere; exact eq ▸ t.rooted _ (t.assigned _ ym)
  have live : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨v,vm⟩ := live
  have ev : exterior D V C⊆V := by
    intro e em; obtain ⟨_,_,arc⟩ := mem_biUnion.mp (mem_sdiff.mp em).1; exact outN_subset arc
  have limit := parent_room free hq reg (by omega) (roots v vm).sub ev ⟨v,vm⟩
    (card_pos.mp (by omega)) (by omega) account.allHeads (width.symm ▸ score) step again
  by_contra! all
  have term : StrongTerminal D V r C :=
    ⟨length,roots,width,next,fun x xm=>by have := all x xm; have := account.high x xm; omega⟩
  have heavy := strong_direct_demand free reg t policy ready mark term sparse
  omega

attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,term,sparse]) (rule_sets := [CHGraphFamilies])] strong_direct_demand
attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,account,length,next,score,step,again,sparse,cost]) (rule_sets := [CHGraphFamilies])] direct_low_cycle_row
#print axioms strong_direct_demand
#print axioms direct_low_cycle_row
end LeanCH.BR.LowShellCycleSelection
