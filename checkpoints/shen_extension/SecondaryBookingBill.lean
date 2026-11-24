import checkpoints.shen_extension.SwitchBooking

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- In the actual repaired selection every cyclic claimant without a first-layer
claim must be the literal cycle to which it moved. -/
theorem secondary_key {D V q r C Y} {s : Selection D V q r 3 (3*r)}
    (book : ShellBooking s) (no : ¬FirstClaim s C) (claim : Y∈claims s C)
    (cy : ¬QFree D (outN D V (s.rep Y)) (outN D V (s.rep Y)).card) :
    Y∈shortSwitches s ∧ Y=C := by
  obtain ⟨key,mark⟩ := mem_filter.mp claim
  by_cases move : Y∈shortSwitches s
  · exact ⟨move,(book.secondary Y move).symm.trans mark⟩
  exact (no ⟨Y,claim,mark ▸ book.primary Y key move cy,cy⟩).elim

/-- The excess charge at a secondary account is bounded by its own literal
class's bill, with every other claimant covered up to one unit. -/
theorem secondary_bill {D V q r C target} (free : QFree D V q) (reg : OutEq r D V)
    {s : Selection D V q r 3 (3*r)} (book : ShellBooking s)
    (room : RoutingRoom q r V.card target) (no : ¬FirstClaim s C) :
    netDebt s C ≤ 1+(if C∈shortSwitches s then (shellDebt D V 3 (3*r) C:ℚ) else 0) := by
  classical
  have hr := room.growth.2.1
  by_cases move : C∈shortSwitches s
  · have cc : C∈claims s C := mem_filter.mpr ⟨(mem_filter.mp move).1,book.secondary C move⟩
    have bound := acyclic_subset_bill free reg (by omega) s room
      (erase_subset C (claims s C)) (by
        intro Y ym
        by_contra cy
        obtain ⟨ne,key⟩ := mem_erase.mp ym
        exact ne (secondary_key book no key cy).2)
    have sum := sum_erase_add (claims s C) (fun Y=>(shellDebt D V 3 (3*r) Y:ℚ)) cc
    rw [ite_eq_left move]
    unfold netDebt
    linarith only [sum,bound]
  · rw [ite_eq_right move,add_zero]
    apply pure_debt free reg (by omega) s _ room
    intro Y mem
    by_contra cy
    obtain ⟨sw,rfl⟩ := secondary_key book no mem cy
    exact move sw

/-- One allocation realizes the paper's switched short classes and its first-layer
charges simultaneously. The bound uses the bill of the actual switched class. -/
theorem booked_secondary_frontier {D V q r target} (free : QFree D V q) (reg : OutEq r D V)
    (s : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target) :
    ∃t : Selection D V q r 3 (3*r),t.rep=s.rep ∧ ShellBooking t ∧
      ∀C,¬FirstClaim t C → netDebt t C≤1+
        (if C∈shortSwitches t then (shellDebt D V 3 (3*r) C:ℚ) else 0) := by
  obtain ⟨t,eq,book⟩ := book_short_shells free reg s room.cycle room.growth.2.1 room.close
  exact ⟨t,eq,book,fun _ none=>secondary_bill free reg book room none⟩

attribute [aesop safe forward (immediate := [free,reg,book,room,no]) (rule_sets := [CHGraphFamilies])] secondary_bill

#print axioms booked_secondary_frontier
#print axioms secondary_key
#print axioms secondary_bill
end LeanCH.BR.LowShellCycleSelection
