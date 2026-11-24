import checkpoints.shen_extension.SecondaryBookingPayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Routing reads a cycle's actual class list. All other booked cycles and
their class choices can be arbitrary. -/
theorem route_pure_account {D V q r target g mid top C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (move : TransferRoom q r V.card g mid top) (cm : C∈booked t) (bill : shortfall t C (r-q))
    (cy : ∀Y∈claims t C,QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card) :
    (∑Y∈claims t C,shellDebt D V 3 (3*r) Y)≤1 ∧
    ∃T,StrongTerminal D V r T ∧ WeakArrival D V r (V.card-((r-1)+top)) (fullRowFloor q r) 1 C T := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  obtain ⟨positive,score,grow,again,_⟩ := move
  obtain ⟨Y,only,yc,om,_,tiers⟩ := unpaid_acyclic free reg (by omega) t cm bill cy ready.cycle ready.close
    ready.space ready.distance ready.score ready.high
  have yk : Y∈claims t C := only.symm ▸ mem_singleton_self Y
  have dag := cy Y yk
  have mul := Nat.mul_le_mul_left (r-q+1) (Nat.pow_le_pow_right (n:=2) (by decide) om)
  have cap : (r-q+1)*2^(omissions D V C r)≤2*(r-q+1) := by simpa [Nat.mul_comm] using mul
  have bounds := tiers.trans cap
  rw [←yc] at bounds
  have result := weak_row_chain free reg (by omega) t (mem_filter.mp yk).1 dag ready.cycle ready.close
    ready.space ready.distance ready.score ready.high ready.squeeze ready.finite (2*(r-q+1)) bounds ready.margin
  rw [yc] at result
  have unit := (acyclic_class_debit free reg (by omega) t (mem_filter.mp yk).1 ready.cycle dag
    (by have := ready.close; have := ready.space; omega) ready.distance).2
  exact ⟨by simpa [only] using unit,routed_arrival free reg t ready cm bill ⟨Y,only,dag,yc,om,result⟩ positive score grow again⟩

/-- Every unpaid cycle without a first claimant on the rebooked graph
has a unit-bounded debt and a physical route to a strong terminal. -/
theorem booked_secondary_route {D V q r target g mid top C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (move : TransferRoom q r V.card g mid top) (cm : C∈booked t) (none : ¬FirstClaim t C)
    (due : rowStock t (booked t) C≤netDebt t C) :
    netDebt t C≤1 ∧ ∃T,StrongTerminal D V r T ∧
      WeakArrival D V r (V.card-((r-1)+top)) (fullRowFloor q r) 1 C T := by
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have off : C∉shortSwitches t := fun sw=>(not_lt_of_ge due) (switched_secondary_paid free reg policy ready sw none)
  have cy Y (ym : Y∈claims t C) : QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card := by
    by_contra bad
    obtain ⟨sw,rfl⟩ := secondary_key policy none ym bad
    exact off sw
  have paid := le_sub_iff_add_le.mp due
  have bill := shortfall_of_bill free reg (by have := ready.close; omega : r-q+2≤q)
    t (fun K km=>by obtain ⟨Y,ym,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ ym)) cm
    (by rw [add_comm]; exact paid)
  exact ⟨pure_debt free reg (by omega) t cy ready,(route_pure_account free reg t ready move cm bill cy).2⟩

#print axioms route_pure_account
#print axioms booked_secondary_route
end LeanCH.BR.LowShellCycleSelection
