import checkpoints.shen_extension.TransferFamilyEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- The labels and scores defining the class of mixed accounts from which
one unit can be deducted on both sides of the global balance. -/
structure SplitAccount {D V q r} (t : Selection D V q r 3 (3*r)) (C : Finset ℕ) : Prop where
  bookedHere : C∈booked t
  width : (exterior D V C).card=r
  size : C.card+1=r
  enough : 2*(r-q+1)<C.card
  second : ∃Y∈claims t C,QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card
  medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card

noncomputable def localCredit {D V q r} (t : Selection D V q r 3 (3*r)) (C : Finset ℕ) : ℚ := by
  classical exact if SplitAccount t C then 1 else 0

theorem credit_affordable {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target) :
    localCredit t C≤rowStock t (booked t) C := by
  classical
  unfold localCredit; split_ifs with h
  · obtain ⟨Y,ym,dag⟩ := h.second
    exact (stock_after_secondary free reg t room ym dag h.size h.width h.enough room.margin).le
  exact sum_nonneg (fun _ _=>by dsimp [share]; positivity)

theorem adjusted_route {D V q r target g mid top cap C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (room : PrimaryRoom q r V.card target g mid top cap)
    (afford : 4*(r-q+1)<3*fullRowFloor q r) (cm : C∈booked t)
    (un : ¬(FirstClaim t C ∧ ¬SplitAccount t C)) (due : rowStock t (booked t) C≤netDebt t C) :
    netDebt t C-localCredit t C≤1 ∧ ∃T,StrongTerminal D V r T ∧
      WeakArrival D V r (V.card-((r-1)+top)) (fullRowFloor q r) 1 C T := by
  classical
  by_cases split : SplitAccount t C
  · obtain ⟨Y,ym,dag⟩ := split.second
    have hq := room.route.cycle.1
    have hr := room.route.growth.2.1
    have fit := room.route.close
    have off : C∉shortSwitches t := by
      intro sw
      have := (switched_shell_paid free reg t (by omega) hr fit sw).1.width
      have := split.width
      omega
    have small := one_omission_total free reg t room.route policy off split.width split.size split.medium
    have low : rowStock t (booked t) C≤(2:ℕ) := by simpa using due.trans small
    have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
      obtain ⟨Z,zm,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ zm)
    have om : omissions D V C r=1 := by unfold omissions; rw [split.width]; omega
    have bound := booked_score_cap free reg (by omega : r-q+2≤q) t scale cm low
    simp only [om,pow_one] at bound
    have tiers := tier_stock D V C 3 (3*r)
    refine ⟨by rw [localCredit,ite_eq_left split]; linarith,?_⟩
    exact itemized_route free reg t room.route ym dag om (budget:=4*(r-q+1)) (by omega) afford
      room.transfer.2.1 room.transfer.2.2.1 room.transfer.2.2.2.1
  · rw [localCredit,ite_eq_right split,sub_zero]
    exact booked_secondary_route free reg t policy room.route room.transfer cm (fun h=>un ⟨h,split⟩) due

#print axioms credit_affordable
#print axioms adjusted_route
end LeanCH.BR.LowShellCycleSelection
