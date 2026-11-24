import checkpoints.shen_extension.CyclePaymentSchedule
import checkpoints.shen_extension.GuardedProfileBudget

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock BypassRepair

/-- A measured floor names the actual graph, carrier, radius and score.
Any source of such a floor can pay this part of a cycle ledger. -/
structure MeasuredFloor (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) : Prop where
  every : ∀v∈V,b≤(ball D V v k).card+1

theorem floor_from_profiles {D V q r lo h b K} (free : QFree D V q) (reg : OutEq r D V)
    (start : ∀v∈V,lo≤(ball D V v 2).card) (known : ∀t∈K,NoHost q t)
    (cover : GuardedProfileBudget.Covers q r lo h K) (target : b≤h+1) :
    MeasuredFloor D V 3 b := by
  constructor
  intro v vm
  exact target.trans (Nat.add_le_add_right (GuardedProfileBudget.third free reg vm (start v vm) known cover) 1)

theorem measured_schedule_exit {D V q r k b} {sel : Selection D V q r k b}
    (free : QFree D V q) (reg : OutEq r D V) (hq : 2≤q) (time : k+k≤q)
    (floor : MeasuredFloor D V k b) (size : V.card≤2*b) (paid : Nonempty (FundedSchedule sel)) : False :=
  schedule_exit sel free hq reg time floor.every size paid

/-- The ledger names a physical unpaid cycle even if the measured floor
came from a different set of lower-degree theorems. -/
theorem measured_unpaid {D V q r k b} (sel : Selection D V q r k b)
    (free : QFree D V q) (reg : OutEq r D V) (hq : 2≤q) (time : k+k≤q)
    (floor : MeasuredFloor D V k b) (size : V.card≤2*b) (live : V.Nonempty) :
    ∃C∈booked sel,rowStock sel (booked sel) C≤netDebt sel C := by
  classical
  obtain ⟨C,cm,bill⟩ := unpaid_cycle free hq reg time floor.every size live sel
  exact ⟨C,cm,le_sub_iff_add_le.mpr (by simpa only [rowStock,add_comm] using bill)⟩

attribute [aesop safe forward (immediate := [free,reg,start,known,cover,target]) (rule_sets := [CHGraphFamilies])] floor_from_profiles
attribute [aesop safe forward (immediate := [free,reg,hq,time,floor,size,paid]) (rule_sets := [CHGraphFamilies])] measured_schedule_exit
attribute [aesop safe forward (immediate := [sel,free,reg,hq,time,floor,size,live]) (rule_sets := [CHGraphFamilies])] measured_unpaid

/-- The constant in this older arithmetic supplier is an effective
degree ceiling. The local ball and schedule theorems above are independent of it. -/
theorem mixed_degree_ceiling {q r} (room : ShellBankOrders.MixedRoom q r) : r≤8 := by
  obtain ⟨_,pos,_,_,_,_,cap⟩ := room
  by_contra! high
  nlinarith [Nat.mul_le_mul_left r high]

#print axioms floor_from_profiles
#print axioms measured_unpaid
#print axioms measured_schedule_exit
#print axioms mixed_degree_ceiling
end LeanCH.BR.LowShellCycleSelection
