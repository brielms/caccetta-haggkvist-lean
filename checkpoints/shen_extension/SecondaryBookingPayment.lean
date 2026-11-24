import checkpoints.shen_extension.SecondaryBookingBill

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Exclusive physical stock pays a secondary account including its other
claimants. Compare demand directly with the number of high physical rows. -/
theorem exclusive_secondary_paid {D V q r C target} (free : QFree D V q) (reg : OutEq r D V)
    {s : Selection D V q r 3 (3*r)} (policy : ShellBooking s) (room : RoutingRoom q r V.card target)
    (cm : C∈booked s) (no : ¬FirstClaim s C) (bank : CompletePayer D V r 1 C)
    (needed : 1+(if C∈shortSwitches s then shellDebt D V 3 (3*r) C else 0)<C.card) :
    netDebt s C<rowStock s (booked s) C := by
  classical
  have hq := room.cycle.1
  have hr := room.growth.2.1
  have fit := room.close
  obtain ⟨Y,ym,ey⟩ := mem_image.mp cm
  have len := s.length _ (s.assigned _ ym)
  rw [ey] at len
  let E := exterior D V C
  have ev : E⊆V := by
    intro x xm
    obtain ⟨z,_,arc⟩ := mem_biUnion.mp (mem_sdiff.mp xm).1
    exact outN_subset arc
  have width : E.card=r-1 := bank.width
  have all v (vm : v∈C) : E⊆outN D V v := by
    intro z zm
    exact mem_of_mem_erase ((complete_row (bank.rooted v vm) (reg v ((bank.rooted v vm).sub vm)) bank.width).symm ▸ (show z∈exterior D V C from zm))
  have grow := bank_growth free hq reg ev (card_pos.mp (by omega : 0<E.card))
    (by omega : E.card≤2*q) room.cycle.2.1 (by simpa only [width] using room.score)
  have per v (vm : v∈C) : 1≤surplus (3*r) (ball D V v 3).card := by
    have bound := score_from_bank (m:=0) free (bank.rooted v vm).sub ev (fun x xm=>((bank.rooted x xm).one x xm).ge)
      (by omega) (by omega) vm (all v vm) (by rw [filter_true_of_mem all]; omega) grow
    have high := room.high.trans_le bound
    simp only [surplus,ite_eq_left high]; omega
  have stock := sum_le_sum per
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at stock
  have bounded K (km : K∈booked s) : omissions D V K r≤r-q := by
    obtain ⟨Z,zm,rfl⟩ := mem_image.mp km
    exact s.loss _ (s.assigned _ zm)
  rw [exclusive_stock free (by omega) reg s cm bank.width bank.sparse bounded (by omega)]
  have bound : (C.card:ℚ)≤∑v∈C,(surplus (3*r) (ball D V v 3).card:ℚ) := by exact_mod_cast stock
  refine (secondary_bill free reg policy room no).trans_lt (lt_of_lt_of_le ?_ bound)
  split_ifs at needed ⊢ <;> exact_mod_cast needed

/-- Every materialized switched cycle with no first-layer claimant is
strictly paid, also counting the unmoved classes on that cycle. -/
theorem switched_secondary_paid {D V q r C target} (free : QFree D V q) (reg : OutEq r D V)
    {s : Selection D V q r 3 (3*r)} (policy : ShellBooking s) (room : RoutingRoom q r V.card target)
    (move : C∈shortSwitches s) (no : ¬FirstClaim s C) : netDebt s C<rowStock s (booked s) C := by
  have hq := room.cycle.1
  have hr := room.growth.2.1
  have key := (mem_filter.mp move).1
  have eq := policy.secondary C move
  have len := s.length _ (s.assigned C key)
  rw [eq] at len
  have bookedC : C∈booked s := eq ▸ mem_image_of_mem s.pay key
  have physical := (switched_shell_paid free reg s (by omega) hr room.close move).1
  apply exclusive_secondary_paid free reg policy room bookedC no physical
  have owe : shellDebt D V 3 (3*r) C≤4 := by
    apply (class_residual (m:=3) _).trans (by decide)
    intro v _; unfold debit; split_ifs <;> omega
  rw [ite_eq_left move]; omega

attribute [aesop safe forward (immediate := [free,reg,policy,room,move,no]) (rule_sets := [CHGraphFamilies])] switched_secondary_paid
#print axioms exclusive_secondary_paid
#print axioms switched_secondary_paid
end LeanCH.BR.LowShellCycleSelection
