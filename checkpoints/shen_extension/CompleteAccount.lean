import checkpoints.shen_extension.CompleteWidthFrontier

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

structure CompleteAccount {D V q r} (t : Selection D V q r 3 (3*r)) (C : Finset ℕ)
    (A : Finset (Finset ℕ)) : Prop where
  width : (exterior D V C).card=r-1
  allHeads : ∀v∈C,exterior D V C⊆outN D V v
  high : ∀v∈C,3*r<(ball D V v 3).card
  direct : A=∅ → ∀k:ℕ,k*(r-q+1)<C.card → (k:ℚ)<netDebt t C
  received : A.Nonempty → (3*(r-1):ℕ)≤netDebt t C+(A.card:ℚ)

theorem complete_account {D V q r δ cap C A target} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap A) (width : (exterior D V C).card=r-1) : CompleteAccount t C A := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have roots K (km : K∈booked t) : ∀x∈K,Rooted D V x K := by
    obtain ⟨Y,yk,rfl⟩ := mem_image.mp km; exact t.rooted _ (t.assigned _ yk)
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Y,yk,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ yk)
  have root := roots C mark.bookedHere
  have ev : exterior D V C⊆V := by
    intro z zm; obtain ⟨_,_,arc⟩ := mem_biUnion.mp (mem_sdiff.mp zm).1; exact outN_subset arc
  have all v (vm : v∈C) : exterior D V C⊆outN D V v := fun _ h=>
    mem_of_mem_erase ((complete_row (root v vm) (reg v ((root v vm).sub vm)) width).symm ▸ h)
  have grow := bank_growth free hq reg ev (card_pos.mp (by omega)) (by omega) ready.cycle.2.1 (by simpa only [width] using ready.score)
  have high v (vm : v∈C) : 3*r<(ball D V v 3).card := by
    have reach := score_from_bank (m:=0) free (root v vm).sub ev (fun x xm=>((root x xm).one x xm).ge) (by omega)
      (by omega) vm (all v vm) (by rw [filter_true_of_mem all]; omega) grow
    exact ready.high.trans_le reach
  refine ⟨width,all,high,?_,?_⟩
  · intro empty k small
    by_contra! low
    have due := mark.due
    rw [empty,sum_empty,add_zero] at due
    have om : omissions D V C r=0 := by simp [omissions,width]
    obtain ⟨v,vm,bound⟩ := booked_small_row free reg t (by omega : r-q+2≤q) scale mark.bookedHere (allowance:=k)
      (due.trans low) (by simpa only [om,pow_zero,Nat.mul_one] using small)
    exact bound.not_gt (high v vm)
  · rintro ⟨Z,zm⟩
    have stock := terminal_stock free (by omega) reg (mark.routed Z zm).2.2.2.2.1 mark.bookedHere roots scale (by omega)
    have bill := stock.trans mark.due
    have lim := sum_le_sum (fun z (h : z∈A)=>(mark.routed z h).2.2.2.1)
    simp only [sum_const,nsmul_eq_mul,mul_one] at lim
    exact bill.trans (add_le_add_right lim _)

attribute [aesop safe forward (immediate := [free,reg,ready,mark,width]) (rule_sets := [CHGraphFamilies])] complete_account
#print axioms complete_account
end LeanCH.BR.LowShellCycleSelection
