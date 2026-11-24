import checkpoints.shen_extension.SharedExceptionGuard

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- A guarded secondary claimant rules out the only two-primary contact
that could raise the combined bill. The common ball comparison uses both
origins of the physical contact supplied by the account. -/
theorem one_omission_total {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (policy : ShellBooking t) (off : C∉shortSwitches t)
    (width : (exterior D V C).card=r) (size : C.card+1=r)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card) :
    netDebt t C≤2 := by
  classical
  obtain ⟨_,low|high⟩ := mixed_contact_bill free reg t ready policy off width.ge size.ge medium
  · exact low
  obtain ⟨_,a,am,b,bm,ne,privateB,same,Z,zm,dag⟩ := high
  obtain ⟨d,de,_,sealed,guard⟩ := guarded_exception free reg t ready (mem_sdiff.mp zm).1 dag size width
  let U := ((claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))).image t.rep
  have info v (vm : v∈U) : v∈V ∧ C⊆outN D V v ∧ (outN D V v\C).card≤1 ∧
      (N2 D V v).card≤r ∧ (ball D V v 3).card=3*r := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp vm
    obtain ⟨ycl,first⟩ := mem_filter.mp ym
    have key := (mem_filter.mp ycl).1
    have uv := rep_native t key
    have debt := (mem_filter.mp (mem_filter.mp (t.represents _ key)).1).2
    have med := medium Y ycl first
    have ⟨hq,a,b,c,d,_⟩ := ready.cycle
    have bound := low_third_second free hq reg uv a b c d debt
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at one
    have two := @card_B2 D V (t.rep Y)
    change (ball D V (t.rep Y) 2).card≤2*r+1 at bound
    have rest := card_sdiff_of_subset first
    rw [reg _ uv] at rest
    exact ⟨uv,first,by omega,by omega,le_antisymm debt med⟩
  have ⟨av,first,slots,_,eqA⟩ := info a am
  have ⟨bv,also,other,b2,eqB⟩ := info b bm
  have hq := ready.cycle.1
  have less := contact_through_exception free (by omega) reg av bv first also privateB same slots other b2 de
    sealed guard (by decide : 2≤3) (by omega)
  omega

/-- A mixed primary/acyclic-secondary cycle with one exterior omission
cannot carry the outstanding debt when the complete rows clear the indicated
score. A short primary is the only remaining possibility in that mixed case. -/
theorem mixed_medium_paid {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (policy : ShellBooking t) (width : (exterior D V C).card=r) (size : C.card+1=r)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card)
    {Z} (zm : Z∈claims t C) (dag : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)
    (score : 3*r+2≤4+target) (enough : 4*(r-q+1)<3*(C.card-(r-q))) :
    netDebt t C<rowStock t (booked t) C := by
  classical
  have key := (mem_filter.mp zm).1
  have id := (mem_filter.mp zm).2
  have cm : C∈booked t := id ▸ mem_image_of_mem t.pay key
  have hr := ready.growth.2.1
  have hq := ready.cycle.1
  have fit := ready.close
  have off : C∉shortSwitches t := by
    intro sw
    have := (switched_shell_paid free reg t (by omega) hr fit sw).1.width
    omega
  have small := one_omission_total free reg t ready policy off width size medium
  obtain ⟨_,_,_,count,_⟩ := claim_data free reg (by omega) t key ready.cycle dag ready.close ready.space ready.distance ready.score
  rw [id,show r-C.card=1 by omega,Nat.one_mul] at count
  let G := C.filter (fun v=>4+target≤(ball D V v 3).card)
  have per v (vm : v∈G) : 3≤surplus (3*r) (ball D V v 3).card := by
    have grow := (mem_filter.mp vm).2
    have high : 3*r<(ball D V v 3).card := by omega
    simp only [surplus,ite_eq_left high]; omega
  have tally := sum_le_sum per
  simp only [sum_const_nat (fun _ _=>rfl)] at tally
  have total : ∑v∈G,surplus (3*r) (ball D V v 3).card ≤ ∑v∈C,surplus (3*r) (ball D V v 3).card :=
    sum_le_sum_of_subset (filter_subset _ _)
  by_contra! due
  have original := le_sub_iff_add_le.mp due
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ ym)
  have bill := shortfall_of_bill free reg (by omega : r-q+2≤q) t scale cm (by rw [add_comm]; exact original)
  have loss : omissions D V C r=1 := by unfold omissions; rw [width]; omega
  have charges : ∑Y∈claims t C,shellDebt D V 3 (3*r) Y≤(receipts t C).card+2 := by
    have rat := sub_le_iff_le_add.mp small
    rw [add_comm] at rat
    exact_mod_cast rat
  have mult := Nat.mul_le_mul_right ((r-q+1)*2^1) charges
  rw [Nat.add_mul (receipts t C).card 2] at mult
  rw [loss] at bill
  simp only [pow_one] at mult bill
  change C.card≤G.card+(r-q) at count
  revert enough
  omega

#print axioms one_omission_total
#print axioms mixed_medium_paid
end LeanCH.BR.LowShellCycleSelection
