import checkpoints.shen_extension.SharedShellSuccessor

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

noncomputable def primaryKeys {D V q r k b} (t : Selection D V q r k b) (C : Finset ℕ) :=
  (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))

/-- Charge the primary representatives' own missing pairs, the acyclic
cohort's own missing pairs, and the remaining class at its actual price. -/
theorem paid_cohorts {D V q r C target allowance} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (medium : ∀Y∈primaryKeys t C,3*r≤(ball D V (t.rep Y) 3).card)
    (covered : (primaryKeys t C).card≤(credits t (primaryKeys t C)).card+allowance) :
    netDebt t C≤(allowance:ℚ)+1+shellDebt D V 3 (3*r) C := by
  classical
  let K := primaryKeys t C
  let J := (claims t C\K).erase C
  have keys : K⊆claims t C := filter_subset _ _
  have other : J⊆claims t C := (erase_subset _ _).trans sdiff_subset
  have apart : Disjoint K J := disjoint_left.mpr (fun _ a b=>(mem_sdiff.mp (mem_of_mem_erase b)).2 a)
  have key Y (ym : Y∈K) := (mem_filter.mp (keys ym)).1
  have individual Y (ym : Y∈K) : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := t.least Y (key Y ym) v vm
    have hi := medium Y ym
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have summed := sum_le_sum individual
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at summed
  have jbill := cohort_unit_bill free reg t ready other (fun Y ym=>by
    by_contra cy
    have mark := (mem_filter.mp (other ym)).2
    have no : Y∉shortSwitches t := fun sw=>(mem_erase.mp ym).1 ((policy.secondary Y sw).symm.trans mark)
    exact (mem_sdiff.mp (mem_of_mem_erase ym)).2
      (mem_filter.mpr ⟨other ym,mark ▸ policy.primary Y (mem_filter.mp (other ym)).1 no cy⟩))
  have bill := split_bill t keys other apart (summed.trans covered) jbill
  have rest : claims t C\(K∪J)⊆{C} := by
    intro Y ym
    obtain ⟨owner,off⟩ := mem_sdiff.mp ym
    apply mem_singleton.mpr
    by_contra ne
    exact off (mem_union_right _ (mem_erase.mpr ⟨ne,mem_sdiff.mpr ⟨owner,fun k=>off (mem_union_left _ k)⟩⟩))
  have lastNat : (∑Y∈claims t C\(K∪J),shellDebt D V 3 (3*r) Y)≤shellDebt D V 3 (3*r) C :=
    (sum_le_sum_of_subset rest).trans (by simp)
  have lastQ : (∑Y∈claims t C\(K∪J),(shellDebt D V 3 (3*r) Y:ℚ))≤shellDebt D V 3 (3*r) C := by exact_mod_cast lastNat
  push_cast at bill
  linarith

/-- A direct account whose stock exceeds the price of its own class plus
the two remaining unit bills must have an actual directed contact. -/
theorem actual_primary_contact {D V q r C target δ cap} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap ∅) (account : CompleteAccount t C ∅)
    (next : ∀e∈exterior D V C,Rooted D V e (exterior D V C))
    (medium : ∀Y∈primaryKeys t C,3*r≤(ball D V (t.rep Y) 3).card)
    (sparse : r-q+1<r-1) (enough : 2+shellDebt D V 3 (3*r) C<C.card) :
    ∃Y∈primaryKeys t C,∃Z∈primaryKeys t C,t.rep Y≠t.rep Z ∧ t.rep Z∈ball D V (t.rep Y) 3 := by
  classical
  let K := primaryKeys t C
  let U := K.image t.rep
  have keys : K⊆claims t C := filter_subset _ _
  have key Y (ym : Y∈K) := (mem_filter.mp (keys ym)).1
  have sub : U⊆V := by intro u um; obtain ⟨Y,y,rfl⟩ := mem_image.mp um; exact rep_native t (key Y y)
  have size : U.card=K.card := card_image_of_injOn (fun Y ym Z zm eq=>
    (rep_key t (key Y ym)).symm.trans ((congrArg (N2 D V) eq).trans (rep_key t (key Z zm))))
  have hq := ready.cycle.1
  have loss H (hm : H∈booked t) : omissions D V H r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp hm; exact t.loss _ (t.assigned _ ym)
  have exactStock := exclusive_stock free (by omega) reg t mark.bookedHere account.width
    (fun z zm=>((next z zm).one z zm).le) loss sparse
  have per c (cm : c∈C) : (1:ℚ)≤surplus (3*r) (ball D V c 3).card := by
    have hi := account.high c cm
    have unit : 1≤surplus (3*r) (ball D V c 3).card := by simp [surplus,hi]; omega
    exact_mod_cast unit
  have stock := sum_le_sum per
  simp only [sum_const,nsmul_eq_mul,mul_one] at stock
  have due := mark.due
  rw [sum_empty,add_zero,exactStock] at due
  have enoughQ : (2:ℚ)+(shellDebt D V 3 (3*r) C:ℚ)<C.card := by exact_mod_cast enough
  have live : (contacts D V U 3).Nonempty := by
    by_contra! empty
    have pairBound := holes_of_contacts (D:=D) (k:=3) sub
    change U.offDiag.card≤(credits t K).card+2*(contacts D V U 3).card at pairBound
    rw [empty,card_empty,offDiag_card] at pairBound
    have amort : K.card≤(credits t K).card+1 := by
      by_cases few : U.card≤1
      · omega
      have := Nat.mul_le_mul_left U.card (show 2≤U.card by omega)
      omega
    have bound := paid_cohorts free reg t policy ready medium amort
    norm_num at bound
    linarith only [stock,due,enoughQ,bound]
  obtain ⟨⟨u,v⟩,edge⟩ := live
  obtain ⟨pair,hit⟩ := mem_filter.mp edge
  obtain ⟨um,vm,ne⟩ := mem_offDiag.mp pair
  obtain ⟨Y,y,rfl⟩ := mem_image.mp um
  obtain ⟨Z,z,rfl⟩ := mem_image.mp vm
  exact ⟨Y,y,Z,z,ne,hit⟩

attribute [aesop safe forward (immediate := [free,reg,policy,ready,medium,covered]) (rule_sets := [CHGraphFamilies])] paid_cohorts
attribute [aesop safe forward (immediate := [free,reg,policy,ready,mark,account,next,medium,sparse,enough]) (rule_sets := [CHGraphFamilies])] actual_primary_contact
#print axioms paid_cohorts
#print axioms actual_primary_contact
end LeanCH.BR.LowShellCycleSelection
