import checkpoints.shen_extension.PartialRouteSupply

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

structure RemainingPayer {D V q r} (t : Selection D V q r 3 (3*r)) (C : Finset ℕ)
    (δ cap : ℕ) (A : Finset (Finset ℕ)) : Prop where
  first : FirstClaim t C
  excluded : ¬SplitAccount t C
  bookedHere : C∈booked t
  bounded : A.card≤cap
  routed : ∀Z∈A,Z∈booked t ∧ (¬FirstClaim t Z ∨ SplitAccount t Z) ∧
    rowStock t (booked t) Z≤netDebt t Z ∧ netDebt t Z-localCredit t Z≤1 ∧
    StrongTerminal D V r C ∧ WeakArrival D V r δ (fullRowFloor q r) 1 Z C
  due : rowStock t (booked t) C≤netDebt t C+∑Z∈A,(netDebt t Z-localCredit t Z)

/-- Debit each mixed source and its stock together, then route all outstanding accounts in one allocation. -/
theorem remaining_after_partial_routes {D V q r target g mid top cap} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t)
    (room : PrimaryRoom q r V.card target g mid top cap) (reserve : cap+5<3*(r-1))
    (afford : 4*(r-q+1)<3*fullRowFloor q r) :
    ∃C A,RemainingPayer t C (V.card-((r-1)+top)) cap A := by
  classical
  let F := booked t
  let δ := V.card-((r-1)+top)
  let debt := netDebt t
  let stock := rowStock t
  let priority := fun C=>FirstClaim t C ∧ ¬SplitAccount t C
  let pay := fun a=>debt a-localCredit t a
  let available := fun S a=>stock S a-localCredit t a
  let P := F.filter (fun a=>¬priority a ∧ ¬StrongTerminal D V r a ∧ stock F a≤debt a)
  have supply a (am : a∈P) := adjusted_route free reg t policy room afford
    (mem_filter.mp am).1 (mem_filter.mp am).2.1 (mem_filter.mp am).2.2.2
  let targetOf a := if h:a∈P then (supply a h).2.choose else a
  let K := P.image targetOf
  have route a (am : a∈P) : StrongTerminal D V r (targetOf a) ∧
      WeakArrival D V r δ (fullRowFloor q r) 1 a (targetOf a) := by
    simpa only [targetOf,dite_eq_left am] using (supply a am).2.choose_spec
  have hq := room.route.cycle.1
  have hr := room.route.growth.2.1
  have slack : r-q+1<r-1 := by have := room.route.close; omega
  have low u (um : u∈V) : 3*r≤(ball D V u 3).card+1 := by
    have := ShellBankOrders.mixed_third free room.route.growth reg um; omega
  have rooted C (cm : C∈F) : ∀v∈C,Rooted D V v C := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact t.rooted _ (t.assigned _ ym)
  have om C (cm : C∈F) : omissions D V C r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact t.loss _ (t.assigned _ ym)
  have rootAll (S : Finset (Finset ℕ)) (ss : ∀z∈S,StrongTerminal D V r z) C (cm : C∈F∪S) :
      ∀v∈C,Rooted D V v C := by
    rcases mem_union.mp cm with a|b
    · exact rooted _ a
    · exact (ss _ b).rooted
  have fixed (S : Finset (Finset ℕ)) (ss : ∀z∈S,StrongTerminal D V r z) C (cm : C∈F) :
      stock (F∪S) C=stock F C :=
    sum_congr rfl (fun v vm=>shares_unchanged free (by omega) reg ss rooted om slack _ cm vm)
  have liveF : F.Nonempty := by
    obtain ⟨C,cm,_⟩ := unpaid_cycle free (by omega) reg (by omega) low room.route.small live t
    exact ⟨C,cm⟩
  have adjusted (S : Finset (Finset ℕ)) (ss : ∀z∈S,StrongTerminal D V r z) :
      ∑a∈F∪S,available (F∪S) a≤∑a∈F,pay a := by
    have all := no_global_surplus t free (by omega) reg (by omega) low room.route.small (rootAll S ss)
    have equal : ∑a∈F∪S,localCredit t a=∑a∈F,localCredit t a := by
      symm
      apply sum_subset subset_union_left
      intro a _ off
      have empty : ¬SplitAccount t a := fun h=>off h.bookedHere
      simp [localCredit,empty]
    simpa only [available,pay,sum_sub_distrib,equal] using
      (show ∑a∈F∪S,stock (F∪S) a-∑a∈F,localCredit t a≤∑a∈F,debt a-∑a∈F,localCredit t a from sub_le_sub_right all _)
  have fin := routed_balance F liveF pay available priority (StrongTerminal D V r) targetOf
    (fun a af n h b=>(route a (mem_filter.mpr ⟨af,n,h,(sub_le_sub_iff_right _).mp b⟩)).1)
    adjusted (fun S ss a am=>congrArg (fun v : ℚ=>v-localCredit t a) (fixed S ss a am))
    (by
      intro S ss a am
      apply sub_nonneg.mpr
      by_cases af : a∈F
      · rw [fixed S ss a af]
        exact credit_affordable free reg t room.route
      have empty : ¬SplitAccount t a := fun h=>af h.bookedHere
      rw [localCredit,ite_eq_right empty]
      exact sum_nonneg (fun v _=>by dsimp [share]; positivity))
  dsimp only at fin
  simp only [available,pay,sub_le_sub_iff_right] at fin
  obtain ⟨C,cu,poss,raw⟩ := fin
  let A := P.filter (fun a=>targetOf a=C)
  change stock (F∪K) C-localCredit t C ≤ (if C∈F then debt C-localCredit t C else 0)+∑Z∈A,pay Z at raw
  have bill : stock (F∪K) C≤(if C∈F then debt C else 0)+∑Z∈A,pay Z := by
    by_cases cf : C∈F
    · simp only [ite_eq_left cf] at raw ⊢; linarith
    have empty : ¬SplitAccount t C := fun h=>cf h.bookedHere
    simpa only [ite_eq_right cf,localCredit,ite_eq_right empty,sub_zero] using raw
  have ss z (zm : z∈K) : StrongTerminal D V r z := by
    obtain ⟨a,am,rfl⟩ := mem_image.mp zm; exact (route a am).1
  have actual a (am : a∈A) :
      StrongTerminal D V r C ∧ WeakArrival D V r δ (fullRowFloor q r) 1 a C :=
    (mem_filter.mp am).2 ▸ route a (mem_filter.mp am).1
  obtain ⟨_,_,_,_,two,entry,sparse⟩ := room.transfer
  have size := arrivals_bound free (by omega) reg (by omega) sparse two entry (fun a (am : a∈A)=>(actual a am).2)
  have limited : A.card≤cap := by
    by_contra! too
    have lim := room.crowd
    have := Nat.mul_le_mul_right (fullRowFloor q r) (show cap+1≤A.card by omega)
    omega
  have sumCost : (∑Z∈A,pay Z)≤(cap:ℚ) := by
    have s := sum_le_sum (fun a (am : a∈A)=>(supply a (mem_filter.mp am).1).1)
    simp only [sum_const,nsmul_eq_mul,mul_one] at s
    exact s.trans (by exact_mod_cast limited)
  have omAll z (zm : z∈F∪K) : omissions D V z r≤r-q := by
    rcases mem_union.mp zm with old|added
    · exact om _ old
    · simp [omissions,(ss _ added).nextSize]
  have enough (term : StrongTerminal D V r C) : (cap:ℚ)+5<stock (F∪K) C :=
    (show (cap:ℚ)+5<((3*(r-1):ℕ):ℚ) by exact_mod_cast reserve).trans_le
      (terminal_stock free (by omega) reg term (mem_sdiff.mp cu).1 (rootAll K ss) omAll slack)
  have cf : C∈F := by
    by_contra off
    have term := ss _ (poss.resolve_left (fun h=>off h.1))
    rw [ite_eq_right off,zero_add] at bill
    linarith only [enough term,bill,sumCost]
  rw [ite_eq_left cf,fixed K ss C cf] at bill
  have retained : priority C := by
    by_contra none
    have term : StrongTerminal D V r C := by
      rcases poss with left|right
      · exact left.2.resolve_left none
      · exact ss _ right
    have debtCap : debt C≤5 := by
      have notSplit : ¬SplitAccount t C := by
        intro h
        have := term.nextSize
        have := h.width
        omega
      have noFirst : ¬FirstClaim t C := fun h=>none ⟨h,notSplit⟩
      have bound := secondary_bill free reg policy room.route noFirst
      have unit : shellDebt D V 3 (3*r) C≤4 := by
        apply (class_residual (m:=3) _).trans (by decide)
        intro v _; unfold debit; split_ifs <;> omega
      have cast : (shellDebt D V 3 (3*r) C:ℚ)≤4 := by exact_mod_cast unit
      change netDebt t C≤5
      split_ifs at bound <;> linarith
    have exc := enough term
    rw [fixed K ss C cf] at exc
    linarith only [exc,bill,sumCost,debtCap]
  refine ⟨C,A,retained.1,retained.2,cf,limited,?_,bill⟩
  intro Z zm
  have zp := (mem_filter.mp zm).1
  obtain ⟨zf,f,_w,b⟩ := mem_filter.mp zp
  exact ⟨zf,by by_cases h : FirstClaim t Z; exact .inr (Classical.byContradiction (fun no=>f ⟨h,no⟩)); exact .inl h,b,(supply Z zp).1,actual Z zm⟩

#print axioms remaining_after_partial_routes
end LeanCH.BR.LowShellCycleSelection
