import checkpoints.shen_extension.GlobalCycleDeficit

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- All distinct representatives are incomparable when their common cycle
exterior strictly exceeds their second shells and each has one spare slot. -/
theorem complete_receipts {D V q r k b C} (free : QFree D V q) (hq : 4≤q)
    (sel : Selection D V q r k b) (time : k+1≤q)
    (first : ∀u∈representatives sel C,C⊆outN D V u)
    (slots : ∀u∈representatives sel C,(outN D V u\C).card≤1)
    (wide : ∀u∈representatives sel C,(N2 D V u).card<(exterior D V C).card) :
    receipts sel C=(representatives sel C).offDiag := by
  apply Finset.Subset.antisymm inter_subset_left
  intro p pm
  obtain ⟨um,vm,ne⟩ := mem_offDiag.mp pm
  have native u (h : u∈representatives sel C) : u∈V := by
    obtain ⟨Y,y,rfl⟩ := mem_image.mp h
    exact rep_native sel (mem_filter.mp y).1
  have miss {u v} (um : u∈representatives sel C) (vm : v∈representatives sel C) (ne : u≠v) :
      v∉ball D V u k := by
    intro hit
    have same := (single_slot_collision free hq (native _ um) ne (first _ um) (first _ vm)
      (slots _ um) (wide _ um).le time hit).2
    exact (wide _ um).ne (congrArg card same)
  exact mem_inter.mpr ⟨pm,mem_filter.mpr ⟨mem_offDiag.mpr ⟨native _ um,native _ vm,ne⟩,
    miss um vm ne,miss vm um ne.symm⟩⟩

/-- The guard and the booking rule supply every hypothesis of the pair
count on the very cycle bearing the deficit. -/
theorem wide_receipts {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) (wide : r<(exterior D V C).card) :
    receipts sel C=(representatives sel C).offDiag := by
  obtain ⟨_,_,primary,_⟩ := short
  have hr := ready.growth.2.1
  obtain ⟨hq,a,b,c,d,_⟩ := ready.cycle
  have atRow u (h : u∈representatives sel C) :
      C⊆outN D V u ∧ (outN D V u\C).card≤1 ∧ (N2 D V u).card≤r := by
    obtain ⟨Y,y,rfl⟩ := mem_image.mp h
    obtain ⟨ym,yc⟩ := mem_filter.mp y
    have uv := rep_native sel ym
    have low := (mem_filter.mp (mem_filter.mp (sel.represents Y ym)).1).2
    have seq := low_third_second free hq reg uv a b c d low
    have start := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at start
    have next := @card_B2 D V (sel.rep Y)
    have inside := primary Y y (by
      intro dag
      have data := claim_data free reg (by omega) sel ym ready.cycle dag ready.close ready.space ready.distance ready.score
      have bound := data.loss
      rw [yc] at bound
      unfold omissions at bound
      omega)
    have cc := sel.length _ (sel.assigned Y ym)
    rw [yc] at cc
    have size := card_sdiff_of_subset inside
    rw [reg _ uv] at size
    have fit := ready.close
    change (ball D V (sel.rep Y) 2).card≤2*r+1 at seq
    exact ⟨inside,by omega,by omega⟩
  exact complete_receipts free (by omega) sel (by omega) (fun u h=>(atRow u h).1)
    (fun u h=>(atRow u h).2.1) (fun u h=>(atRow u h).2.2.trans_lt wide)

/-- In the wide-exterior leaf the only remaining escapes are a genuinely
short source, or a low score on that physical cycle. -/
theorem wide_price {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) (wide : r<(exterior D V C).card) :
    (∃Y∈claims sel C,(ball D V (sel.rep Y) 3).card<3*r) ∨
    (C.filter (fun v=>3*r<(ball D V v 3).card)).card+
    2*(C.filter (fun v=>3*r+1<(ball D V v 3).card)).card ≤ (r-q+1)*2^(omissions D V C r) := by
  classical
  by_cases anyShort : ∃Y∈claims sel C,(ball D V (sel.rep Y) 3).card<3*r
  · exact Or.inl anyShort
  right
  have all := wide_receipts free reg short ready wide
  obtain ⟨cm,_,_,price⟩ := short
  have nt : ¬StrongTerminal D V r C := fun h=> by have := h.nextSize; omega
  simp only [ite_eq_right nt,add_zero] at price
  have unit Y (ym : Y∈claims sel C) : shellDebt D V 3 (3*r) Y≤1 := by
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := sel.least Y (mem_filter.mp ym).1 v vm
    have high : 3*r≤(ball D V (sel.rep Y) 3).card := Nat.le_of_not_gt (fun h=>anyShort ⟨Y,ym,h⟩)
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have count := sum_le_sum (s:=claims sel C) unit
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at count
  have square : (claims sel C).card≤(receipts sel C).card+1 := by
    rw [all,offDiag_card,representatives_card]
    by_cases little : (claims sel C).card≤1
    · omega
    have := Nat.mul_le_mul_left (claims sel C).card (show 2≤(claims sel C).card by omega)
    omega
  have total := count.trans square
  have original : (↑(receipts sel C).card:ℚ)+rowStock sel (booked sel) C≤
      ∑Y∈claims sel C,(shellDebt D V 3 (3*r) Y:ℚ) := by
    change _≤ _ - _ at price
    linarith only [price]
  have scale C (cm : C∈booked sel) : omissions D V C r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact sel.loss _ (sel.assigned _ ym)
  have hq := ready.cycle.1
  have fit := ready.close
  have bill := shortfall_of_bill free reg (by omega : r-q+2≤q) sel scale cm original
  let cost := (r-q+1)*2^(omissions D V C r)
  have mult := Nat.mul_le_mul_right cost total
  rw [Nat.add_mul,Nat.one_mul] at mult
  change (receipts sel C).card*cost+_≤_*cost at bill
  apply (tier_stock D V C 3 (3*r)).trans
  exact Nat.le_of_add_le_add_left (bill.trans mult)

attribute [aesop safe forward (immediate := [free,reg,short,ready,wide]) (rule_sets := [CHGraphFamilies])] wide_price
ch_family_split_result wide_price
#print axioms wide_price
end LeanCH.BR.LowShellCycleSelection
