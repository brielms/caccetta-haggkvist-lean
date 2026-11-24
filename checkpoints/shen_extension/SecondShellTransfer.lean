import checkpoints.shen_extension.ShortShellPayer

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen PhysicalCycleStock ExteriorPacking
open scoped Classical

/-- Transfer the entire residual class bill to its own literal second
shell. The original cross-class receipts are still credited exactly once. -/
noncomputable def switchedBill {D V q r k b} (sel : Selection D V q r k b)
    (M : Finset (Finset ℕ)) (C : Finset ℕ) : ℚ :=
  (if C∈booked sel then netDebt sel C else 0) -
  (∑Y∈M,if sel.pay Y=C then (shellDebt D V k b Y:ℚ) else 0) +
  (if C∈M then (shellDebt D V k b C:ℚ) else 0)

theorem switched_total {D V q r k b} (sel : Selection D V q r k b)
    {M : Finset (Finset ℕ)} (keys : M⊆classes D V k b) :
    ∑C∈booked sel∪M,switchedBill sel M C=∑C∈booked sel,netDebt sel C := by
  classical
  let F := booked sel∪M
  have balance : (∑C∈F,∑Y∈M,if sel.pay Y=C then (shellDebt D V k b Y:ℚ) else 0)=∑Y∈M,(shellDebt D V k b Y:ℚ) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro Y ym
    have hm : sel.pay Y∈F := mem_union_left _ (mem_image_of_mem _ (keys ym))
    simp [hm]
  have originals : F.filter (fun C=>C∈booked sel)=booked sel := by ext C; simp [F]
  have moves : F.filter (fun C=>C∈M)=M := by ext C; simp [F]
  change ∑C∈F,switchedBill sel M C=_
  simp only [switchedBill,sum_add_distrib,sum_sub_distrib]
  rw [balance]
  simp only [←sum_filter,originals,moves,sub_add_cancel]

/-- The switch never creates a second copy of an existing physical row.
Under the displayed capacity condition a brand-new receiver pays strictly.
Thus any remaining failure is at an originally booked cycle, tested with
its exact balance after all switches. -/
theorem old_payer_after_switch {D V q r k b d c} (sel : Selection D V q r k b)
    (free : QFree D V q) (reg : OutEq r D V) (hq : 2≤q) (time : k+k≤q)
    (floor : ∀v∈V,b≤(ball D V v k).card+1) (size : V.card≤2*b) (live : V.Nonempty)
    {M : Finset (Finset ℕ)} (keys : M⊆classes D V k b)
    (receivers : ∀Y∈M,CompletePayer D V r d Y)
    (loss : ∀C∈booked sel,omissions D V C r≤c) (room : c+d<r-1)
    (stock : ∀Y∈M, (shellDebt D V k b Y:ℚ)<∑v∈Y,(surplus b (ball D V v k).card:ℚ)) :
    ∃Y∈classes D V k b,Y∉M ∧ rowStock sel (booked sel) (sel.pay Y)≤switchedBill sel M (sel.pay Y) := by
  classical
  let F := booked sel∪M
  have old C (cm : C∈booked sel) : ∀x∈C,Rooted D V x C := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact sel.rooted _ (sel.assigned _ ym)
  have roots C (cm : C∈F) : ∀x∈C,Rooted D V x C :=
    (mem_union.mp cm).elim (old C) (fun ym=>(receivers C ym).rooted)
  have bounded C (cm : C∈F) : omissions D V C r≤c := by
    rcases mem_union.mp cm with cf|cs
    · exact loss C cf
    · simp [omissions,(receivers C cs).width]
  have unique {Y H} (ym : Y∈M) (hm : H∈F) {v} (vy : v∈Y) (vh : v∈H) : Y=H :=
    complete_exclusive free hq (receivers Y ym).rooted (roots H hm) reg
      (receivers Y ym).width (receivers Y ym).sparse (bounded H hm) room vy vh
  have unchanged C (cm : C∈booked sel) : rowStock sel F C=rowStock sel (booked sel) C := by
    apply sum_congr rfl
    intro v vm
    have same : through F v=through (booked sel) v := by
      ext Y
      simp only [through,mem_filter,F,mem_union]
      constructor
      · rintro ⟨om|nm,vy⟩
        · exact ⟨om,vy⟩
        · exact ⟨(unique nm (mem_union_left _ cm) vy vm).symm ▸ cm,vy⟩
      · exact fun h=>⟨Or.inl h.1,h.2⟩
    simp only [share,turns,same]
  have newStock Y (ym : Y∈M) : rowStock sel F Y=∑v∈Y,(surplus b (ball D V v k).card:ℚ) := by
    apply sum_congr rfl
    intro v vm
    have only : through F v={Y} := eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨mem_union_right _ ym,vm⟩,
      fun H hm=>(unique ym (mem_filter.mp hm).1 vm (mem_filter.mp hm).2).symm⟩
    simp [share,turns,only,omissions,(receivers Y ym).width]
  have total := no_global_surplus sel free hq reg time floor size roots
  rw [←switched_total sel keys] at total
  obtain ⟨C,cm,_⟩ := unpaid_cycle free hq reg time floor size live sel
  by_contra! no
  have cleared T (all : claims sel T⊆M) :
      switchedBill sel M T≤(if T∈M then (shellDebt D V k b T:ℚ) else 0) := by
    have same : M.filter (fun Y=>sel.pay Y=T)=claims sel T := by
      ext Y
      simp only [claims,mem_filter]
      exact ⟨fun h=>⟨keys h.1,h.2⟩,fun h=>⟨all (mem_filter.mpr h),h.2⟩⟩
    unfold switchedBill
    rw [←sum_filter,same]
    by_cases used : T∈booked sel
    · simp only [ite_eq_left used,netDebt]
      have nn := (Nat.cast_nonneg (receipts sel T).card : (0:ℚ)≤↑(receipts sel T).card)
      linarith
    · simp only [ite_eq_right used]
      have nn : (0:ℚ)≤∑Y∈claims sel T,(shellDebt D V k b Y:ℚ) := sum_nonneg (fun _ _=>Nat.cast_nonneg _)
      linarith
  have point T (tm : T∈F) : switchedBill sel M T≤rowStock sel F T ∧
      (T∈M ∨ ¬claims sel T⊆M → switchedBill sel M T<rowStock sel F T) := by
    by_cases erased : claims sel T⊆M
    · have bound := cleared T erased
      by_cases moved : T∈M
      · rw [ite_eq_left moved] at bound
        rw [newStock T moved]
        exact ⟨bound.trans (stock T moved).le,fun _=>bound.trans_lt (stock T moved)⟩
      · rw [ite_eq_right moved] at bound
        exact ⟨bound.trans (sum_nonneg (fun _ _=>by dsimp [share]; positivity)),
          fun either=>(either.elim moved (fun n=>n erased)).elim⟩
    · obtain ⟨Y,ym,away⟩ := Finset.not_subset.mp erased
      obtain ⟨key,assigned⟩ := mem_filter.mp ym
      have strict := no Y key away
      rw [assigned] at strict
      rw [unchanged T (assigned ▸ mem_image_of_mem sel.pay key)]
      exact ⟨strict.le,fun _=>strict⟩
  have strictOne : ∃T∈F,switchedBill sel M T<rowStock sel F T := by
    by_cases has : M.Nonempty
    · obtain ⟨Y,ym⟩ := has
      exact ⟨Y,mem_union_right _ ym,(point Y (mem_union_right _ ym)).2 (.inl ym)⟩
    obtain ⟨Y,yk,assigned⟩ := mem_image.mp cm
    have notIn : ¬claims sel C⊆M := fun sub=>has ⟨Y,sub (mem_filter.mpr ⟨yk,assigned⟩)⟩
    exact ⟨C,mem_union_left _ cm,(point C (mem_union_left _ cm)).2 (.inr notIn)⟩
  exact (not_lt_of_ge total) (sum_lt_sum (fun T tm=>(point T tm).1) strictOne)

attribute [aesop safe forward (immediate := [sel,free,reg,hq,time,floor,size,live,keys,receivers,loss,room,stock]) (rule_sets := [CHGraphFamilies])] old_payer_after_switch

#print axioms switched_total
#print axioms old_payer_after_switch
end LeanCH.BR.LowShellCycleSelection
