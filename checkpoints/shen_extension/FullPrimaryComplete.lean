import checkpoints.shen_extension.FullPrimaryPayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- A full first-layer cycle identifies its own second shell. A different
claim can only come from the acyclic side, where its second shell must
equal the whole cycle and the class owes at most one unit. -/
theorem full_cohort_bill {D V q r target C cap} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (room : RoutingRoom q r V.card target) (full : C.card=r) :
    let E := exterior D V C
    E∈claims sel C ∧ C=outN D V (sel.rep E) ∧
    (∑Y∈claims sel C,shellDebt D V 3 (3*r) Y)≤shellDebt D V 3 (3*r) E+1 := by
  classical
  let E := exterior D V C
  have hr := room.growth.2.1
  have hq := room.cycle.1
  have fit := room.close
  have space := room.space
  have recover Y (ym : Y∈claims sel C) (first : C⊆outN D V (sel.rep Y)) :
      E=Y ∧ C=outN D V (sel.rep Y) := by
    have yk := (mem_filter.mp ym).1
    have uv := rep_native sel yk
    have eq := eq_of_subset_of_card_le first (by rw [reg _ uv,full])
    exact ⟨by dsimp [E]; rw [eq,ShellCycleSupply.head_exterior free (by omega) uv,rep_key sel yk],eq⟩
  obtain ⟨Y,ym,first,_⟩ := short.2.1
  obtain ⟨same,physical⟩ := recover Y ym first
  subst Y
  have secondary Y (ym : Y∈(claims sel C).erase E) :
      Y=C ∧ shellDebt D V 3 (3*r) Y≤1 := by
    obtain ⟨diff,charged⟩ := mem_erase.mp ym
    obtain ⟨key,book⟩ := mem_filter.mp charged
    have dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card := by
      by_contra no
      exact diff (recover Y charged (short.2.2.1 Y charged no)).1.symm
    have data := claim_data free reg (by omega) sel key room.cycle dag fit space room.distance room.score
    have sub := data.inside
    rw [book] at sub
    have cost := (acyclic_class_debit free reg (by omega) sel key room.cycle dag (by omega) room.distance).2
    exact ⟨(eq_of_subset_of_card_le sub (by rw [data.width,full])).symm,cost⟩
  have left := sum_le_sum (s:=(claims sel C).erase E) (fun Y ym=>(secondary Y ym).2)
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at left
  have cells : (claims sel C).erase E⊆{C} := fun Y ym=>mem_singleton.mpr (secondary Y ym).1
  have only := card_le_card cells
  rw [card_singleton] at only
  have sum := sum_erase_add (claims sel C) (fun Y=>shellDebt D V 3 (3*r) Y) ym
  refine ⟨ym,physical,?_⟩
  change _≤shellDebt D V 3 (3*r) E+1
  omega

/-- On a complete cycle, sparsity of the actual next bank prevents any
other booked cycle from drawing on the same physical rows. -/
theorem exclusive_stock {D V q r k b c d C} (free : QFree D V q) (hq : 2≤q)
    (reg : OutEq r D V) (sel : Selection D V q r k b) (cm : C∈booked sel)
    (complete : (exterior D V C).card=r-1) (sparse : ∀v∈exterior D V C,(outN D (exterior D V C) v).card≤d)
    (loss : ∀K∈booked sel,omissions D V K r≤c) (room : c+d<r-1) :
    rowStock sel (booked sel) C=∑v∈C,(surplus b (ball D V v k).card:ℚ) := by
  classical
  have roots K (km : K∈booked sel) : ∀v∈K,Rooted D V v K := by
    obtain ⟨Y,yk,rfl⟩ := mem_image.mp km
    exact sel.rooted _ (sel.assigned _ yk)
  apply sum_congr rfl
  intro v vm
  have alone : through (booked sel) v={C} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨cm,vm⟩,?_⟩
    intro H hm
    obtain ⟨hf,vh⟩ := mem_filter.mp hm
    exact (complete_exclusive free hq (roots C cm) (roots H hf) reg complete sparse (loss H hf) room vm vh).symm
  simp [share,turns,alone,omissions,complete]

/-- When the whole exterior is one smaller than the degree and the
three-ball is short, that exterior has an induced cycle on all its labels. -/
theorem complete_short_bank {D V q r C E u} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (hr : 2≤r) (fit : r≤q+2) (c : C=outN D V u) (e : E=N2 D V u)
    (paid : ∀x∈C,E⊆outN D V x) (width : E.card=r-1) (short : (ball D V u 3).card<3*r) :
    ∀a∈E,Rooted D V a E := by
  have ev : E⊆V := e ▸ (fun _ ym=>N2_subV ym)
  have cv : C⊆V := c ▸ outN_subset
  have start := card_B1 (free.mono_bound hq) uv
  rw [reg _ uv] at start
  have mid := @card_B2 D V u
  have last := @card_B3 D V u
  have ys : (N2 D V u).card=r-1 := e ▸ width
  have zsmall : (N3 D V u).card<r := by omega
  intro x xm
  refine ShellCycleSupply.rooted_on_small_set free (by omega) ev (by omega) ?_ xm
  intro a am
  have sub : outN D V a⊆outN D E a∪N3 D V u := by
    intro v vm
    have edge := (mem_outN.mp vm).2
    rcases headY (free.mono_bound hq) uv (e ▸ am) (outN_subset vm) edge with near|far
    · rcases mem_union.mp near with vx|vy
      · have vc : v∈C := c.symm ▸ vx
        exact (digonfree free (by omega) (ev am) (cv vc) edge (mem_outN.mp (paid v vc am)).2).elim
      · exact mem_union_left _ (mem_outN.mpr ⟨e.symm ▸ vy,edge⟩)
    · exact mem_union_right _ far
  have bound := (card_le_card sub).trans (card_union_le _ _)
  rw [reg _ (ev am)] at bound
  omega

theorem full_at_zero_false {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) (full : C.card=r)
    (width : (exterior D V C).card=r-1) : False := by
  classical
  let E := exterior D V C
  let u := sel.rep E
  have hr := ready.growth.2.1
  have hq := ready.cycle.1
  have fit := ready.close
  obtain ⟨ec,same,total⟩ := full_cohort_bill free reg short ready full
  have key := (mem_filter.mp ec).1
  have uv := rep_native sel key
  have ey : E=N2 D V u := (rep_key sel key).symm
  have ev : E⊆V := fun _ m=>N2_subV (ey ▸ m)
  have root := sel.rooted _ (sel.assigned _ key)
  have len := sel.length _ (sel.assigned _ key)
  have id := (mem_filter.mp ec).2
  rw [id] at root len
  have sub : C⊆V := same ▸ outN_subset
  have all v (vm : v∈C) : E⊆outN D V v := by
    have none := row_omissions (root v vm) (reg v (sub vm))
    have zero : omissions D V C r=0 := by simp [omissions,width]
    exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (none.trans zero))
  have grow := bank_growth free hq reg ev (card_pos.mp (by change 0<(exterior D V C).card; omega))
    (by change (exterior D V C).card≤2*q; omega) ready.cycle.2.1 (by simpa only [width,E] using ready.score)
  have allHigh v (vm : v∈C) : 3*r<(ball D V v 3).card := by
    have pays := score_from_bank (m:=0) free sub ev (fun x xm=>((root x xm).one x xm).ge) (by omega)
      (by omega) vm (all v vm) (by rw [filter_true_of_mem all]; omega) grow
    exact ready.high.trans_le pays
  have complete : ¬StrongTerminal D V r C := fun h=>by have := h.size; omega
  have original := short.2.2.2
  simp only [ite_eq_right complete,add_zero] at original
  have charge := le_sub_iff_add_le.mp original
  have actual : (↑(receipts sel C).card:ℚ)+rowStock sel (booked sel) C≤
      ∑Y∈claims sel C,(shellDebt D V 3 (3*r) Y:ℚ) := by linarith only [charge]
  have bounded K (km : K∈booked sel) : omissions D V K r≤r-q := by
    obtain ⟨Y,yk,rfl⟩ := mem_image.mp km; exact sel.loss _ (sel.assigned _ yk)
  have tier := tier_stock D V C 3 (3*r)
  rw [filter_true_of_mem allHigh] at tier
  by_cases early : (ball D V u 3).card<3*r
  · have sparse := complete_short_bank free (by omega) reg uv (by omega) fit same ey all width early
    have alone := exclusive_stock free (by omega) reg sel short.1 width (fun v vm=>((sparse v vm).one v vm).le) bounded (by omega)
    rw [alone] at actual
    have sumQ : ∑v∈C,(surplus (3*r) (ball D V v 3).card:ℚ)≤∑Y∈claims sel C,(shellDebt D V 3 (3*r) Y:ℚ) :=
      (le_add_of_nonneg_left (Nat.cast_nonneg (receipts sel C).card : (0:ℚ)≤↑(receipts sel C).card)).trans actual
    have count : (∑v∈C,surplus (3*r) (ball D V v 3).card)≤∑Y∈claims sel C,shellDebt D V 3 (3*r) Y := by exact_mod_cast sumQ
    have few : shellDebt D V 3 (3*r) E≤4 := by
      apply (class_residual (m:=3) _).trans (by decide)
      intro v _; unfold debit; split_ifs <;> omega
    change _≤shellDebt D V 3 (3*r) E+1 at total
    omega
  · have unit : shellDebt D V 3 (3*r) E≤1 := by
      apply (class_residual (m:=1) _).trans (by decide)
      intro v vm
      have minimum := sel.least E key v vm
      change (ball D V u 3).card≤_ at minimum
      have low := (mem_filter.mp (mem_filter.mp vm).1).2
      rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
    have ceiling := shortfall_of_bill free reg (by omega : r-q+2≤q) sel bounded short.1 actual
    have om : omissions D V C r=0 := by simp [omissions,width]
    rw [om,pow_zero,Nat.mul_one] at ceiling
    change _≤shellDebt D V 3 (3*r) E+1 at total
    have scale := Nat.mul_le_mul_right (r-q+1) (show (∑Y∈claims sel C,shellDebt D V 3 (3*r) Y)≤2 by omega)
    omega

#print axioms full_at_zero_false
end LeanCH.BR.LowShellCycleSelection
