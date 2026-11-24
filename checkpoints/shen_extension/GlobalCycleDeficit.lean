import checkpoints.shen_extension.RoutedCycleLedger

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

noncomputable def netDebt {D V q r k b} (sel : Selection D V q r k b) (C : Finset ℕ) : ℚ :=
  (∑Y∈claims sel C,(shellDebt D V k b Y:ℚ))-(receipts sel C).card

noncomputable def rowStock {D V q r k b} (_sel : Selection D V q r k b) (F : Finset (Finset ℕ)) (C : Finset ℕ) : ℚ :=
  ∑v∈C,share D V F r (fun a=>surplus b (ball D V a k).card) C v

theorem no_global_surplus {D V q r k b} (sel : Selection D V q r k b)
    (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V) (time : k+k≤q)
    (floor : ∀u∈V,b≤(ball D V u k).card+1) (size : V.card≤2*b)
    {F : Finset (Finset ℕ)} (root : ∀C∈F,∀v∈C,Rooted D V v C) :
    ∑C∈F,rowStock sel F C ≤ ∑C∈booked sel,netDebt sel C := by
  classical
  by_contra! gain
  let all := booked sel
  let holes := all.biUnion (receipts sel)
  have genuine : holes⊆DotClonePairCompletion.orderedIncomparable D V k := by
    intro p pm; obtain ⟨C,cm,inside⟩ := mem_biUnion.mp pm; exact (mem_inter.mp inside).2
  have marks {C} {p : ℕ×ℕ} (pm : p∈receipts sel C) := mem_offDiag.mp (mem_inter.mp pm).1
  have cross {C} {p : ℕ×ℕ} (pm : p∈receipts sel C) : N2 D V p.1≠N2 D V p.2 := by
    intro eq
    obtain ⟨a,b,ne⟩ := marks pm
    exact ne ((represents_claim a).2.symm.trans ((congrArg _ eq).trans (represents_claim b).2))
  have key {C u} (um : u∈representatives sel C) := (mem_filter.mp (represents_claim um).1).2
  have apart : (all:Set (Finset ℕ)).PairwiseDisjoint (receipts sel) := by
    intro C _ H _ ne
    exact disjoint_left.mpr (fun p a b=>ne ((key (marks a).1).symm.trans (key (marks b).1)))
  have num : (holes.card:ℚ)=∑C∈all,((receipts sel C).card:ℚ) := by
    exact_mod_cast card_biUnion apart
  apply ledger_from_shell_classes free hq time floor size root (fun C cm v vm=>(root C cm v vm).sub vm)
    reg genuine (fun p pm=>by obtain ⟨C,cm,h⟩ := mem_biUnion.mp pm; exact cross h)
  change (∑Y∈classes D V k b,(shellDebt D V k b Y:ℚ)) < (holes.card:ℚ)+∑C∈F,rowStock sel F C
  unfold netDebt at gain
  rw [sum_sub_distrib] at gain
  have total : (∑C∈all,∑Y∈claims sel C,(shellDebt D V k b Y:ℚ)) =
      ∑Y∈classes D V k b,(shellDebt D V k b Y:ℚ) :=
    sum_fiberwise_of_maps_to (fun Y ym=>mem_image_of_mem sel.pay ym) _
  change (∑C∈all,∑Y∈claims sel C,(shellDebt D V k b Y:ℚ)) - (∑C∈all,((receipts sel C).card:ℚ)) < _ at gain
  rw [total,←num] at gain
  linarith only [gain]

theorem pure_debt {D V q r target C} (free : QFree D V q) (reg : OutEq r D V) (hr : 0<r)
    (sel : Selection D V q r 3 (3*r)) (all : ∀Y∈claims sel C,
      QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (room : RoutingRoom q r V.card target) : netDebt sel C≤1 := by
  classical
  let K := claims sel C
  let R := representatives sel C
  have data Y (ym : Y∈K) : ClaimData D V Y C q r (sel.rep Y) target := by
    obtain ⟨key,eq⟩ := mem_filter.mp ym
    rw [←eq]
    exact claim_data free reg hr sel key room.cycle (all Y ym) room.close room.space room.distance room.score
  have sep a (am : a∈R) b (bm : b∈R) (ne : a≠b) : b∉ball D V a 3 := by
    obtain ⟨ak,ar⟩ := represents_claim am
    obtain ⟨bk,br⟩ := represents_claim bm
    have dis : N2 D V a≠N2 D V b := fun eq=>ne (ar.symm.trans ((congrArg _ eq).trans br))
    have ad := data _ ak
    have bd := data _ bk
    rw [ar] at ad
    rw [br] at bd
    exact separate_claims free (by have := room.cycle.1; omega) reg hr (ar ▸ rep_native sel (mem_filter.mp ak).1)
      (br ▸ rep_native sel (mem_filter.mp bk).1) rfl rfl dis ad bd
  have av {a} (am : a∈R) : a∈V :=
    (represents_claim am).2 ▸ rep_native sel (mem_filter.mp (represents_claim am).1).1
  have holes : receipts sel C=R.offDiag := by
    apply inter_eq_left.mpr
    intro p pm
    obtain ⟨a,b,ne⟩ := mem_offDiag.mp pm
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨av a,av b,ne⟩,sep _ a _ b ne,sep _ b _ a ne.symm⟩
  have units Y (ym : Y∈K) : (shellDebt D V 3 (3*r) Y:ℚ)≤1 := by
    exact_mod_cast (acyclic_class_debit free reg hr sel (mem_filter.mp ym).1 room.cycle (all Y ym)
      (by have := room.close; have := room.space; omega) room.distance).2
  have cost := sum_le_sum units
  simp only [sum_const,nsmul_eq_mul,mul_one] at cost
  have numeric : K.card≤R.offDiag.card+1 := by
    rw [offDiag_card,show R.card=K.card from representatives_card sel C]
    by_cases small : K.card≤1
    · omega
    have := Nat.mul_le_mul_left K.card (show 2≤K.card by omega)
    omega
  unfold netDebt
  rw [holes]
  have translated : (K.card:ℚ)≤R.offDiag.card+1 := by exact_mod_cast numeric
  change (∑Y∈K,(shellDebt D V 3 (3*r) Y:ℚ)) - (R.offDiag.card:ℚ)≤1
  linarith only [cost,translated]


/-- A counting step for simultaneous transfers. Every exceptional source
pays at most one, and each physical destination is reserved up to cap times. -/
theorem transfer_sum {α : Type*} [DecidableEq α] {F P K : Finset α} {cap : ℕ}
    (live : F.Nonempty) (pf : P⊆F) (sep : Disjoint P K)
    (whereTo : α→α) (dest : ∀x∈P,whereTo x∈K)
    (count : ∀z∈K,(P.filter (fun x=>whereTo x=z)).card≤cap)
    (debt stock : α→ℚ) (one : ∀x∈P,debt x≤1)
    (nn : ∀x∈F∪K,0≤stock x)
    (safe : ∀x∈(F∪K)\P,(if x∈F then debt x else 0)+(if x∈K then (cap:ℚ) else 0)<stock x) :
    ∑x∈F,debt x < ∑x∈F∪K,stock x := by
  classical
  let H := (F∪K)\P
  have pk : K⊆H := fun x xm=>mem_sdiff.mpr ⟨mem_union_right _ xm,fun p=>disjoint_left.mp sep p xm⟩
  have hk : H.Nonempty := by
    obtain ⟨x,xf⟩ := live
    by_cases xp : x∈P
    · exact ⟨_,pk (dest _ xp)⟩
    · exact ⟨x,mem_sdiff.mpr ⟨mem_union_left _ xf,xp⟩⟩
  have summed := sum_lt_sum (fun x (xm : x∈H)=>(safe x xm).le) (hk.imp (fun x xm=>⟨xm,safe x xm⟩))
  rw [sum_add_distrib,←sum_filter,←sum_filter] at summed
  have hf : H.filter (fun x=>x∈F)=F\P := by ext; simp [H]; tauto
  have hK : H.filter (fun x=>x∈K)=K := by ext; simp only [mem_filter]; exact ⟨And.right,fun h=>⟨pk h,h⟩⟩
  rw [hf,hK,sum_const,nsmul_eq_mul] at summed
  have little := sum_le_sum one
  simp only [sum_const,nsmul_eq_mul,mul_one] at little
  have banks : P.card≤K.card*cap := by
    have bound := sum_le_sum count
    rw [sum_const_nat (fun _ _=>rfl)] at bound
    have exactCount : (∑z∈K,(P.filter (fun x=>whereTo x=z)).card)=P.card := by
      simpa only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] using
        (sum_fiberwise_of_maps_to dest (fun _=>1 : α→ℕ))
    omega
  have m : (P.card:ℚ)≤(K.card:ℚ)*cap := by exact_mod_cast banks
  have combined := sum_sdiff pf (f:=debt)
  have all := sum_le_sum_of_subset_of_nonneg (sdiff_subset : H⊆F∪K) (fun x xm _=>nn x xm)
  linarith only [summed,little,m,combined,all]

open scoped Classical

/-- At least one first-layer claim survives *after paying all weak secondary
groups together*. A booked strong terminal may have to reserve cap units;
every other cycle is tested at its original full stock. -/
theorem outstanding_primary {D V q r target top} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (sel : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (ledger : AssignmentLedger sel (V.card-((r-1)+top))) (cap : ℕ)
    (crowd : (V.card-((r-1)+top))*2 < (cap+1)*fullRowFloor q r)
    (spare : cap+1<3*(r-1)) :
    ∃C∈booked sel,FirstClaim sel C ∧
      rowStock sel (booked sel) C ≤ netDebt sel C + (if StrongTerminal D V r C then (cap:ℚ) else 0) := by
  classical
  by_contra! no
  let F := booked sel
  let rank := r-q
  let δ := V.card-((r-1)+top)
  let debt := netDebt sel
  let original := rowStock sel F
  let P := F.filter (fun C=>¬FirstClaim sel C ∧ ¬StrongTerminal D V r C ∧ original C≤debt C)
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have lower u (um : u∈V) : 3*r≤(ball D V u 3).card+1 := by
    have := ShellBankOrders.mixed_third free ready.growth reg um; omega
  have room : rank+1<r-1 := by dsimp [rank]; omega
  have rooted C (cm : C∈F) : ∀v∈C,Rooted D V v C := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact sel.rooted _ (sel.assigned Y ym)
  have omitted C (cm : C∈F) : omissions D V C r≤rank := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm; exact sel.loss _ (sel.assigned Y ym)
  have fLive : F.Nonempty := by
    obtain ⟨C,cm,_⟩ := unpaid_cycle free (by omega) reg (by omega) lower ready.small live sel
    exact ⟨C,cm⟩
  have facts C (cm : C∈P) := by
    obtain ⟨cf,notFirst,_,price⟩ := mem_filter.mp cm
    have pay := le_sub_iff_add_le.mp price
    have bill := shortfall_of_bill free reg (by dsimp [rank]; have := ready.close; omega : rank+2≤q)
      sel omitted cf (by change (↑(receipts sel C).card:ℚ)+original C≤_; rw [add_comm]; exact pay)
    exact (ledger.route C cf bill).resolve_left notFirst
  let assign C := if cm:C∈P then ((facts C cm).2.choose) else C
  let K := P.image assign
  have actual C (cm : C∈P) :
      StrongTerminal D V r (assign C) ∧ WeakArrival D V r δ (fullRowFloor q r) 1 C (assign C) := by
    simpa only [assign,dite_eq_left cm] using (facts C cm).2.choose_spec
  have terminals T (tm : T∈K) : StrongTerminal D V r T := by
    obtain ⟨C,cm,rfl⟩ := mem_image.mp tm; exact (actual C cm).1
  have noDouble : Disjoint P K := disjoint_left.mpr (fun C a b=>(mem_filter.mp a).2.2.1 (terminals C b))
  have count T (_ : T∈K) : (P.filter (fun C=>assign C=T)).card≤cap := by
    have bound := ledger.limit T (P.filter (fun C=>assign C=T)) (fun C cm=>(mem_filter.mp cm).2 ▸ (actual C (mem_filter.mp cm).1).2)
    by_contra! lo
    have too := Nat.mul_le_mul_right (fullRowFloor q r) (show cap+1≤(P.filter (fun C=>assign C=T)).card by omega)
    omega
  let F' := F∪K
  have rootAll C (cm : C∈F') : ∀x∈C,Rooted D V x C := by
    rcases mem_union.mp cm with old|new
    · exact rooted _ old
    · exact (terminals _ new).rooted
  have omAll C (cm : C∈F') : omissions D V C r≤rank := by
    rcases mem_union.mp cm with old|new
    · exact omitted _ old
    · simp [omissions,(terminals _ new).nextSize]
  have fixed C (cm : C∈F) : rowStock sel F' C=original C :=
    sum_congr rfl (fun v vm=>shares_unchanged free (by omega) reg terminals rooted omitted room _ cm vm)
  have available C (cm : C∈F') (term : StrongTerminal D V r C) :
      (cap:ℚ)+1 < rowStock sel F' C := by
    have h := terminal_stock free (by omega) reg term cm rootAll omAll room
    have hh : ((cap:ℚ)+1)<((3*(r-1):ℕ):ℚ) := by exact_mod_cast spare
    exact hh.trans_le h
  have funded := transfer_sum fLive (filter_subset _ _ : P⊆F) noDouble assign (fun _ cm=>mem_image_of_mem _ cm) count
    debt (rowStock sel F') (fun C cm=>by
      have a := (facts C cm).1
      have aa : (∑Y∈claims sel C,(shellDebt D V 3 (3*r) Y:ℚ))≤1 := by exact_mod_cast a
      change (∑Y∈claims sel C,(shellDebt D V 3 (3*r) Y:ℚ))-(receipts sel C).card≤1
      exact (sub_le_self _ (by positivity)).trans aa)
    (fun C _=>sum_nonneg (fun v _=>by dsimp [share]; positivity)) (by
      intro C cm
      obtain ⟨used,off⟩ := mem_sdiff.mp cm
      by_cases old : C∈F
      · rw [ite_eq_left old]
        by_cases primary : FirstClaim sel C
        · have lim := no C old primary
          rw [fixed _ old]
          change debt C+(if StrongTerminal D V r C then (cap:ℚ) else 0)<original C at lim
          by_cases reach : C∈K
          · simpa [reach,terminals _ reach] using lim
          · rw [ite_eq_right reach]; split_ifs at lim <;> linarith
        by_cases term : StrongTerminal D V r C
        · have lim := available C used term
          have dd := pure_debt free reg (by omega) sel (ledger.acyclic C primary) ready
          change debt C≤1 at dd
          split_ifs <;> linarith
        have cheap : ¬original C≤debt C := fun h=>off (mem_filter.mpr ⟨old,primary,term,h⟩)
        rw [ite_eq_right (fun cm=>term (terminals C cm)),add_zero,fixed _ old]
        exact lt_of_not_ge cheap
      · have new := (mem_union.mp used).resolve_left old
        rw [ite_eq_right old,ite_eq_left new,zero_add]
        exact (lt_add_one (cap:ℚ)).trans (available C used (terminals C new)))
  exact (not_lt_of_ge (no_global_surplus sel free (by omega) reg (by omega) lower ready.small rootAll)) funded

/-- A short primary cycle is marked on the exact thinning that supplies its
representatives. The reserved amount can only be claimed by a strong terminal. -/
def PrimaryShort {D V q r} (sel : Selection D V q r 3 (3*r)) (cap : ℕ) (C : Finset ℕ) : Prop :=
  C∈booked sel ∧ FirstClaim sel C ∧
    (∀Y∈claims sel C,¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card → C⊆outN D V (sel.rep Y)) ∧
    rowStock sel (booked sel) C ≤ netDebt sel C +
    (if StrongTerminal D V r C then (cap:ℚ) else 0)

structure PrimaryRoom (q r n target g mid top cap : ℕ) : Prop where
  route : RoutingRoom q r n target
  transfer : TransferRoom q r n g mid top
  crowd : (n-((r-1)+top))*2 < (cap+1)*fullRowFloor q r
  spare : cap+1<3*(r-1)

theorem primary_frontier {D V q r target g mid top cap} (free : QFree D V q)
    (reg : OutEq r D V) (live : V.Nonempty) (sel : Selection D V q r 3 (3*r))
    (room : PrimaryRoom q r V.card target g mid top cap) :
    ∃t : Selection D V q r 3 (3*r),t.rep=sel.rep ∧ ∃C,PrimaryShort t cap C := by
  obtain ⟨t,same,ledger⟩ := all_claims free reg sel room.route room.transfer
  obtain ⟨C,cm,primary,bill⟩ := outstanding_primary free reg live t room.route ledger cap room.crowd room.spare
  exact ⟨t,same,C,cm,primary,fun Y ym dag=>(mem_filter.mp ym).2 ▸ ledger.first Y (mem_filter.mp ym).1 dag,bill⟩

theorem native_primary {D V q r target g mid top cap} (free : QFree D V q)
    (reg : OutEq r D V) (live : V.Nonempty) (room : PrimaryRoom q r V.card target g mid top cap) :
    ∃t : Selection D V q r 3 (3*r),∃C,PrimaryShort t cap C := by
  obtain ⟨hq,a,b,c,d,e,f,g₁⟩ := room.route.cycle
  obtain ⟨sel⟩ := native_selection free hq reg a b c d e f g₁
  obtain ⟨t,_,rest⟩ := primary_frontier free reg live sel room
  exact ⟨t,rest⟩

structure OnPrimaryDeficit (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀q≤CHRuleCatalog.cutoff p,∀target g mid top cap,
    PrimaryRoom q p.s p.n target g mid top cap →
    ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀sel : Selection F (range p.n) q p.s 3 (3*p.s),
        ∃t : Selection F (range p.n) q p.s 3 (3*p.s),t.rep=sel.rep ∧ ∃C,PrimaryShort t cap C

theorem primary_on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : OnPrimaryDeficit p := by
  constructor
  intro q cut target g mid top cap room F sub reg sel
  exact primary_frontier (qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut))
    reg ⟨0,mem_range.mpr bad.order⟩ sel (by simpa only [card_range] using room)

attribute [aesop safe forward (immediate := [free,reg,live,room]) (rule_sets := [CHGraphFamilies])] native_primary
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] primary_on_bad

#print axioms primary_on_bad
#print axioms native_primary
#print axioms outstanding_primary

#print axioms no_global_surplus
#print axioms pure_debt
end LeanCH.BR.LowShellCycleSelection
