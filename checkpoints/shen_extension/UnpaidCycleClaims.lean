import checkpoints.shen_extension.SharedCycleContacts
import checkpoints.shen_extension.RetainedShellScores

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

noncomputable def representatives {D V q r k b} (sel : Selection D V q r k b) (C : Finset ℕ) :=
  (claims sel C).image sel.rep

noncomputable def receipts {D V q r k b} (sel : Selection D V q r k b) (C : Finset ℕ) :=
  (representatives sel C).offDiag ∩ DotClonePairCompletion.orderedIncomparable D V k

theorem represents_claim {D V q r k b C u} {sel : Selection D V q r k b}
    (um : u∈representatives sel C) :
    N2 D V u∈claims sel C ∧ sel.rep (N2 D V u)=u := by
  obtain ⟨Y,ym,rfl⟩ := mem_image.mp um
  rw [rep_key sel (mem_filter.mp ym).1]
  exact ⟨ym,rfl⟩

theorem representatives_card {D V q r k b} (sel : Selection D V q r k b) (C) :
    (representatives sel C).card=(claims sel C).card := by
  apply card_image_of_injOn
  intro Y y Z z eq
  exact (rep_key sel (mem_filter.mp y).1).symm.trans ((congrArg (N2 D V) eq).trans
    (rep_key sel (mem_filter.mp z).1))

/-- Even against all actual missing pairs between the chosen representatives,
some booked physical cycle receives at least as much debt as its receipts. -/
theorem unpaid_cycle {D V q r k b} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (time : k+k≤q) (floor : ∀v∈V,b≤(ball D V v k).card+1) (size : V.card≤2*b)
    (live : V.Nonempty) (sel : Selection D V q r k b) :
    ∃C∈booked sel,( (receipts sel C).card : ℚ )+
      ∑v∈C,share D V (booked sel) r (fun v=>surplus b (ball D V v k).card) C v ≤
      ∑Y∈claims sel C,(shellDebt D V k b Y : ℚ) := by
  classical
  by_contra! strict
  have has : (classes D V k b).Nonempty := by
    by_contra! empty
    have large v (vm : v∈V) : b+1≤(ball D V v k).card := by
      by_contra! h
      have low : v∈shellOrigins D V k b := mem_filter.mpr ⟨vm,by omega⟩
      exact (not_nonempty_iff_eq_empty.mpr empty) ⟨_,mem_image_of_mem _ low⟩
    have := card_ge_of_two_balls free time large large live
    omega
  have natv : booked sel⊆sel.family := by
    intro C cm
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact sel.assigned Y ym
  have iden C p (pm : p∈receipts sel C) := mem_offDiag.mp (mem_inter.mp pm).1
  have key C x (xm : x∈representatives sel C) := (mem_filter.mp (represents_claim xm).1).2
  have apart : ((booked sel) : Set (Finset ℕ)).PairwiseDisjoint (receipts sel) := by
    intro C _ H _ ne
    exact disjoint_left.mpr (fun p a b=>ne ((key C _ (iden C p a).1).symm.trans (key H _ (iden H p b).1)))
  obtain ⟨Y,ym⟩ := has
  apply ledger_from_cycle_receipts free hq time floor size (fun H hm=>sel.rooted H (natv hm))
    (fun H hm=>sel.sub H (natv hm)) reg sel.pay (receipts sel) (fun Y hy=>mem_image_of_mem _ hy)
    (fun _ _ _ pm=>(mem_inter.mp pm).2) _ apart (fun C cm=>(strict C cm).le)
    ⟨_,mem_image_of_mem _ ym,strict _ (mem_image_of_mem _ ym)⟩
  intro C _ p pm eq
  obtain ⟨a,b,ne⟩ := iden C p pm
  exact ne ((represents_claim a).2.symm.trans ((congrArg _ eq).trans (represents_claim b).2))

/-- Convert an unpaid rational bill to an integer inequality on the same
cycle. Only its own omission exponent enters, even in a mixed family. -/
theorem shortfall_of_bill {D V q r k b c C} (free : QFree D V q) (reg : OutEq r D V)
    (cut : c+2≤q) (sel : Selection D V q r k b) (cap : ∀H∈booked sel,omissions D V H r≤c)
    (cm : C∈booked sel) (bill : ((receipts sel C).card : ℚ) +
      (∑v∈C, share D V (booked sel) r (fun a=>surplus b (ball D V a k).card) C v)≤
        ∑Y∈claims sel C,(shellDebt D V k b Y:ℚ)) :
    let d := (c+1)*2^(omissions D V C r)
    (receipts sel C).card*d+(∑v∈C,surplus b (ball D V v k).card)≤(∑Y∈claims sel C,shellDebt D V k b Y)*d := by
  classical
  let d := (c+1)*2^(omissions D V C r)
  let P v := surplus b (ball D V v k).card
  have positive : 0<(d:ℚ) := by dsimp [d]; positivity
  have rooted H (hm : H∈booked sel) : ∀v∈H,Rooted D V v H := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp hm
    exact sel.rooted _ (sel.assigned Y ym)
  have row v (vm : v∈C) : (P v:ℚ)/(d:ℚ) ≤ share D V (booked sel) r (fun a=>(P a:ℚ)) C v := by
    have tc := turns_bound (v:=v) free cut rooted reg cap
    have occ : C∈through (booked sel) v := mem_filter.mpr ⟨cm,vm⟩
    have nz : 0<(turns D (booked sel) v).card := card_pos.mpr ⟨_,mem_image_of_mem _ occ⟩
    unfold share
    rw [←div_eq_mul_one_div,div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    dsimp [d]
    push_cast
    gcongr
    exact_mod_cast tc
  have rsum := sum_le_sum row
  rw [←sum_div] at rsum
  have bound := (add_le_add_right rsum ((receipts sel C).card:ℚ)).trans bill
  have final : ((receipts sel C).card:ℚ)*(d:ℚ)+(∑v∈C,(P v:ℚ)) ≤
        (∑Y∈claims sel C,(shellDebt D V k b Y:ℚ))*(d:ℚ) := by
    calc
      _ = ((receipts sel C).card+(∑v∈C,(P v:ℚ))/(d:ℚ))*(d:ℚ) := by
        rw [add_mul,div_mul_cancel₀ _ positive.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right bound positive.le
  exact_mod_cast final


theorem unpaid_stock {D V q r k b c} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (time : k+k≤q) (cut : c+2≤q) (floor : ∀v∈V,b≤(ball D V v k).card+1) (size : V.card≤2*b)
    (live : V.Nonempty) (sel : Selection D V q r k b) (cap : ∀C∈booked sel,omissions D V C r≤c) :
    ∃C∈booked sel, let d := (c+1)*2^(omissions D V C r)
                   (receipts sel C).card*d + (∑v∈C,surplus b (ball D V v k).card) ≤
                     (∑Y∈claims sel C,shellDebt D V k b Y)*d := by
  classical
  obtain ⟨C,cm,bill⟩ := unpaid_cycle free hq reg time floor size live sel
  exact ⟨C,cm,shortfall_of_bill free reg cut sel cap cm bill⟩

/-- Count one unit from each high row and the two additional units from each strong row.
The two sets are nested filters on the same carrier. -/
theorem tier_stock (D : CH.Digraph) (V C : Finset ℕ) (k b : ℕ) :
    (C.filter (fun v=>b<(ball D V v k).card)).card+
      2*(C.filter (fun v=>b+1<(ball D V v k).card)).card ≤
      ∑v∈C,surplus b (ball D V v k).card := by
  classical
  let H := C.filter (fun v=>b<(ball D V v k).card)
  let S := C.filter (fun v=>b+1<(ball D V v k).card)
  have sub : S⊆H := fun _ mem=>mem_filter.mpr ⟨(mem_filter.mp mem).1,by have := (mem_filter.mp mem).2; omega⟩
  have paid := RetainedShellScores.increments (W:=C) (A:=H) (B:=S) (C:=∅)
    (n:=0) (i:=1) (j:=2) (k:=0) (f:=fun v=>surplus b (ball D V v k).card)
    (filter_subset _ _) sub (empty_subset _) (fun _ _=>by omega)
    (fun v vm=>by have e:= (mem_filter.mp vm).2; simp [surplus,e]; omega)
    (fun v vm=>by have e:= (mem_filter.mp vm).2; simp [surplus,show b<(ball D V v k).card by omega]; omega)
    (fun _ h=>False.elim (notMem_empty _ h))
  simpa [Nat.mul_comm] using paid

def shortfall {D V q r k b} (sel : Selection D V q r k b) (C : Finset ℕ) (c : ℕ) :=
  let d := (c+1)*2^(omissions D V C r)
  (receipts sel C).card*d+(∑v∈C,surplus b (ball D V v k).card) ≤
    (∑Y∈claims sel C,shellDebt D V k b Y)*d

theorem unpaid_acyclic {D V q r target C c} (free : QFree D V q) (reg : OutEq r D V) (hr : 0<r)
    (sel : Selection D V q r 3 (3*r)) (cm : C∈booked sel) (under : shortfall sel C c)
    (all : ∀Y∈claims sel C,QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (regime : Room q r) (one : r≤q+2) (fit : r+1<2*(q-1))
    (dist : (r-(q+1))*(r-q)+3≤q) (guard : ScoreRoom q r (r-1) target)
    (pay : 3*r<4+target) :
    ∃Y,claims sel C={Y} ∧ sel.pay Y=C ∧ omissions D V C r≤1 ∧
      C.card≤(C.filter (fun v=>3*r<(ball D V v 3).card)).card+(r-C.card)*(r-q) ∧
      (C.filter (fun v=>3*r<(ball D V v 3).card)).card+
        2*(C.filter (fun v=>3*r+1<(ball D V v 3).card)).card≤(c+1)*2^(omissions D V C r) := by
  classical
  let K := claims sel C
  let R := representatives sel C
  let d := (c+1)*2^(omissions D V C r)
  let H := C.filter (fun v=>3*r<(ball D V v 3).card)
  let S := C.filter (fun v=>3*r+1<(ball D V v 3).card)
  let cost := ∑v∈C,surplus (3*r) (ball D V v 3).card
  have data Y (ym : Y∈K) : ClaimData D V Y C q r (sel.rep Y) target := by
    obtain ⟨key,eq⟩ := mem_filter.mp ym
    rw [←eq]
    exact claim_data free reg hr sel key regime (all Y ym) one fit dist guard
  have origin a (am : a∈R) := represents_claim am
  have separate a (am : a∈R) b (bm : b∈R) (ne : a≠b) : b∉ball D V a 3 := by
    obtain ⟨ak,ar⟩ := origin a am
    obtain ⟨bk,br⟩ := origin b bm
    have dis : N2 D V a≠N2 D V b := fun eq=>ne (ar.symm.trans ((congrArg _ eq).trans br))
    have ad := data _ ak
    have bd := data _ bk
    rw [ar] at ad
    rw [br] at bd
    exact separate_claims free (by have := regime.1; omega) reg hr (ar ▸ rep_native sel (mem_filter.mp ak).1)
      (br ▸ rep_native sel (mem_filter.mp bk).1) rfl rfl dis ad bd
  have allV {a} (am : a∈R) : a∈V := (origin a am).2 ▸ rep_native sel (mem_filter.mp (origin a am).1).1
  have holes : receipts sel C=R.offDiag := by
    apply inter_eq_left.mpr
    intro e em
    obtain ⟨a,b,ne⟩ := mem_offDiag.mp em
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨allV a,allV b,ne⟩,separate _ a _ b ne,separate _ b _ a ne.symm⟩
  have units := sum_le_sum (s:=K) (f:=fun Y=>shellDebt D V 3 (3*r) Y) (g:=fun _=>1)
    (fun Y ym=>(acyclic_class_debit free reg hr sel (mem_filter.mp ym).1 regime (all Y ym) (by omega) dist).2)
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at units
  obtain ⟨Y,ym,yc⟩ := mem_image.mp cm
  have yk : Y∈K := mem_filter.mpr ⟨ym,yc⟩
  have ydata := data Y yk
  have sub : C.filter (fun v=>4+target≤(ball D V v 3).card)⊆H :=
    fun v vm=>mem_filter.mpr ⟨(mem_filter.mp vm).1,pay.trans_le (mem_filter.mp vm).2⟩
  have supply : C.card≤H.card+(r-C.card)*(r-q) := ydata.scores.trans (Nat.add_le_add_right (card_le_card sub) _)
  have len := sel.length _ (sel.assigned Y ym)
  rw [yc] at len
  have delta := Nat.mul_le_mul_right (r-q) (show r-C.card≤r-(q+1) by omega)
  have stock : H.card+2*S.card≤cost := tier_stock D V C 3 (3*r)
  have positive : 0<cost := by omega
  change (receipts sel C).card*d+cost≤(∑a∈K,shellDebt D V 3 (3*r) a)*d at under
  rw [holes,offDiag_card] at under
  have kr : R.card=K.card := representatives_card sel C
  rw [kr] at under
  have cap := under.trans (Nat.mul_le_mul_right d units)
  have unique : K.card=1 := by
    have lo := card_pos.mpr (show K.Nonempty from ⟨Y,yk⟩)
    by_contra! bad
    have big := Nat.mul_le_mul_left K.card (show 2≤K.card by omega)
    have swallowed := Nat.mul_le_mul_right d (show K.card≤K.card*K.card-K.card by omega)
    omega
  have oneKey : K={Y} := eq_of_subset_of_card_le (singleton_subset_iff.mpr yk) (by simp [unique]) |>.symm
  rw [unique] at cap
  simp only [Nat.one_mul,Nat.sub_self,Nat.zero_mul,Nat.zero_add] at cap
  exact ⟨Y,oneKey,yc,ydata.loss,supply,stock.trans cap⟩
#print axioms unpaid_acyclic

#print axioms unpaid_stock
end LeanCH.BR.LowShellCycleSelection
