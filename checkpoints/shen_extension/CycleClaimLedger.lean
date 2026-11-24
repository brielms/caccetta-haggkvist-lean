import checkpoints.shen_extension.LowShellRecovery
import checkpoints.shen_extension.LowShellWholeCycle

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

noncomputable def classes (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) :=
  (shellOrigins D V k b).image (N2 D V)
noncomputable def claims {D V q r k b} (sel : Selection D V q r k b) (C : Finset ℕ) :=
  (classes D V k b).filter (fun Y => sel.pay Y=C)

/-- Only the image of the actual assignments participates in the row budget. -/
noncomputable def booked {D V q r k b} (sel : Selection D V q r k b) :=
  (classes D V k b).image sel.pay

theorem rep_key {D V q r k b Y} (sel : Selection D V q r k b) (ym : Y∈classes D V k b) :
    N2 D V (sel.rep Y)=Y := (mem_filter.mp (sel.represents Y ym)).2

theorem rep_native {D V q r k b Y} (sel : Selection D V q r k b) (ym : Y∈classes D V k b) :
    sel.rep Y∈V := (mem_filter.mp (mem_filter.mp (sel.represents Y ym)).1).1

/-- Missing directions between representatives of different shell classes are
additional physical receipts. Group their ordered pairs by the same selected
cycle. No such pair is counted inside a class or handed to two cycles. -/
theorem claim_ledger {D V q r k b} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (time : k+k≤q) (floor : ∀v∈V,b≤(ball D V v k).card+1) (size : V.card≤2*b)
    (sel : Selection D V q r k b)
    (separate : ∀Y∈classes D V k b,∀Z∈classes D V k b,Y≠Z → sel.pay Y=sel.pay Z →
      sel.rep Z∉ball D V (sel.rep Y) k)
    (paid : ∀C∈booked sel,
      (∑ Y∈claims sel C,(shellDebt D V k b Y : ℚ)) ≤
        ((claims sel C).offDiag.card:ℚ)+
        ∑v∈C,share D V (booked sel) r (fun a=>surplus b (ball D V a k).card) C v)
    (strict : ∃C∈booked sel,
      (∑ Y∈claims sel C,(shellDebt D V k b Y : ℚ)) <
        ((claims sel C).offDiag.card:ℚ)+
        ∑v∈C,share D V (booked sel) r (fun a=>surplus b (ball D V a k).card) C v) : False := by
  classical
  let rows C := (claims sel C).image sel.rep
  let holes C := (rows C).offDiag
  have key C a (am : a∈rows C) :
      N2 D V a∈classes D V k b ∧ sel.pay (N2 D V a)=C ∧ sel.rep (N2 D V a)=a := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp am
    obtain ⟨yc,mark⟩ := mem_filter.mp ym
    rw [rep_key sel yc]
    exact ⟨yc,mark,rfl⟩
  have apart : ((booked sel) : Set (Finset ℕ)).PairwiseDisjoint holes := by
    intro C _ H _ ne
    exact disjoint_left.mpr (fun p l r=>ne ((key _ _ (mem_offDiag.mp l).1).2.1.symm.trans
      (key _ _ (mem_offDiag.mp r).1).2.1))
  have real C (p : ℕ×ℕ) (pm : p∈holes C) :
      p∈DotClonePairCompletion.orderedIncomparable D V k ∧ N2 D V p.1≠N2 D V p.2 := by
    obtain ⟨a,b,ab⟩ := mem_offDiag.mp pm
    obtain ⟨ak,ac,ar⟩ := key C _ a
    obtain ⟨bk,bc,br⟩ := key C _ b
    have ne : N2 D V p.1≠N2 D V p.2 := fun eq=>ab (ar.symm.trans ((congrArg _ eq).trans br))
    have forward := separate _ ak _ bk ne (ac.trans bc.symm)
    have backward := separate _ bk _ ak ne.symm (bc.trans ac.symm)
    rw [ar,br] at forward backward
    exact ⟨mem_filter.mpr ⟨mem_offDiag.mpr ⟨ar ▸ rep_native sel ak,br ▸ rep_native sel bk,ab⟩,
      fun h=>forward h,fun h=>backward h⟩,ne⟩
  have card C : (holes C).card=(claims sel C).offDiag.card := by
    have inj : Set.InjOn sel.rep (claims sel C) := by
      intro Y ym Z zm eq
      exact (rep_key sel (mem_filter.mp ym).1).symm.trans ((congrArg (N2 D V) eq).trans
        (rep_key sel (mem_filter.mp zm).1))
    simp only [holes,rows,offDiag_card,card_image_of_injOn inj]
  have native : booked sel⊆sel.family := by
    intro C cm
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact sel.assigned Y ym
  obtain ⟨C,cm,lt⟩ := strict
  exact ledger_from_cycle_receipts free hq time floor size (fun H hm=>sel.rooted H (native hm))
    (fun H hm=>sel.sub H (native hm)) reg sel.pay holes (fun Y ym=>mem_image_of_mem _ ym)
    (fun H _ p pm=>(real H p pm).1) (fun H _ p pm=>(real H p pm).2) apart
    (fun H hm=>by rw [card]; exact paid H hm) ⟨C,cm,by rw [card]; exact lt⟩

/-- A unit residual per class is covered with at most one unit of row
stock per booked cycle, however many classes have the same image. -/
theorem unit_claim_exit {D V q r k b} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (time : k+k≤q) (floor : ∀v∈V,b≤(ball D V v k).card+1) (size : V.card≤2*b)
    (live : V.Nonempty) (sel : Selection D V q r k b)
    (debt : ∀Y∈classes D V k b,shellDebt D V k b Y≤1)
    (separate : ∀Y∈classes D V k b,∀Z∈classes D V k b,Y≠Z → sel.pay Y=sel.pay Z →
      sel.rep Z∉ball D V (sel.rep Y) k)
    (capacity : ∀C∈booked sel,(1:ℚ)<∑v∈C,share D V (booked sel) r
      (fun a=>surplus b (ball D V a k).card) C v) : False := by
  classical
  have has : (classes D V k b).Nonempty := by
    by_contra! empty
    have large v (vm : v∈V) : b+1≤(ball D V v k).card := by
      by_contra! h
      have low : v∈shellOrigins D V k b := mem_filter.mpr ⟨vm,by omega⟩
      exact (not_nonempty_iff_eq_empty.mpr empty) ⟨_,mem_image_of_mem _ low⟩
    have := card_ge_of_two_balls free time large large live
    omega
  have pay C (cm : C∈booked sel) :
      (∑ Y∈claims sel C,(shellDebt D V k b Y : ℚ)) <
        ((claims sel C).offDiag.card:ℚ)+
        ∑v∈C,share D V (booked sel) r (fun a=>surplus b (ball D V a k).card) C v := by
    let K := claims sel C
    have small Y (ym : Y∈K) : (shellDebt D V k b Y : ℚ)≤1 := by
      exact_mod_cast debt Y (mem_filter.mp ym).1
    have cost := sum_le_sum small
    simp only [sum_const,nsmul_eq_mul,mul_one] at cost
    have bound : K.card≤K.offDiag.card+1 := by
      rw [offDiag_card]
      have square : K.card*K.card+1≥2*K.card := by
        by_cases low : K.card≤1
        · rcases (by omega : K.card=0 ∨ K.card=1) with n|n <;> rw [n] <;> decide
        · have := Nat.mul_le_mul_left K.card (show 2≤K.card by omega)
          omega
      omega
    have lim : (K.card:ℚ)≤K.offDiag.card+1 := by exact_mod_cast bound
    have total := cost.trans lim
    apply lt_of_le_of_lt total
    exact add_lt_add_right (capacity C cm) _
  obtain ⟨Y,ym⟩ := has
  exact claim_ledger free hq reg time floor size sel separate (fun C cm=>(pay C cm).le)
    ⟨_,mem_image_of_mem _ ym,pay _ (mem_image_of_mem _ ym)⟩

#print axioms claim_ledger
#print axioms unit_claim_exit
end LeanCH.BR.LowShellCycleSelection
