import Mathlib.Combinatorics.Enumerative.DoubleCounting
import LeanCH.BR.BR96

/-! Counts on the actual arcs between a marked parent set and the rest of the
carrier. The cutoff, degree, distance and size of the parent set are independent. -/
namespace LeanCH.BR.ParentCutPacking
open Finset BRq2 BRq3 BR45 BRsGen

theorem cross_capacity {α : Type*} [DecidableEq α] {V S R : Finset α}
    {r : ℕ} (row : α → Finset α) (degree : ∀v∈R,(row v).card≤r)
    (cover : ∀x∈S,∀y∈V\S,∃v∈R,x∈row v ∧ y∈row v) :
    S.card*(V\S).card ≤ R.card*(r*r/4) := by
  classical
  let cell := fun v => ((row v)∩S) ×ˢ ((row v)\S)
  have sub : S ×ˢ (V\S) ⊆ R.biUnion cell := by
    rintro ⟨x,y⟩ xy
    obtain ⟨xs,yc⟩ := mem_product.mp xy
    obtain ⟨v,vm,xv,yv⟩ := cover x xs y yc
    exact mem_biUnion.mpr ⟨v,vm,mem_product.mpr ⟨mem_inter.mpr ⟨xv,xs⟩,
      mem_sdiff.mpr ⟨yv,(mem_sdiff.mp yc).2⟩⟩⟩
  have per v (vm : v∈R) : (cell v).card≤r*r/4 := by
    dsimp only [cell]
    rw [card_product]
    have split := card_sdiff_add_card_inter (row v) S
    have size := degree v vm
    apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
    have amgm (a b : ℕ) : a*b*4≤(a+b)*(a+b) := by
      rcases le_total a b with h|h
      · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
        nlinarith
      · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
        nlinarith
    exact (amgm _ _).trans (Nat.mul_le_mul (by omega) (by omega))
  simpa only [card_product,Finset.sum_const_nat (fun _ _=>rfl)] using
    ((card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum per)))

/-- Retain the number of distinct parents needed per outside label. -/
theorem incidence_capacity {α : Type*} [DecidableEq α] {V S R : Finset α} {r l h : ℕ}
    (row : α→Finset α) (inside : S⊆V) (deg : ∀v∈R,(row v).card≤r)
    (inner : ∀x∈S,l≤(R.filter (fun v=>x∈row v)).card)
    (outer : ∀x∈V\S,h≤(R.filter (fun v=>x∈row v)).card) :
    S.card*l+(V\S).card*h≤R.card*r := by
  classical
  let col := fun x=>(R.filter (fun v=>x∈row v)).card
  have one := sum_le_sum inner
  have two := sum_le_sum outer
  have eq : (∑x∈V,col x) = ∑v∈R,((row v)∩V).card := by
    simp only [col,card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [←card_filter,filter_mem_eq_inter,inter_comm]
  have cap : (∑x∈V,col x)≤∑_v∈R,r := eq.le.trans (sum_le_sum (fun v vm=>
    (card_le_card inter_subset_left).trans (deg v vm)))
  rw [←sum_sdiff inside] at cap
  simpa [col,add_comm] using (add_le_add two one).trans cap

/-- If fewer than h rows hit the outside label, they have insufficient room
to cover S. Each of those rows uses one of its slots for the label itself. -/
theorem outside_multiplicity {α : Type*} [DecidableEq α] {V S R : Finset α} {r h : ℕ}
    (row : α→Finset α) (deg : ∀v∈R,(row v).card≤r)
    (cover : ∀x∈S,∀y∈V\S,∃v∈R,x∈row v ∧ y∈row v)
    (demand : (h-1)*(r-1)<S.card) (y) (ym : y∈V\S) :
    h≤(R.filter (fun v=>y∈row v)).card := by
  classical
  let A := R.filter (fun v=>y∈row v)
  have sub : S⊆A.biUnion (fun v=>(row v).erase y) := by
    intro x xm
    obtain ⟨v,vr,xv,yv⟩ := cover x xm y ym
    exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨vr,yv⟩,mem_erase.mpr ⟨fun eq=>
      (mem_sdiff.mp ym).2 (eq ▸ xm),xv⟩⟩
  have cap := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (g:=fun _=>r-1)
    (fun v (vm : v∈A)=>by rw [card_erase_of_mem (mem_filter.mp vm).2]; have := deg v (mem_filter.mp vm).1; omega)))
  simp only [sum_const,nsmul_eq_mul] at cap
  change h≤A.card
  by_contra! low
  exact (not_lt_of_ge (cap.trans (Nat.mul_le_mul_right (r-1) (by omega : A.card≤h-1)))) demand

theorem parent_outside {D V q a x v k} (free : QFree D V q) (av : a∈V)
    (dist : k+2≤q) (parent : x∈inN D V a) (px : D v x=true) : v∉ball D V a k := by
  intro hit
  obtain ⟨_,l,le,walk⟩ := mem_ball.mp hit
  obtain ⟨xv,xa⟩ := mem_inN.mp parent
  exact free a _ (by omega) (by omega) ((walk.snoc xv px).snoc av xa)

theorem covers_outside_ball {D V q a S k} (free : QFree D V q) (av : a∈V)
    (dist : k+2≤q) (sub : S⊆inN D V a)
    (pairs : ∀x∈V,∀y∈V,x≠y → ∃v∈V,D v x=true ∧ D v y=true) :
    ∀x∈S,∀y∈V\S,∃v∈V\ball D V a k,x∈outN D V v ∧ y∈outN D V v := by
  intro x xs y yc
  obtain ⟨yv,ys⟩ := mem_sdiff.mp yc
  have xv := (mem_inN.mp (sub xs)).1
  obtain ⟨v,vm,vx,vy⟩ := pairs x xv y yv (fun eq=>ys (eq ▸ xs))
  exact ⟨v,mem_sdiff.mpr ⟨vm,parent_outside free av dist (sub xs) vx⟩,
    mem_outN.mpr ⟨xv,vx⟩,mem_outN.mpr ⟨yv,vy⟩⟩

#print axioms cross_capacity
#print axioms incidence_capacity
#print axioms outside_multiplicity
#print axioms covers_outside_ball
end LeanCH.BR.ParentCutPacking
