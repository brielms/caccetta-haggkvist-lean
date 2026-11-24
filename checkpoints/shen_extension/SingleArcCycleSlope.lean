import checkpoints.shen_extension.SingleArcCycleBalance

namespace LeanCH.BR.Closure.SingleArcCycleSlope
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse SingleArcCycleBalance
open scoped Matrix

noncomputable def score {I : Type*} [Fintype I] (q : ℕ) (N : Finset I) (z : I→ℝ) : ℝ :=
  (q:ℝ)*(∑j∈N,z j)-∑j,z j

/-- The price change is constant on every cycle label except the
midpoint. The unique old predecessor of the midpoint makes this exact. -/
theorem price_change {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ}
    (cy : Cycle E V q C) (a v : C) (av : E a v=true) (t x : ℝ) (j : C) :
    ((q:ℝ)+1)*tiltedPrices q E a v t x j =
      ((q:ℝ)+t)*tiltedPrices q E a v 1 x j+
        (t-1)*(1-(q:ℝ)*x-(if j=v then 1 else 0)) := by
  let R := realMatrix q E C
  let rhs (s : ℝ) (k : C) := (if k=v then (1:ℝ) else 0)-(if k=a then s else 0)
  let h (s : ℝ) := R⁻¹ *ᵥ rhs s
  have col (k : C) : E k v=true ↔ k=a := by
    constructor
    · intro kv
      have size : (inN E C v).card=1 := cy.incoming v v.property
      exact Subtype.ext (card_le_one.mp size.le _ (mem_inN.mpr ⟨k.property,kv⟩)
        _ (mem_inN.mpr ⟨a.property,av⟩))
    · rintro rfl; exact av
  have diff (k : C) : ((q:ℝ)+1)*rhs t k-((q:ℝ)+t)*rhs 1 k=(1-t)*R k v := by
    simp only [rhs,R,realMatrix_entry,col]
    split_ifs <;> ring
  have raw (i : C) : ((q:ℝ)+1)*h t i-((q:ℝ)+t)*h 1 i=(1-t)*(if i=v then 1 else 0) := by
    have iv := congrFun (congrFun (nonsing_inv_mul R (matrix_unit hq E C)) i) v
    change (∑k,R⁻¹ i k*R k v)=(1:Matrix C C ℝ) i v at iv
    rw [one_apply] at iv
    change _*(∑k,R⁻¹ i k*rhs t k)-_*(∑k,R⁻¹ i k*rhs 1 k)=_
    rw [mul_sum,mul_sum,←sum_sub_distrib,←iv,mul_sum]
    exact sum_congr rfl (fun k _=>by linear_combination R⁻¹ i k * diff k)
  change _*(h t j+(-t*x-h t v))=_*(h 1 j+(-1*x-h 1 v))+_
  have mid := raw v
  rw [ite_eq_left rfl] at mid
  linear_combination raw j - mid

def slope {I : Type*} [Fintype I] [DecidableEq I] (q : ℕ) (N : Finset I) (v : I) (x : ℝ) : ℝ :=
  1-(if v∈N then (q:ℝ) else 0)+((q:ℝ)*x-1)*((q:ℝ)+1-(q:ℝ)*N.card)

/-- With u=(t−1)/(q+t), the outside score after positive rescaling is
its score at t=1 plus u times a number determined by the hit count. -/
theorem score_change {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ}
    (cy : Cycle E V q C) (a v : C) (av : E a v=true) (t x : ℝ) (N : Finset C) :
    ((q:ℝ)+1)*score q N (tiltedPrices q E a v t x)=
      ((q:ℝ)+t)*score q N (tiltedPrices q E a v 1 x)+(t-1)*slope q N v x := by
  let z := fun s=>tiltedPrices q E a v s x
  have sumChange (S : Finset C) : ((q:ℝ)+1)*(∑j∈S,z t j)-((q:ℝ)+t)*(∑j∈S,z 1 j)=
      (t-1)*((S.card:ℝ)*(1-(q:ℝ)*x)-(if v∈S then 1 else 0)) := by
    rw [mul_sum,mul_sum,←sum_sub_distrib]
    have val (j : C) : ((q:ℝ)+1)*z t j-((q:ℝ)+t)*z 1 j=
        (t-1)*(1-(q:ℝ)*x-(if j=v then 1 else 0)) := by
      linarith only [price_change hq cy a v av t x j]
    simp only [val,←mul_sum,sum_sub_distrib,sum_const,nsmul_eq_mul,sum_ite_eq']
    ring
  have allSum := sumChange univ
  simp only [card_univ,Fintype.card_coe,cy.size,Nat.cast_add,Nat.cast_one,mem_univ,ite_true] at allSum
  change _*((q:ℝ)*(∑j∈N,z t j)-∑j,z t j)=_*((q:ℝ)*(∑j∈N,z 1 j)-∑j,z 1 j)+_
  unfold slope
  have loc := sumChange N
  by_cases mem : v∈N <;> simp only [mem,ite_true,ite_false] at loc ⊢ <;>
    linear_combination (q:ℝ)*loc-allSum

theorem signs {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ} (hq : 2≤q) {x : ℝ}
    (heavy : 1<((q:ℝ)-1)*x) (N : Finset I) (v : I) :
    (N.card=0 → 0<slope q N v x) ∧
    (N.card=1 → v∉N → slope q N v x=(q:ℝ)*x) ∧
    (2≤N.card → slope q N v x<0) := by
  have two : (2:ℝ)≤q := by exact_mod_cast hq
  have xp : 0<x := pos_of_mul_pos_right (by linarith only [heavy] : 0<((q:ℝ)-1)*x) (by linarith)
  have D : 0<(q:ℝ)*x-1 := by linarith only [heavy,xp]
  refine ⟨?_,?_,?_⟩
  · intro empty
    rw [card_eq_zero.mp empty]; simp [slope]
    nlinarith only [mul_pos D (show 0<(q:ℝ)+1 by linarith)]
  · intro one off
    simp [slope,one,off]
  · intro multi
    have m : (2:ℝ)≤N.card := by exact_mod_cast multi
    have cost : 1<((q:ℝ)*x-1)*((q:ℝ)-1) := by
      nlinarith only [mul_pos (show 0<(q:ℝ) by linarith) (sub_pos.mpr heavy)]
    have more := mul_nonneg D.le (mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr m))
    dsimp [slope]; split_ifs <;> nlinarith only [more,cost,two]

end LeanCH.BR.Closure.SingleArcCycleSlope
#print axioms LeanCH.BR.Closure.SingleArcCycleSlope.price_change
#print axioms LeanCH.BR.Closure.SingleArcCycleSlope.score_change
#print axioms LeanCH.BR.Closure.SingleArcCycleSlope.signs
