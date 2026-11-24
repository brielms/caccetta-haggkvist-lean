import checkpoints.shen_extension.SingleArcCycleBalance

namespace LeanCH.BR.Closure.CycleHitMass
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor

/-- In the old flat column law the exterior mean number of heads on
any proper boundary cycle is (q+1)/q, independent of its location. -/
theorem mean {q : ℕ} {E : CH.Digraph} {V C : Finset ℕ} (cy : Cycle E V q C)
    {p : ℕ→ℚ} (pm : mass V p=1) (pc : ∀j∈V,WeightedSD.col q E V p j=1) :
    (∑i∈V \ C,p i*((q:ℚ)*(outN E C i).card-((q:ℚ)+1)))=0 := by
  have count (i : ℕ) : p i*((outN E C i).card:ℚ)=∑j∈C,if E i j=true then p i else 0 := by
    rw [←sum_filter]; simp [outN,mul_comm]
  have cols (j) (jc : j∈C) : (q:ℚ)*(∑i∈V,if E i j=true then p i else 0)=1-p j := by
    have eq := pc j (cy.sub jc)
    unfold WeightedSD.col inW at eq
    linarith only [eq]
  have tot : (q:ℚ)*(∑i∈V,p i*((outN E C i).card:ℚ))=(C.card:ℚ)-∑j∈C,p j := by
    simp_rw [count]
    rw [sum_comm,mul_sum,sum_congr rfl cols,sum_sub_distrib]
    simp
  have pm' : ∑i∈V,p i=1 := pm
  have full : (∑i∈V,p i*((q:ℚ)*(outN E C i).card-((q:ℚ)+1)))= -(∑j∈C,p j) := by
    simp only [mul_sub,mul_left_comm (p _) (q:ℚ),sum_sub_distrib,←mul_sum,←sum_mul,pm']
    rw [cy.size,Nat.cast_add,Nat.cast_one] at tot
    linarith only [tot]
  have internal : (∑i∈C,p i*((q:ℚ)*(outN E C i).card-((q:ℚ)+1)))= -(∑i∈C,p i) := by
    rw [←sum_neg_distrib]
    apply sum_congr rfl; intro i ic; rw [cy.heads i ic]; push_cast; ring
  have part := sum_sdiff (f:=fun i=>p i*((q:ℚ)*(outN E C i).card-((q:ℚ)+1))) cy.sub
  linarith only [part,full,internal]

theorem two_hits {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ} (cy : Cycle E V q C)
    (ex : (V \ C).Nonempty) {p : ℕ→ℚ} (pos : ∀i∈V,0<p i) (pm : mass V p=1)
    (pc : ∀j∈V,WeightedSD.col q E V p j=1) :
    ∃i∈V \ C,2≤(outN E C i).card := by
  by_contra! thin
  have neg := sum_neg (s:=V \ C) (f:=fun i=>p i*((q:ℚ)*(outN E C i).card-((q:ℚ)+1))) (fun i hi=>by
    have le : ((outN E C i).card:ℚ)≤1 := by exact_mod_cast (by have := thin i hi; omega : (outN E C i).card≤1)
    apply mul_neg_of_pos_of_neg (pos i (mem_sdiff.mp hi).1)
    linarith only [mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q : (0:ℚ)≤q)]) ex
  rw [mean cy pm pc] at neg
  exact (lt_irrefl _ neg)

end LeanCH.BR.Closure.CycleHitMass
#print axioms LeanCH.BR.Closure.CycleHitMass.mean
#print axioms LeanCH.BR.Closure.CycleHitMass.two_hits
