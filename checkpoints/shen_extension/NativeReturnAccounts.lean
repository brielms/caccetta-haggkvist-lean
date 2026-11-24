import checkpoints.shen_extension.TwoParentReturnCapacity
import checkpoints.shen_extension.SparseParentDual

namespace LeanCH.BR.Closure.NativeReturnAccounts
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity

/-- Contract the same adjacency entries first by tails and then by heads.
The forward and reverse vectors need not agree. -/
theorem balance (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w π : ℕ→ℚ) :
    (∑i∈V,π i*WeightedSD.row q E V w i)=∑j∈V,w j*WeightedSD.col q E V π j := by
  have eq : (∑i∈V,π i*outW E V w i)=∑j∈V,w j*inW E V π j := by
    simp only [outW,inW,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  calc
    _ = (∑i∈V,π i*w i)+q*∑i∈V,π i*outW E V w i := by
      simp only [WeightedSD.row,mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intros
      ring
    _ = _ := by
      rw [eq]
      simp only [WeightedSD.col,mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intros
      ring

/-- Equip the very forward vector used by the repair with a native column
equalizer of the same value, even if its original choice has been hidden. -/
theorem recover {q n w c} (X : ShortestCycleWeights.Model q n)
    (small : SmallerSmallRow q X.V.card) (wm : mass X.V w=1)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) :
    ∃π:ℕ→ℚ,(∀i∈X.V,0<π i) ∧ mass X.V π=1 ∧
      ∀i∈X.V,WeightedSD.col q X.D X.V π i=c := by
  obtain ⟨_,π,d,_,_,pp,_,pm,_,cols⟩ := strict_pair_of_proper_smallRow
    (small.induced X.free) X.live (fun i=>(X.weights i:ℚ)) (fun _ _=>Nat.cast_nonneg _) X.strict
  have eq := balance q X.D X.V w π
  simp only [Finset.sum_congr rfl (fun i hi => congrArg (fun v : ℚ => π i*v) (rows i hi)),
    Finset.sum_congr rfl (fun i hi => congrArg (fun v : ℚ => w i*v) (cols i hi)),←sum_mul] at eq
  change mass X.V π*c=mass X.V w*d at eq
  rw [pm,wm,one_mul,one_mul] at eq
  exact ⟨π,pp,pm,eq.symm ▸ cols⟩

/-- For an actual two-parent root the native column pays through exactly
these three labels. For distinct parents both of their prices occur. -/
theorem at_pair {q D V b p y π c} (par : inN D V b={p,y}) (ne : p≠y)
    (col : WeightedSD.col q D V π b=c) : π b+(q:ℚ)*(π p+π y)=c := by
  have eq : π b+(q:ℚ)*mass (inN D V b) π=c := by
    simpa only [WeightedSD.col,mass,inN,inW,sum_filter] using col
  simpa [par,mass,ne] using eq

/-- A short list of parents forces a heavy native parent. The head of b
supplies the strict bound on b's own price in the same column system. -/
theorem parent_bound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {b : ℕ} {π : ℕ→ℚ} {c : ℚ}
    (hq : 2≤q) (high : 1<c) (bv : b∈V) (live : (outN D V b).Nonempty)
    (pos : ∀i∈V,0<π i) (cols : ∀i∈V,WeightedSD.col q D V π i=c) :
    let P := inN D V b
    ∃i∈P, ((q:ℚ)-1)*c < (P.card:ℚ)*(q:ℚ)^2*π i ∧
      (P.card<q → 1<(q:ℚ)^2*π i) := by
  classical
  intro P
  obtain ⟨j,jh⟩ := live
  obtain ⟨jv,bj⟩ := mem_outN.mp jh
  have flat (k) (kv : k∈V) : π k+(q:ℚ)*mass (inN D V k) π=c := by
    simpa only [WeightedSD.col,inW,inN,mass,sum_filter] using cols k kv
  have pay : π b≤mass (inN D V j) π := by
    exact single_le_sum (fun i hi=>(pos i (mem_inN.mp hi).1).le) (mem_inN.mpr ⟨bv,bj⟩)
  have qn : 0≤(q:ℚ) := Nat.cast_nonneg _
  have qt : (2:ℚ)≤q := by exact_mod_cast hq
  have below : (q:ℚ)*π b<c := by linarith only [flat j jv,pos j jv,mul_le_mul_of_nonneg_left pay qn]
  have eq : π b+(q:ℚ)*mass P π=c := flat b bv
  have liveP : P.Nonempty := by
    by_contra empty
    rw [not_nonempty_iff_eq_empty.mp empty] at eq
    simp [mass] at eq
    nlinarith only [eq,below,pos b bv,mul_nonneg (show 0≤(q:ℚ)-1 by linarith) (pos b bv).le]
  obtain ⟨i,hi,top⟩ := P.exists_max_image π liveP
  have sum := sum_le_sum (s:=P) (fun j hj=>top j hj)
  have bound : mass P π≤P.card*π i := by simpa [mass,nsmul_eq_mul] using sum
  have scaled := congrArg (fun z : ℚ=>(q:ℚ)*z) eq
  have lo : ((q:ℚ)-1)*c<(P.card:ℚ)*(q:ℚ)^2*π i := by
    nlinarith only [scaled,below,mul_le_mul_of_nonneg_left bound (sq_nonneg (q:ℚ))]
  refine ⟨i,hi,lo,?_⟩
  intro few
  by_contra! light
  have k : (P.card:ℚ)+1≤q := by exact_mod_cast (show P.card+1≤q by omega)
  nlinarith only [lo,k,mul_le_mul_of_nonneg_left light (Nat.cast_nonneg P.card),
    mul_lt_mul_of_pos_left high (show (0:ℚ)<q-1 by linarith)]

#print axioms parent_bound

#print axioms balance
#print axioms recover
#print axioms at_pair
end LeanCH.BR.Closure.NativeReturnAccounts
