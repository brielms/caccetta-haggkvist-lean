import checkpoints.shen_extension.ParentReturnDeposit

namespace LeanCH.BR.Closure.TwoParentWithdrawalDual
open Finset BRq2 BRq3 BR45 WeightedSD

def reserve (q : ℕ) (E : CH.Digraph) (U : Finset ℕ) (x : ℕ→ℝ) (i : ℕ) :=
  realRow q E U x i-realMass U x

/-- The same puncture dual separates all nonnegative final allocations,
including ones made by arbitrary signed changes of the old weights. -/
theorem priced_sum {q E U ρ} (dual : RealDual q E U 1 ρ)
    (x : ℕ→ℝ) (nn : ∀i∈U,0≤x i) :
    (∑ i∈U,ρ i*reserve q E U x i) = - ∑ j∈U,x j*(1-realCol q E U ρ j) ∧
    (∑ i∈U,ρ i*reserve q E U x i)≤0 := by
  have eq : (∑ i∈U,ρ i*reserve q E U x i) = - ∑ j∈U,x j*(1-realCol q E U ρ j) := by
    simp only [reserve,mul_sub,sum_sub_distrib,←sum_mul,real_cross_rows,mul_one]
    change _-realMass U ρ*realMass U x= - (realMass U x-_)
    rw [dual.normalized]; ring
  exact ⟨eq,eq.trans_le (neg_nonpos.mpr (sum_nonneg fun j jv=>mul_nonneg (nn j jv) (sub_nonneg.mpr (dual.columns j jv))))⟩

/-- Both named parents carry positive mass in EVERY puncture dual. -/
theorem parent_prices {q E V b p y t u w c} (hq : 2≤q) (free : QFree E V q)
    (bv : b∈V) (parents : inN E V b={p,y}) (ne : p≠y)
    (tu : t∈V.erase b) (uu : u∈V.erase b) (pt : E p t=true) (yu : E y u=true)
    (wp : ∀i∈V,0<w i) (rows : ∀i∈V,WeightedSD.row q E V w i=c)
    {ρ} (dual : RealDual q E (V.erase b) 1 ρ) :
    let σ : ℝ := (c:ℝ)-(mass V w:ℝ)
    let m : ℝ := w b
    m+σ≤q*m*(ρ p+ρ y) ∧ q*ρ p≤1 ∧ q*ρ y≤1 ∧ σ≤q*m*ρ p ∧ σ≤q*m*ρ y := by
  intro σ m
  let U := V.erase b
  have survives {i} (par : i∈inN E V b) : i∈U :=
    mem_erase.mpr ⟨fun eq=>loopfree free (by omega) bv (eq ▸ (mem_inN.mp par).2),(mem_inN.mp par).1⟩
  have pu := survives (parents ▸ mem_insert_self p {y})
  have yv := survives (parents ▸ mem_insert_of_mem (mem_singleton_self y))
  have upper {i j} (iu : i∈U) (ju : j∈U) (edge : E i j=true) : (q:ℝ)*ρ i≤1 := by
    have le : ρ i≤realInW E U ρ j := by
      rw [realInW]
      simpa only [edge,ite_true] using single_le_sum (s:=U) (f:=fun k=>if E k j=true then ρ k else 0)
        (fun k ku=>by split_ifs; exact dual.nonneg k ku; exact le_rfl) iu
    have col := dual.columns j ju
    unfold realCol at col
    linarith only [col,dual.nonneg j ju,mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q : (0:ℝ)≤q)]
  have up := upper pu tu pt
  have uy := upper yv uu yu
  have row (i) (iv : i∈U) : realRow q E U (fun j=>(w j:ℝ)) i =
      (c:ℝ)-(if i∈({p,y}:Finset ℕ) then q*m else 0) := by
    have incidence : E i b=true ↔ i∈({p,y}:Finset ℕ) := by
      rw [←parents,mem_inN]; simp [mem_of_mem_erase iv]
    have old := rows i (mem_of_mem_erase iv)
    rw [WeightedSD.row,outW_erase bv] at old
    rw [realRow_rat,WeightedSD.row]
    dsimp only [U,m]; by_cases arc : E i b=true
    · simp only [arc,incidence.mp arc,ite_true] at old ⊢
      exact_mod_cast (show w i+q*outW E (V.erase b) w i=c-q*w b by linarith only [old])
    · have off : i∉({p,y}:Finset ℕ) := fun h=>arc (incidence.mpr h)
      rw [ite_eq_right arc,add_zero] at old
      rw [ite_eq_right off,sub_zero]
      exact_mod_cast old
  have base := (priced_sum dual (fun i=>(w i:ℝ)) (fun i iu=>by exact_mod_cast (wp i (mem_of_mem_erase iu)).le)).2
  have total : realMass U (fun i=>(w i:ℝ))=(mass V w:ℝ)-m := by
    have split : mass U w+w b=mass V w := sum_erase_add _ _ bv
    rw [realMass_rat]; dsimp only [m]; exact_mod_cast (show mass U w=mass V w-w b by linarith)
  have weight : (∑i∈U,ρ i*(if i∈({p,y}:Finset ℕ) then (q:ℝ)*m else 0))=(ρ p+ρ y)*(q*m) := by
    simp only [mul_ite,mul_zero,←sum_filter,filter_mem_eq_inter,
      inter_eq_right.mpr (insert_subset pu (singleton_subset_iff.mpr yv)),sum_pair ne,add_mul]
  change (∑i∈U,ρ i*(realRow q E U (fun j=>(w j:ℝ)) i-realMass U (fun j=>(w j:ℝ))))≤0 at base
  have entry (i) (iv : i∈U) :
      ρ i*(realRow q E U (fun j=>(w j:ℝ)) i-realMass U (fun j=>(w j:ℝ))) =
      ρ i*((c:ℝ)-(mass V w:ℝ)+m)-ρ i*(if i∈({p,y}:Finset ℕ) then q*m else 0) := by
    rw [row i iv,total]; ring
  rw [sum_congr rfl entry] at base
  rw [sum_sub_distrib,weight,←sum_mul] at base
  change realMass U ρ*_ - _ ≤ 0 at base
  rw [dual.normalized,one_mul] at base
  have init : m+σ≤q*m*(ρ p+ρ y) := by dsimp only [σ]; linarith only [base]
  have mn : 0≤m := by dsimp only [m]; exact_mod_cast (wp b bv).le
  exact ⟨init,up,uy,by linarith only [init,mul_le_mul_of_nonneg_right uy mn],
    by linarith only [init,mul_le_mul_of_nonneg_right up mn]⟩

/-- Keeping all other rows weakly paid and p's positive reserve A forces
a deficit of at least σ A / w(b) at y, even if old weights are withdrawn. -/
theorem tradeoff {q E U p y ρ} (ne : p≠y) (pu : p∈U) (yu : y∈U)
    (dual : RealDual q E U 1 ρ) {σ m : ℝ} (mp : 0<m)
    (lower : σ≤q*m*ρ p) (upper : q*ρ y≤1) (yp : 0<ρ y) (x : ℕ→ℝ) (xn : ∀i∈U,0≤x i)
    (others : ∀i∈U, i≠p → i≠y → 0≤reserve q E U x i)
    (paid : 0≤reserve q E U x p) :
    σ*reserve q E U x p ≤ m*(-reserve q E U x y) := by
  let S : Finset ℕ := {p,y}
  have sub : S⊆U := insert_subset pu (singleton_subset_iff.mpr yu)
  have sum := (priced_sum dual x xn).2
  have pair := sum_le_sum_of_subset_of_nonneg (f:=fun i=>ρ i*reserve q E U x i) sub (fun i iv absent=>
    mul_nonneg (dual.nonneg i iv) (others i iv (fun eq=>absent (eq ▸ mem_insert_self _ _))
      (fun eq=>absent (eq ▸ mem_insert_of_mem (mem_singleton_self _)))))
  rw [show S={p,y} from rfl,sum_pair ne] at pair
  have yd : 0≤ -reserve q E U x y := by
    by_contra! neg
    linarith only [pair,sum,mul_nonneg (dual.nonneg p pu) paid,mul_pos yp (show 0<reserve q E U x y by linarith)]
  have both : ρ p*reserve q E U x p≤ρ y*(-reserve q E U x y) := by linarith only [pair,sum]
  nlinarith only [mul_le_mul_of_nonneg_right lower paid,
    mul_le_mul_of_nonneg_left both (mul_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) mp.le),
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right upper yd) mp.le]

#print axioms priced_sum
#print axioms parent_prices
#print axioms tradeoff

/-- After arbitrary withdrawals and deposits, keeping p weakly paid and all
nonparents weakly paid forces y's deficit. In any all-weak allocation both
parents are exactly tight. The dual comes from the smaller-support law. -/
theorem on_puncture {q E V b p y t u w c} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (bv : b∈V) (parents : inN E V b={p,y}) (ne : p≠y)
    (tu : t∈V.erase b) (uu : u∈V.erase b) (pt : E p t=true) (yu : E y u=true)
    (wp : ∀i∈V,0<w i) (high : mass V w<c) (rows : ∀i∈V,WeightedSD.row q E V w i=c)
    (x : ℕ→ℝ) (xn : ∀i∈V.erase b,0≤x i) :
    let U := V.erase b
    let A := reserve q E U x
    let σ : ℝ := (c:ℝ)-(mass V w:ℝ)
    (∀i∈U,i≠p → i≠y → 0≤A i) → 0≤A p →
      σ*A p≤(w b:ℝ)*(-A y) ∧ (0≤A y → A p=0 ∧ A y=0) := by
  intro U A σ others paid
  have lives {i} (par : i∈inN E V b) : i∈U :=
    mem_erase.mpr ⟨fun eq=>loopfree free (by omega) bv (eq ▸ (mem_inN.mp par).2),(mem_inN.mp par).1⟩
  have pv := lives (parents ▸ mem_insert_self p {y})
  have yv := lives (parents ▸ mem_insert_of_mem (mem_singleton_self y))
  obtain ⟨ρ,dual⟩ := realDual_of_smallRow (small _ _ (card_erase_lt_of_mem bv)
    (free.mono_set (erase_subset _ _))) ⟨p,pv⟩
  obtain ⟨_,up,uy,lp,ly⟩ := parent_prices hq free bv parents ne tu uu pt yu wp rows dual
  have sp : 0<σ := sub_pos.mpr (by exact_mod_cast high)
  have mp : (0:ℝ)<w b := by exact_mod_cast wp b bv
  have pos {i} (low : σ≤(q:ℝ)*(w b:ℝ)*ρ i) : 0<ρ i :=
    pos_of_mul_pos_right (sp.trans_le low) (mul_nonneg (Nat.cast_nonneg _) mp.le)
  have forward := tradeoff ne pv yv dual mp lp uy (pos ly) x xn others paid
  refine ⟨forward,fun yp=>?_⟩
  have rev := tradeoff ne.symm yv pv dual mp ly up (pos lp) x xn (fun i iv iy ip=>others i iv ip iy) yp
  change σ*A p≤(w b:ℝ)*(-A y) at forward
  change σ*A y≤(w b:ℝ)*(-A p) at rev
  exact ⟨le_antisymm (nonpos_of_mul_nonpos_right (forward.trans (mul_nonpos_of_nonneg_of_nonpos mp.le (neg_nonpos.mpr yp))) sp) paid,
    le_antisymm (nonpos_of_mul_nonpos_right (rev.trans (mul_nonpos_of_nonneg_of_nonpos mp.le (neg_nonpos.mpr paid))) sp) yp⟩

#print axioms on_puncture
end LeanCH.BR.Closure.TwoParentWithdrawalDual
