import checkpoints.shen_extension.PunctureLawMixture
import Mathlib.Analysis.SpecificLimits.Basic

namespace LeanCH.BR.Closure.PunctureDiscrepancy
open Finset Matrix FiniteCutInverse
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Continue from one omitted label to another in proportion to the latter's
unspent column allowance. The missing row mass is absorbed at this label. -/
noncomputable def next (B : Matrix ι ι ℝ) (x : ι→ℝ) : Matrix ι ι ℝ := fun i j =>
  if i=j then 0 else -B i j*x j/(B i i*x i)

noncomputable def stop (B : Matrix ι ι ℝ) (x : ι→ℝ) (d : ℝ) (i : ι) := d/(B i i*x i)

theorem transition (B : Matrix ι ι ℝ) (x : ι→ℝ) {d : ℝ} (positive : 0<d)
    (xp : ∀i,0<x i) (xm : ∑i,x i=1) (eq : ∀i,(B *ᵥ x) i=d)
    (off : ∀i j,i≠j → B i j≤0) (lower : ∀i j,-1≤B i j) (i : ι) :
    (∀j,0≤next B x i j) ∧ 0<stop B x d i ∧
      (∑j,next B x i j)+stop B x d i=1 ∧ (∑j,next B x i j)≤1/(1+d) := by
  classical
  let cost := ∑j∈univ.erase i,-B i j*x j
  have cn : 0≤cost := sum_nonneg (fun j hj => mul_nonneg (neg_nonneg.mpr (off i j (mem_erase.mp hj).1.symm)) (xp j).le)
  have rowSum : (∑j,B i j*x j)=d := eq i
  have exactCost : B i i*x i=d+cost := by
    dsimp only [cost]
    simp only [neg_mul,sum_neg_distrib]
    linarith only [sum_erase_add univ (fun j => B i j*x j) (mem_univ i),rowSum]
  have diagPos : 0<B i i*x i := by linarith
  have cap : cost≤1 := by
    calc
      _ ≤ ∑j∈univ.erase i,x j := sum_le_sum (fun j _ => by
        simpa using (mul_le_mul_of_nonneg_right (show -B i j≤1 by linarith [lower i j]) (xp j).le))
      _ ≤ ∑j,x j := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun j _ _ => (xp j).le)
      _ = _ := xm
  have kRow : (∑j,next B x i j)=cost/(B i i*x i) := by
    rw [←sum_erase_add univ _ (mem_univ i)]
    simp only [next,ite_true,add_zero]
    dsimp only [cost]
    rw [sum_div]
    exact sum_congr rfl fun j hj => ite_eq_right (mem_erase.mp hj).1.symm
  refine ⟨fun j => ?_,div_pos positive diagPos,?_,?_⟩
  · by_cases same : i=j
    · simp [next,same]
    · rw [next,ite_eq_right same]
      exact div_nonneg (mul_nonneg (neg_nonneg.mpr (off i j same)) (xp j).le) diagPos.le
  · rw [kRow,stop,←add_div,add_comm,←exactCost,div_self diagPos.ne']
  · rw [kRow]
    apply (div_le_div_iff₀ diagPos (by linarith : 0<1+d)).mpr
    nlinarith only [exactCost,mul_nonneg positive.le (sub_nonneg.mpr cap)]

/-- A chain repeatedly continuing through the discrepancy relation has a
geometric tail, for any finite starting mass. -/
theorem decay (K : Matrix ι ι ℝ) (kn : ∀i j,0≤K i j) {rate : ℝ}
    (rn : 0≤rate) (cap : ∀i,(∑j,K i j)≤rate) (w : ι→ℝ) (wn : ∀i,0≤w i) (n : ℕ) :
    (∀i,0≤(w ᵥ* K^n) i) ∧ (∑i,(w ᵥ* K^n) i) ≤ (∑i,w i)*rate^n := by
  classical
  induction n with
  | zero => simpa using (show (∀i,0≤w i) ∧ (∑i,w i)≤∑i,w i from ⟨wn,le_rfl⟩)
  | succ n ih =>
    rw [pow_succ,←Matrix.vecMul_vecMul]
    let v := w ᵥ* K^n
    have step : ∑j,(v ᵥ* K) j = ∑i,v i*(∑j,K i j) := by
      change (∑j,∑i,v i*K i j)=_
      rw [sum_comm]
      simp only [mul_sum]
    refine ⟨fun j => sum_nonneg (fun i _ => mul_nonneg (ih.1 i) (kn i j)),?_⟩
    change (∑j,(v ᵥ* K) j) ≤ _
    rw [step,pow_succ]
    calc
      _ ≤ ∑i,v i*rate := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (cap i) (ih.1 i))
      _ = (∑i,v i)*rate := (sum_mul _ _ _).symm
      _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right ih.2 rn

/-- At equilibrium the absorbed mass is exactly the mixture recovered from
the graph. Truncating the process after n steps leaves an explicit remainder. -/
theorem absorption (B : Matrix ι ι ℝ) (x l : ι→ℝ) {d : ℝ} (dp : 0<d)
    (xp : ∀i,0<x i) (xm : ∑i,x i=1) (lp : ∀i,0<l i)
    (eq : ∀i,(B *ᵥ x) i=d) (off : ∀i j,i≠j → B i j≤0) (lower : ∀i j,-1≤B i j)
    (balance : ∀i,l i*B i i=d+∑j∈univ.erase i,l j*(-B j i)) :
    let K := next B x
    let v := fun i => l i*(B i i*x i)/d
    (∀ i,0≤v i) ∧ ∀n i,
      l i - (∑k∈range n,(x ᵥ* K^k) i*stop B x d i) = (v ᵥ* K^n) i*stop B x d i ∧
      (v ᵥ* K^n) i*stop B x d i ≤ (∑j,v j)*(1/(1+d))^n := by
  classical
  intro K v
  have data := transition B x dp xp xm eq off lower
  have diag (i) : 0<B i i*x i := lt_of_not_ge (fun h => (div_nonpos_of_nonneg_of_nonpos dp.le h).not_gt (data i).2.1)
  have notZero (i) : B i i≠0 := fun h => (diag i).ne' (by rw [h,zero_mul])
  have vn (i) : 0≤v i := div_nonneg (mul_nonneg (lp i).le (diag i).le) dp.le
  have absorbed (i) : v i*stop B x d i=l i := by
    dsimp [v,stop]
    field_simp [dp.ne',notZero i,(xp i).ne']
  have inflow (i) : v i=x i+(v ᵥ* K) i := by
    have term (j) (ji : j≠i) : v j*K j i = (l j*(-B j i))*x i/d := by
      dsimp only [K,next,v]
      rw [ite_eq_right ji]
      field_simp [dp.ne',notZero j,(xp j).ne']
    change _=x i+∑j,v j*K j i
    rw [←sum_erase_add univ _ (mem_univ i)]
    have self : K i i=0 := by simp [K,next]
    rw [self,mul_zero,add_zero]
    have inner := sum_congr (s₁:=univ.erase i) rfl (fun j hj => term j (mem_erase.mp hj).1)
    rw [inner,←sum_div,←sum_mul]
    dsimp only [v]
    field_simp [dp.ne']
    have bal := balance i
    simp only [mul_neg] at bal
    nlinarith only [congrArg (· * x i) bal]
  have visits (n) : ∀i,v i=(∑k∈range n,(x ᵥ* K^k) i)+(v ᵥ* K^n) i := by
    intro i
    induction n with
    | zero => simp
    | succ n ih =>
      have law : v=x+v ᵥ* K := funext inflow
      have h := congrArg (fun u => (u ᵥ* K^n) i) law
      change (v ᵥ* K^n) i=((x+v ᵥ* K) ᵥ* K^n) i at h
      rw [Matrix.add_vecMul,Matrix.vecMul_vecMul,←pow_succ'] at h
      rw [sum_range_succ]
      change (v ᵥ* K^n) i=(x ᵥ* K^n) i+(v ᵥ* K^(n+1)) i at h
      linarith
  refine ⟨vn,fun n i => ⟨?_,?_⟩⟩
  · rw [←sum_mul,←absorbed]
    linarith only [congrArg (· * stop B x d i) (visits n i)]
  · have rn : 0≤1/(1+d) := by positivity
    have tail := decay K (fun i j => (data i).1 j) rn (fun i => (data i).2.2.2) v vn n
    have stopLe : stop B x d i≤1 := by
      linarith only [(data i).2.2.1,sum_nonneg (s:=univ) (fun j _ => (data i).1 j)]
    calc
      _ ≤ (v ᵥ* K^n) i := by simpa using mul_le_mul_of_nonneg_left stopLe (tail.1 i)
      _ ≤ ∑j,(v ᵥ* K^n) j := single_le_sum (fun j _ => tail.1 j) (mem_univ i)
      _ ≤ _ := tail.2

#print axioms absorption

#print axioms transition
#print axioms decay
end LeanCH.BR.Closure.PunctureDiscrepancy
