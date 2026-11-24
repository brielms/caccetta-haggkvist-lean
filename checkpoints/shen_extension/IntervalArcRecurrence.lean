import checkpoints.shen_extension.SharedArcFlatArithmetic
import Mathlib.Data.Nat.Periodic

namespace LeanCH.BR.Closure.IntervalArcRecurrence
open Matrix Finset

def pulse (n i : ℕ) : ℝ := if i % n = 0 then 1 else 0

/-- Multiplication by -q modulo qr+1 orders the interval steps as
1,1+q,...,1+(r-1)q. The row law below is just the labelled arc table. -/
structure Rows {I : Type*} [Fintype I] (q r : ℕ) (label : ℕ → I)
    (R : Matrix I I ℝ) : Prop where
  period : ∀ i, label (i+(q*r+1))=label i
  distinct : ∀ i t, label (i+t)=label i ↔ t%(q*r+1)=0
  row : ∀ i (x : I → ℝ), (R *ᵥ x) (label i) =
    x (label i)+(q:ℝ)*∑ s ∈ range r, x (label (i+1+q*s))

theorem of_entries {I : Type*} [Fintype I] [DecidableEq I]
    {q r : ℕ} {label : ℕ→I} {R : Matrix I I ℝ}
    (per : ∀ i, label (i+(q*r+1))=label i)
    (distinct : ∀ i t, label (i+t)=label i ↔ t%(q*r+1)=0)
    (entries : ∀ i j, R (label i) j = (if label i=j then 1 else 0)+
      (q:ℝ)*∑ s ∈ range r, (if label (i+1+q*s)=j then 1 else 0)) : Rows q r label R := by
  refine ⟨per,distinct,fun i x => ?_⟩
  simp only [mulVec,dotProduct,entries,add_mul,sum_add_distrib,mul_assoc,sum_mul,←mul_sum]
  rw [sum_comm (s:=univ) (t:=range r)]
  simp [ite_mul]

def Equation (q n : ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ i, g (i+q)-(q:ℝ)*g (i+1)+((q:ℝ)-1)*g i =
    (q:ℝ)*(pulse n (i+1+q)-pulse n (i+1))

/-- A periodic solution of the homogeneous recurrence attains its
maximum. Strict deficit propagates forward one step, so it is constant. -/
theorem unique {q n : ℕ} (hq : 2≤q) (hn : 0<n) {g h : ℕ→ℝ}
    (pg : Function.Periodic g n) (ph : Function.Periodic h n)
    (eg : Equation q n g) (eh : Equation q n h) (i : ℕ) :
    g i-g 0=h i-h 0 := by
  let d := fun i => g i-h i
  have pd : Function.Periodic d n := fun i => by simp only [d,pg i,ph i]
  obtain ⟨m,_,maximal⟩ := exists_max_image (range n) d ⟨0,mem_range.mpr hn⟩
  have le (j : ℕ) : d j≤d m := pd.map_mod_nat j ▸ maximal _ (mem_range.mpr (Nat.mod_lt _ hn))
  have eq (i : ℕ) : d i=d m := by
    by_contra diff
    have lt := lt_of_le_of_ne (le i) diff
    have always (j : ℕ) : d (i+j)<d m := by
      induction j with
      | zero => simpa using lt
      | succ j ih =>
        have p : 0<(q:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (by omega : 1<q))
        have strict := mul_lt_mul_of_pos_left ih p
        have recur : d (i+j+q) - (q:ℝ)*d (i+j+1)+((q:ℝ)-1)*d (i+j)=0 := by
          dsimp only [d]; linear_combination eg (i+j) - eh (i+j)
        have next : (q:ℝ)*d (i+j+1)<(q:ℝ)*d m := by
          linarith only [recur,strict,le (i+j+q)]
        exact lt_of_mul_lt_mul_left next (Nat.cast_nonneg q)
    have modlt := Nat.mod_lt i hn
    have bad := always (m+(n-i%n))
    have atM : d (i+(m+(n-i%n)))=d m := by
      rw [←pd.map_mod_nat (i+(m+(n-i%n))),←pd.map_mod_nat m]
      congr 1
      calc
        _ = ((i%n)+(m+(n-i%n)))%n := by simp
        _ = (m+n)%n := by congr 1; omega
        _ = m%n := Nat.add_mod_right _ _
    exact bad.ne atM
  have a := (eq i).trans (eq 0).symm
  dsimp only [d] at a; linarith

noncomputable def column {I : Type*} (q : ℕ) (label : ℕ→I) (L : Matrix I I ℝ) (c i : ℕ) :=
  (q:ℝ)*L (label (c+i+1)) (label c)

theorem column_equation {I : Type*} [Fintype I] [DecidableEq I] {q r : ℕ}
    {label : ℕ→I} {R L : Matrix I I ℝ} (rows : Rows q r label R) (inverse : R*L=1) (c : ℕ) :
    Function.Periodic (column q label L c) (q*r+1) ∧ Equation q (q*r+1) (column q label L c) := by
  constructor
  · intro i; simp only [column,show c+(i+(q*r+1))+1=(c+i+1)+(q*r+1) by omega,rows.period]
  intro i
  let x (j : ℕ) := L (label (c+j)) (label c)
  have row (j : ℕ) : x j+(q:ℝ)*(∑ s ∈ range r, x (j+1+q*s))=pulse (q*r+1) j := by
    have h := rows.row (c+j) (fun u => L u (label c))
    have h' := congrArg (fun M : Matrix I I ℝ => M (label (c+j)) (label c)) inverse
    change (R *ᵥ fun u => L u (label c)) (label (c+j)) = _ at h'
    simp only [h,Matrix.one_apply,rows.distinct] at h'
    simpa only [x,pulse,Nat.add_assoc] using h'
  let seq (s : ℕ) := x ((i+1)+1+q*s)
  have tel := Finset.sum_range_succ' seq r
  rw [sum_range_succ] at tel
  have last : seq r=x (i+1) := by
    dsimp [seq,x]; rw [show c+(i+1+1+q*r)=(c+(i+1))+(q*r+1) by omega,rows.period]
  have shift : (∑ s ∈ range r, x (i+1+q+1+q*s))=∑ s ∈ range r, seq (s+1) := by
    apply sum_congr rfl; intro s _; dsimp [seq]; rw [Nat.mul_succ]; congr 1; omega
  have h0 := row (i+1)
  have hq := row (i+1+q)
  change x (i+1)+(q:ℝ)*(∑ s ∈ range r, seq s)=_ at h0
  rw [shift] at hq
  rw [last] at tel
  change (∑ s ∈ range r, seq s) + x (i+1) = (∑ s ∈ range r, seq (s+1)) + x (i+2) at tel
  simp only [column,show c+(i+q)+1=c+(i+1+q) by omega,show c+(i+1)+1=c+(i+2) by omega,
    show c+i+1=c+(i+1) by omega]
  change (q:ℝ)*x (i+1+q)-(q:ℝ)*((q:ℝ)*x (i+2))+((q:ℝ)-1)*((q:ℝ)*x (i+1))=_
  linear_combination (q:ℝ)*hq - (q:ℝ)*h0 + (q:ℝ)^2*tel

/-- Any periodic scalar solution supplies the exact local tensor score
at every displacement. It uses q and n only; its additive constant drops out. -/
theorem score_eq {I : Type*} [Fintype I] [DecidableEq I] {q r : ℕ} (hq : 2≤q)
    {label : ℕ→I} {R L : Matrix I I ℝ} (rows : Rows q r label R) (inv : R*L=1)
    (g : ℕ→ℝ) (per : Function.Periodic g (q*r+1)) (eqn : Equation q (q*r+1) g)
    (a t : ℕ) (ht : t≤q*r+1) :
    let v := label (a+1)
    let k := label (a+t)
    let b := label (a+t+1)
    1+(q:ℝ)*(L v k-L v (label a)+L b (label a)-L b k) =
      1+(g t-g 0)+(g (q*r+1-t)-g 0) := by
  intro v k b
  have A := column_equation rows inv a
  have K := column_equation rows inv (a+t)
  have one := unique hq (by omega) A.1 per A.2 eqn t
  have two := unique hq (by omega) K.1 per K.2 eqn (q*r+1-t)
  simp only [column,Nat.add_zero] at one two
  rw [show a+t+(q*r+1-t)+1=(a+1)+(q*r+1) by omega,rows.period] at two
  dsimp only [v,k,b]; linear_combination one + two

end LeanCH.BR.Closure.IntervalArcRecurrence
#print axioms LeanCH.BR.Closure.IntervalArcRecurrence.score_eq
