import checkpoints.shen_extension.GlobalFamilyDual

namespace LeanCH.BR.Closure.RecipientBalance
open Finset BRq2 BRq3 BR45 WeightedSD

/-- Rows that see the first label and miss the second. -/
def exclusive (E : CH.Digraph) (V : Finset ℕ) (y r : ℕ) :=
  V.filter (fun i => E i y = true ∧ E i r = false)

private theorem difference (E : CH.Digraph) (V : Finset ℕ) (p : ℕ → ℚ) (y r : ℕ) :
    inW E V p y - inW E V p r = mass (exclusive E V y r) p - mass (exclusive E V r y) p := by
  unfold inW mass exclusive
  simp only [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  cases E i y <;> cases E i r <;> simp_all

/-- Sending weight from y to r trades two exact sets of parents. Common
parents drop out. The diagonal term measures the change of label weight. -/
theorem balance {q E V p c} (cols : ∀ i ∈ V, WeightedSD.col q E V p i = c)
    {y r} (hy : y ∈ V) (hr : r ∈ V) :
    (q:ℚ) * mass (exclusive E V y r) p + p y =
      (q:ℚ) * mass (exclusive E V r y) p + p r := by
  have a := cols y hy
  have b := cols r hr
  unfold WeightedSD.col at a b
  have d := congrArg (fun t : ℚ => (q:ℚ)*t) (difference E V p y r)
  change _ * (_ - _) = _ * (_ - _) at d
  linarith only [a,b,d]

/-- If the marked losing row outweighs both the label increment and the
exclusive gaining parents that will be deleted, some surviving row sees the
recipient and misses the lost head. The forbidden set is arbitrary. -/
theorem surviving_parent {q E V p c} (pos : ∀ i ∈ V, 0 ≤ p i)
    (cols : ∀ i ∈ V, WeightedSD.col q E V p i = c) {b y r}
    (hy : y∈V) (hr : r∈V) (hb : b∈exclusive E V y r) (Z : Finset ℕ)
    (credit : p r + (q:ℚ)*mass (exclusive E V r y ∩ Z) p < p y + (q:ℚ)*p b) :
    ∃ i∈V, i∉Z ∧ E i r=true ∧ E i y=false := by
  have le : p b ≤ mass (exclusive E V y r) p :=
    single_le_sum (fun i hi => pos i (mem_filter.mp hi).1) hb
  have eqn := balance cols hy hr
  by_contra! none
  have sub : exclusive E V r y ⊆ Z := by
    intro i hi
    obtain ⟨iv,ir,iy⟩ := mem_filter.mp hi
    by_contra iz
    exact (none i iv iz ir) iy
  rw [inter_eq_left.mpr sub] at credit
  linarith only [credit,eqn,mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q : (0:ℚ) ≤ q)]

/-- Summing along a closed sequence of *labels* cancels the diagonal terms.
The next label is specified by a permutation, which may have several orbits. -/
theorem closed {q E V p c} (cols : ∀ i∈V, WeightedSD.col q E V p i=c)
    {ι : Type*} [Fintype ι] (next : Equiv.Perm ι) (label : ι → ℕ)
    (inside : ∀ i, label i∈V) :
    (q:ℚ) * (∑ i, mass (exclusive E V (label i) (label (next i))) p) =
      (q:ℚ) * ∑ i, mass (exclusive E V (label (next i)) (label i)) p := by
  classical
  have h := sum_congr (rfl : (univ : Finset ι) = univ) (fun i _ =>
    balance cols (inside i) (inside (next i)))
  simp only [sum_add_distrib, ← mul_sum] at h
  have perm := Equiv.sum_comp next (fun i => p (label i))
  linarith only [h,perm]

#print axioms balance
#print axioms surviving_parent
#print axioms closed
end LeanCH.BR.Closure.RecipientBalance
