import LeanCH.BR.BRWeightedPerturb
import LeanCH.BR.BRWeightedSD

/-! Graph-level form of the zero-coordinate perturbation, on the same host
and with exactly the same edges. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 Matrix WeightedArithmetic WeightedPerturb
open scoped Matrix

def adjacencyMatrix (D : CH.Digraph) (V : Finset ℕ) : Matrix V V ℤ :=
  fun i j => if D i j = true then 1 else 0

theorem matrix_row (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (i : V) :
    (rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun j : V => w j)) i = row q D V w i := by
  rw [rational_mulVec_apply]
  unfold row outW
  simp only [adjacencyMatrix, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
    one_mul, zero_mul]
  exact congrArg (fun z : ℚ => w i + q * z)
    (Finset.sum_coe_sort V (fun j => if D i j = true then w j else 0))

theorem matrix_col (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (i : V) :
    ((fun j : V => w j) ᵥ* rationalMatrix q (adjacencyMatrix D V)) i = col q D V w i := by
  rw [rational_vecMul_apply]
  unfold col inW
  simp only [adjacencyMatrix, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
    one_mul, zero_mul]
  exact congrArg (fun z : ℚ => w i + q * z)
    (Finset.sum_coe_sort V (fun j => if D j i = true then w j else 0))

theorem outW_erase {D : CH.Digraph} {V : Finset ℕ} {x : ℕ} (hx : x ∈ V)
    (w : ℕ → ℚ) (v : ℕ) :
    outW D V w v = outW D (V.erase x) w v + if D v x = true then w x else 0 :=
  (Finset.sum_erase_add _ _ hx).symm

theorem inW_erase {D : CH.Digraph} {V : Finset ℕ} {x : ℕ} (hx : x ∈ V)
    (w : ℕ → ℚ) (v : ℕ) :
    inW D V w v = inW D (V.erase x) w v + if D x v = true then w x else 0 :=
  (Finset.sum_erase_add _ _ hx).symm

theorem outW_zero_erase {D : CH.Digraph} {V : Finset ℕ} {x : ℕ} (hx : x ∈ V)
    {w : ℕ → ℚ} (hwx : w x = 0) (v : ℕ) : outW D V w v = outW D (V.erase x) w v := by
  rw [outW_erase hx w v]
  simp [hwx]

theorem inW_zero_erase {D : CH.Digraph} {V : Finset ℕ} {x : ℕ} (hx : x ∈ V)
    {w : ℕ → ℚ} (hwx : w x = 0) (v : ℕ) : inW D V w v = inW D (V.erase x) w v := by
  rw [inW_erase hx w v]
  simp [hwx]

theorem positive_col_eq {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hSD : SelfDual q D V) {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    {v : ℕ} (hv : v ∈ V) (hvp : 0 < w v) : col q D V w v = mass V w := by
  have hc := hSD w hw hr
  have hhi : ∀ u ∈ V, w u * col q D V w u ≤ w u * mass V w := by
    intro u hu
    exact mul_le_mul_of_nonneg_left (hc u hu) (hw u hu)
  have hlo : (∑ u ∈ V, w u * mass V w) ≤ ∑ u ∈ V, w u * col q D V w u := by
    rw [← row_col_balance q D V w]
    exact Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hr u hu) (hw u hu))
  have heq := le_antisymm (Finset.sum_le_sum hhi) hlo
  have each := (Finset.sum_eq_sum_iff_of_le hhi).mp heq v hv
  exact mul_left_cancel₀ (ne_of_gt hvp) each

/-- A one-zero violation over an internally self-dual support yields a
strictly positive strict-row weighting on the SAME graph and vertex set. -/
theorem positive_weighting_of_one_zero {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {x : ℕ} (hx : x ∈ V) (hloop : D x x = false)
    (hcore : SelfDual q D (V.erase x)) (w : ℕ → ℚ)
    (hw : ∀ v ∈ V.erase x, 0 < w v) (hwx : w x = 0) (hsum : mass V w = 1)
    (hr : ∀ v ∈ V, 1 ≤ row q D V w v) (hbad : 1 < col q D V w x) :
    ∃ p : ℕ → ℚ, (∀ v ∈ V, 0 < p v) ∧ mass V p = 1 ∧
      ∀ v ∈ V, 1 < row q D V p v := by
  let S := V.erase x
  have hsub : S ⊆ V := Finset.erase_subset _ _
  have hmass : mass S w = 1 := by
    have hh := Finset.sum_erase_add V w hx
    change mass S w + w x = mass V w at hh
    rw [hwx, hsum] at hh
    linarith
  have hrows : ∀ v ∈ S, mass S w ≤ row q D S w v := by
    intro v hv
    have hh := hr v (hsub hv)
    simpa only [row, outW_zero_erase hx hwx, hmass] using hh
  have hrS : ∀ v ∈ S, row q D S w v = 1 := by
    intro v hv
    exact (positive_row_eq hcore (fun a ha => (hw a ha).le) hrows hv (hw v hv)).trans hmass
  have hcS : ∀ v ∈ S, col q D S w v = 1 := by
    intro v hv
    exact (positive_col_eq hcore (fun a ha => (hw a ha).le) hrows hv (hw v hv)).trans hmass
  let A := adjacencyMatrix D S
  let a : S → ℤ := fun i => if D x i = true then 1 else 0
  let b : S → ℤ := fun i => if D i x = true then 1 else 0
  have hrM : rationalMatrix q A *ᵥ (fun i : S => w i) = fun _ => 1 := by
    funext i
    exact (matrix_row q D S w i).trans (hrS i i.property)
  have hcM : (fun i : S => w i) ᵥ* rationalMatrix q A = fun _ => 1 := by
    funext i
    exact (matrix_col q D S w i).trans (hcS i i.property)
  have ha : 1 ≤ (q : ℚ) * ∑ i : S, (a i : ℚ) * w i := by
    have hh := hr x hx
    rw [row, hwx, outW_zero_erase hx hwx] at hh
    change 1 ≤ 0 + q * outW D S w x at hh
    rw [outW, ← Finset.sum_coe_sort] at hh
    simpa only [zero_add, outW, a, Int.cast_ite, Int.cast_one, Int.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_coe_sort] using hh
  have hb : 1 < (q : ℚ) * ∑ i : S, (b i : ℚ) * w i := by
    rw [col, hwx, inW_zero_erase hx hwx] at hbad
    change 1 < 0 + q * inW D S w x at hbad
    rw [inW, ← Finset.sum_coe_sort] at hbad
    simpa only [zero_add, inW, b, Int.cast_ite, Int.cast_one, Int.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_coe_sort] using hbad
  obtain ⟨p, t, hp, ht, htotal, hpr, htr⟩ := lift_zero_vertex hq A
    (fun i : S => w i) (fun i => hw i i.property)
    (by simpa only [mass, Finset.sum_coe_sort] using hmass) hrM hcM a b ha hb
  let z : ℕ → ℚ := fun v => if v = x then t else if hv : v ∈ S then p ⟨v, hv⟩ else 0
  have hzx : z x = t := by simp [z]
  have hzS : ∀ i : S, z i = p i := by
    intro i
    have hin := i.property
    have hne : (i : ℕ) ≠ x := (Finset.mem_erase.mp hin).1
    simp [z, hne, hin]
  have hmassz : mass S z = ∑ i : S, p i := by
    rw [mass, ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl (fun i hi => hzS i)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro v hv
    by_cases he : v = x
    · simpa only [he, hzx] using ht
    · have hvS : v ∈ S := Finset.mem_erase.mpr ⟨he, hv⟩
      simpa only [hzS ⟨v, hvS⟩] using hp ⟨v, hvS⟩
  · have hh := Finset.sum_erase_add V z hx
    change mass S z + z x = mass V z at hh
    rw [hmassz, hzx, htotal] at hh
    exact hh.symm
  · intro v hv
    by_cases he : v = x
    · subst v
      have heq : outW D S z x = ∑ i : S, (a i : ℚ) * p i := by
        rw [outW, ← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro i hi
        simp [a, hzS i]
      rw [row, outW_erase hx z x, hloop]
      simp only [Bool.false_eq_true, ite_false, add_zero, hzx]
      change 1 < t + q * outW D S z x
      rw [heq]
      exact htr
    · have hvS : v ∈ S := Finset.mem_erase.mpr ⟨he, hv⟩
      have heq : (rationalMatrix q A *ᵥ p) ⟨v, hvS⟩ = row q D S z v := by
        have hvect : p = (fun i : S => z i) := funext (fun i => (hzS i).symm)
        rw [hvect]
        exact matrix_row q D S z ⟨v, hvS⟩
      have hh := hpr ⟨v, hvS⟩
      rw [heq] at hh
      simp only [row, outW_erase hx z v, hzx]
      by_cases hedge : D v x = true
      · simpa [b, hedge, row, mul_add, mul_assoc, add_assoc] using hh
      · simpa [b, hedge, row] using hh

end LeanCH.BR.WeightedSD
