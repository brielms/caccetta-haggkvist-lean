module

public import LeanCH.CompromiseFair

set_option linter.style.header false

/-! Whole-out-neighbourhood packing certificates. The left-vector hypothesis
is explicit: this module does not invoke or formalize Perron--Frobenius. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseFair
public section

namespace CH.CompromisePacking

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def capacity (v z : V) : ℝ :=
  (if z ∈ second adj v then 1 else 0) + (if adj z v then 1 else 0)

@[expose] def rowImage (C : V → V → ℝ) (v z : V) : ℝ :=
  ∑ y ∈ inN adj z, C v y

@[expose] def Packed (C : V → V → ℝ) : Prop :=
  (∀ v y, 0 ≤ C v y) ∧ ∀ v z, rowImage adj C v z ≤ capacity adj v z

theorem capacity_transpose (p : V → ℝ) (z : V) :
    ∑ v, p v * capacity adj v z = mass p (secondIn adj z) + mass p (outN adj z) := by
  have hs : univ.filter (fun v => z ∈ second adj v) = secondIn adj z := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_second, mem_secondIn]
    constructor <;> rintro ⟨hne, ha, hp⟩
    · exact ⟨hne.symm, ha, hp⟩
    · exact ⟨hne.symm, ha, hp⟩
  simp only [capacity, mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib]
  rw [← sum_filter, hs, ← sum_filter]
  rw [show univ.filter (adj z ·) = outN adj z by ext; simp]
  rfl

omit [DecidableEq V] in
theorem image_transpose (p : V → ℝ) (C : V → V → ℝ) (z : V) :
    ∑ v, p v * rowImage adj C v z =
      ∑ y ∈ inN adj z, ∑ v, p v * C v y := by
  simp only [rowImage, mul_sum]
  exact sum_comm

/-- A nonnegative left vector with growth at least two is a fair certificate. -/
theorem fair_of_packing (C : V → V → ℝ) (hC : Packed adj C)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hne : ∃ v, 0 < p v)
    (growth : ∀ y, 2 * p y ≤ ∑ v, p v * C v y) : Fair adj p := by
  refine ⟨hp, hne, ?_⟩
  intro z
  have hl := sum_le_sum (s := inN adj z) (fun y _ => growth y)
  have hr := sum_le_sum (s := (univ : Finset V)) (fun v _ =>
    mul_le_mul_of_nonneg_left (hC.2 v z) (hp v))
  rw [capacity_transpose adj p z, image_transpose adj p C z] at hr
  rw [← mul_sum] at hl
  change 2 * mass p (inN adj z) ≤ _ at hl
  linarith

theorem compromise_of_packing (C : V → V → ℝ) (hC : Packed adj C)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hne : ∃ v, 0 < p v)
    (growth : ∀ y, 2 * p y ≤ ∑ v, p v * C v y)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 < p v ∧ 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v :=
  compromise_of_fair adj p w (fair_of_packing adj C hC p hp hne growth) hw

/-- If every supported row meets one common target, that target bounds row mass. -/
theorem row_sum_bound (C : V → V → ℝ) (hC : Packed adj C)
    (v z : V)
    (common : ∀ y, (∀ t, adj y t → 0 < capacity adj v t) → adj y z) :
    ∑ y, C v y ≤ capacity adj v z := by
  have hzero (y : V) (hy : ¬ adj y z) : C v y = 0 := by
    by_contra hne
    have hp : 0 < C v y := lt_of_le_of_ne (hC.1 v y) (Ne.symm hne)
    apply hy
    apply common y
    intro t hyt
    have hterm : C v y ≤ rowImage adj C v t := by
      apply single_le_sum (fun a _ => hC.1 v a)
      simpa using hyt
    exact hp.trans_le (hterm.trans (hC.2 v t))
  have heq : ∑ y, C v y = rowImage adj C v z := by
    unfold rowImage
    symm
    apply sum_subset (subset_univ _)
    intro y _ hy
    exact hzero y (by simpa using hy)
  rw [heq]
  exact hC.2 v z

omit [DecidableEq V] in
/-- Row mass at most one rules out a nonzero left vector growing by two. -/
theorem no_left_growth (C : V → V → ℝ) (rows : ∀ v, ∑ y, C v y ≤ 1)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (growth : ∀ y, 2 * p y ≤ ∑ v, p v * C v y) : ∀ v, p v = 0 := by
  have hg := sum_le_sum (s := (univ : Finset V)) (fun y _ => growth y)
  have hr := sum_le_sum (s := (univ : Finset V)) (fun v _ =>
    mul_le_mul_of_nonneg_left (rows v) (hp v))
  simp only [mul_one, mul_sum] at hr
  rw [sum_comm] at hg
  rw [← mul_sum] at hg
  have hsum : (∑ v, p v) ≤ 0 := by linarith
  intro v
  have hterm : p v ≤ ∑ y, p y := single_le_sum (fun y _ => hp y) (mem_univ v)
  exact le_antisymm (hterm.trans hsum) (hp v)

end CH.CompromisePacking

#print axioms CH.CompromisePacking.fair_of_packing
#print axioms CH.CompromisePacking.compromise_of_packing
#print axioms CH.CompromisePacking.row_sum_bound
#print axioms CH.CompromisePacking.no_left_growth
