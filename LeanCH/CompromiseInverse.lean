module

public import LeanCH.CompromiseCritical
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-! A strict counterweight that cannot lose any coordinate makes the
coefficient matrix inverse nonpositive. This is the square minimally
semipositive matrix criterion, proved here by a finite ratio argument.
The graph application needs deletion certificates only in the original
orientation. -/

open Finset CH.CompromiseGame
open scoped Matrix
public section

namespace CH.CompromiseInverse

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def Full (M : V → V → ℝ) : Prop :=
  ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → (∀ v, row M w v < 0) → ∀ v, 0 < w v

omit [DecidableEq V] in
theorem row_sub (M : V → V → ℝ) (x y : V → ℝ) (v : V) :
    row M (fun u => x u - y u) v = row M x v - row M y v := by
  simp [row, mul_sub, sum_sub_distrib]

omit [DecidableEq V] in
theorem row_scale (M : V → V → ℝ) (x : V → ℝ) (r : ℝ) (v : V) :
    row M (fun u => r * x u) v = r * row M x v := by
  simp only [row, mul_left_comm, mul_sum]

omit [DecidableEq V] in
/-- A signed vector whose image is nonnegative must be nonpositive. -/
theorem inverse_order (M : V → V → ℝ) (full : Full M)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ row M x v) : ∀ v, x v ≤ 0 := by
  have wp := full w hw bad
  intro a
  by_contra ha
  have xa : 0 < x a := lt_of_not_ge ha
  obtain ⟨k, _, hmax⟩ := exists_max_image (univ : Finset V)
    (fun v => x v / w v) ⟨a, mem_univ a⟩
  let r := x k / w k
  have rp : 0 < r := (div_pos xa (wp a)).trans_le (hmax a (mem_univ a))
  let y := fun v => r * w v - x v
  have yn (v : V) : 0 ≤ y v := by
    have hr : x v / w v ≤ r := hmax v (mem_univ v)
    exact sub_nonneg.mpr ((div_le_iff₀ (wp v)).mp hr)
  have yz : y k = 0 := by dsimp [y, r]; field_simp [ne_of_gt (wp k)]; ring
  have ybad (v : V) : row M y v < 0 := by
    change row M (fun u => r * w u - x u) v < 0
    rw [row_sub, row_scale]
    have hn := mul_neg_of_pos_of_neg rp (bad v)
    linarith [hx v]
  have hp := full y yn ybad k
  linarith

omit [DecidableEq V] in
theorem row_injective (M : V → V → ℝ) (full : Full M)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0) :
    Function.Injective (row M) := by
  intro x y he
  have hxy (v : V) : row M (fun u => x u - y u) v = 0 := by
    rw [row_sub, congrFun he v, sub_self]
  have hyx (v : V) : row M (fun u => y u - x u) v = 0 := by
    rw [row_sub, congrFun he v, sub_self]
  have hn := inverse_order M full w hw bad _ (fun v => by rw [hxy])
  have hp := inverse_order M full w hw bad _ (fun v => by rw [hyx])
  funext v
  linarith [hn v, hp v]

theorem matrix_isUnit (M : Matrix V V ℝ) (full : Full M)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0) : IsUnit M := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  exact row_injective M full w hw bad

theorem inverse_nonpos (M : Matrix V V ℝ) (full : Full M)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0) :
    ∀ i j, M⁻¹ i j ≤ 0 := by
  have unit := matrix_isUnit M full w hw bad
  have inv := M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp unit)
  intro i j
  apply inverse_order M full w hw bad (fun v => M⁻¹ v j) _ i
  intro v
  change 0 ≤ (M * M⁻¹) v j
  rw [inv]
  by_cases h : v = j <;> simp [Matrix.one_apply, h]

omit [DecidableEq V] in
/-- Even a signed reverse counterweight is positive: no reverse deletion
hypothesis is needed. -/
theorem reverse_positive (M : Matrix V V ℝ) (full : Full M)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0)
    (p : V → ℝ) (pb : ∀ u, col M p u < 0) : ∀ u, 0 < p u := by
  classical
  have unit := matrix_isUnit M full w hw bad
  have inv := M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp unit)
  have sign := inverse_nonpos M full w hw bad
  let B : Matrix V V ℝ := M⁻¹
  intro u
  have hn : ∃ v, M⁻¹ v u < 0 := by
    by_contra h
    push Not at h
    have hz (v : V) : M⁻¹ v u = 0 := le_antisymm (sign v u) (h v)
    have he := congrArg (fun A : Matrix V V ℝ => A u u) inv
    simp [Matrix.mul_apply, hz] at he
  have he : col B (col M p) u = p u := by
    change ((p ᵥ* M) ᵥ* M⁻¹) u = p u
    rw [Matrix.vecMul_vecMul, inv, Matrix.vecMul_one]
  rw [← he]
  apply sum_pos'
  · intro v _
    exact mul_nonneg_of_nonpos_of_nonpos (pb v).le (sign v u)
  · obtain ⟨v, hv⟩ := hn
    exact ⟨v, mem_univ v, mul_pos_of_neg_of_neg (pb v) hv⟩

omit [DecidableEq V] in
/-- One-sided full support suffices for strictly positive probability
weights equalizing the matrix and its transpose at the same negative value. -/
theorem two_sided_of_full [Nonempty V] (M : Matrix V V ℝ) (full : Full M)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, row M w0 v < 0) :
    ∃ w ∈ simplex, ∃ p ∈ simplex, ∃ c : ℝ, c < 0 ∧
      (∀ v, 0 < w v) ∧ (∀ v, 0 < p v) ∧
        (∀ v, row M w v = c) ∧ (∀ u, col M p u = c) := by
  classical
  obtain ⟨w1, hw1, hb1⟩ := normalize_bad M w0 hw0 bad0
  apply critical_two_sided M w1 hw1 hb1
  · exact fun w hw hb => full w hw.1 hb
  · exact fun p _ pb => reverse_positive M full w0 hw0 bad0 p pb

@[expose] def DeletedLeft (M : V → V → ℝ) : Prop :=
  ∀ x, ∃ p ∈ simplex, p x = 0 ∧ ∀ u, u ≠ x → 0 ≤ col M p u

omit [DecidableEq V] in
theorem full_of_deletedLeft (M : V → V → ℝ) (deleted : DeletedLeft M) : Full M := by
  classical
  intro w hw hb x
  obtain ⟨p, hp, _, cols⟩ := deleted x
  by_contra h
  have wx : w x = 0 := le_antisymm (le_of_not_gt h) (hw x)
  have neg := payoff_neg M w p hp hb
  have nonneg : 0 ≤ payoff M w p := by
    rw [payoff_transpose]
    apply sum_nonneg
    intro u _
    by_cases hu : u = x
    · simp [hu, wx]
    · exact mul_nonneg (hw u) (cols u hu)
  linarith

omit [DecidableEq V] in
theorem atom_bound (M : V → V → ℝ) (deleted : DeletedLeft M)
    (b : ℝ) (lower : ∀ v u, -b ≤ M v u)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (c : ℝ)
    (constant : ∀ v, row M w v = c) : ∀ x, -c ≤ b * w x := by
  classical
  intro x
  obtain ⟨p, hp, _, cols⟩ := deleted x
  have pair : c = ∑ u, w u * col M p u := by
    rw [← payoff_transpose]
    simp [payoff, constant, ← sum_mul, hp.2]
  have retained : 0 ≤ ∑ u ∈ univ.erase x, w u * col M p u := by
    exact sum_nonneg (fun u hu => mul_nonneg (hw u) (cols u (mem_erase.mp hu).1))
  have omitted : -b ≤ col M p x := by
    have h := sum_le_sum (s := (univ : Finset V))
      (fun v _ => mul_le_mul_of_nonneg_left (lower v x) (hp.1 v))
    simpa [col, ← sum_mul, hp.2] using h
  have hs := sum_erase_add (univ : Finset V) (fun u => w u * col M p u) (mem_univ x)
  have hm := mul_le_mul_of_nonneg_left omitted (hw x)
  nlinarith

omit [DecidableEq V] in
theorem order_bound (M : V → V → ℝ) (deleted : DeletedLeft M)
    (b : ℝ) (lower : ∀ v u, -b ≤ M v u)
    (w : V → ℝ) (hw : w ∈ simplex) (c : ℝ)
    (constant : ∀ v, row M w v = c) : (Fintype.card V : ℝ) * (-c) ≤ b := by
  classical
  have h := sum_le_sum (s := (univ : Finset V))
    (fun x _ => atom_bound M deleted b lower w hw.1 c constant x)
  simpa [sum_const, nsmul_eq_mul, ← mul_sum, hw.2] using h

open CH.CompromiseDeletion CH.CompromiseCritical

variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def matrix : Matrix V V ℝ := Matrix.of (coefficient adj)

theorem graph_full (deleted : DeletedFair adj) : Full (coefficient adj) := by
  intro w hw hb
  exact deleted_fair_full_support adj deleted w hw
    (fun v => by simpa [row_coefficient] using hb v)

/-- A graph counterweight together with fair certificates for each deleted
graph forces an invertible, inverse-nonpositive compromise matrix. -/
theorem graph_inverse_nonpos (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0) :
    IsUnit (matrix adj) ∧ ∀ i j, (matrix adj)⁻¹ i j ≤ 0 := by
  have hb (v : V) : row (coefficient adj) w v < 0 := by simpa [row_coefficient] using bad v
  exact ⟨matrix_isUnit _ (graph_full adj deleted) w hw hb,
    inverse_nonpos _ (graph_full adj deleted) w hw hb⟩

theorem graph_two_sided [Nonempty V] (deleted : DeletedFair adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) :
    ∃ w ∈ simplex, ∃ p ∈ simplex, ∃ c : ℝ, c < 0 ∧
      (∀ v, 0 < w v) ∧ (∀ v, 0 < p v) ∧
        (∀ v, surplus adj w v = c) ∧ (∀ v, surplus (fun a b => adj b a) p v = c) := by
  obtain ⟨w, hw, p, hp, c, cn, wp, pp, rows, cols⟩ :=
    two_sided_of_full (coefficient adj) (graph_full adj deleted) w0 hw0
      (fun v => by simpa [row_coefficient] using bad0 v)
  refine ⟨w, hw, p, hp, c, cn, wp, pp, ?_, ?_⟩
  · intro v
    simpa [row_coefficient] using rows v
  · intro v
    rw [← slack_reverse adj p v, ← col_coefficient adj p v]
    exact cols v

end CH.CompromiseInverse

#print axioms CH.CompromiseInverse.inverse_order
#print axioms CH.CompromiseInverse.matrix_isUnit
#print axioms CH.CompromiseInverse.inverse_nonpos
#print axioms CH.CompromiseInverse.reverse_positive
#print axioms CH.CompromiseInverse.two_sided_of_full
#print axioms CH.CompromiseInverse.full_of_deletedLeft
#print axioms CH.CompromiseInverse.atom_bound
#print axioms CH.CompromiseInverse.order_bound
#print axioms CH.CompromiseInverse.graph_inverse_nonpos
#print axioms CH.CompromiseInverse.graph_two_sided
