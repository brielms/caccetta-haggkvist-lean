module

public import LeanCH.CompromiseInverse

set_option linter.style.header false

/-! The CH linear program, its deletion certificates, and its positive
two-weight normal form. The LP property of every deleted graph is an
explicit hypothesis; no general CH theorem is asserted. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.CompromiseInverse
public section

namespace CH.LinearProgram

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def matrix : Matrix V V ℝ :=
  Matrix.of (fun v u => (1 : ℝ) - (if u = v then 1 else 0) - (if adj v u then 3 else 0))

omit [DecidableEq V] in
theorem out_sum (w : V → ℝ) (v : V) :
    outWeight adj w v = ∑ u, if adj v u then w u else 0 := by
  have he : outN adj v = univ.filter (adj v ·) := by ext; simp
  simp [outWeight, mass, he, sum_filter]

omit [DecidableEq V] in
theorem in_sum (p : V → ℝ) (u : V) :
    inWeight adj p u = ∑ v, if adj v u then p v else 0 := by
  have he : inN adj u = univ.filter (adj · u) := by ext; simp
  simp [inWeight, mass, he, sum_filter]

theorem row_matrix (w : V → ℝ) (v : V) :
    row (matrix adj) w v = (∑ u, w u) - w v - 3 * outWeight adj w v := by
  have he (u : V) : matrix adj v u * w u =
      w u - (if u = v then w u else 0) - 3 * (if adj v u then w u else 0) := by
    simp only [matrix, Matrix.of_apply]
    split_ifs <;> ring
  simp only [row, he, sum_sub_distrib, ← mul_sum]
  simp [← out_sum adj w v]

theorem col_matrix (p : V → ℝ) (u : V) :
    col (matrix adj) p u = (∑ v, p v) - p u - 3 * inWeight adj p u := by
  have he (v : V) : p v * matrix adj v u =
      p v - (if v = u then p v else 0) - 3 * (if adj v u then p v else 0) := by
    simp only [matrix, Matrix.of_apply]
    by_cases h : v = u
    · subst v
      by_cases ha : adj u u
      · simp [ha, mul_comm]
      · simp [ha]
    · by_cases ha : adj v u
      · simp [h, Ne.symm h, ha]
        ring
      · simp [h, Ne.symm h, ha]
  simp only [col, he, sum_sub_distrib, ← mul_sum]
  simp [← in_sum adj p u]

omit [Fintype V] in
theorem matrix_lower (noLoop : ∀ v, ¬ adj v v) : ∀ v u, -2 ≤ matrix adj v u := by
  intro v u
  by_cases h : u = v
  · subst u
    simp [matrix, noLoop v]
  · by_cases ha : adj v u <;> norm_num [matrix, h, ha]

@[expose] def DeletedLP : Prop :=
  ∀ x : V, ∃ p ∈ simplex, p x = 0 ∧ ∀ u, u ≠ x → p u + 3 * inWeight adj p u ≤ 1

theorem deleted_left (deleted : DeletedLP adj) : DeletedLeft (matrix adj) := by
  intro x
  obtain ⟨p, hp, px, cols⟩ := deleted x
  refine ⟨p, hp, px, ?_⟩
  intro u hu
  rw [col_matrix, hp.2]
  linarith [cols u hu]

omit [DecidableEq V] in
theorem lp_iff_distribution [Nonempty V] :
    (∀ w : V → ℝ, (∀ v, 0 ≤ w v) →
      ∃ v, w v + 3 * outWeight adj w v ≤ ∑ u, w u) ↔
    ∃ p ∈ simplex, ∀ u, p u + 3 * inWeight adj p u ≤ 1 := by
  classical
  constructor
  · intro good
    have hno : ¬ ∃ w ∈ simplex, ∀ v, row (matrix adj) w v < 0 := by
      rintro ⟨w, hw, bad⟩
      obtain ⟨v, hv⟩ := good w hw.1
      have hb := bad v
      rw [row_matrix] at hb
      linarith
    obtain ⟨p, hp, cols⟩ := (fair_iff_no_bad (matrix adj)).mpr hno
    refine ⟨p, hp, ?_⟩
    intro u
    have h := cols u
    rw [col_matrix, hp.2] at h
    linarith
  · rintro ⟨p, hp, cols⟩ w hw
    by_contra h
    push Not at h
    have bad (v : V) : row (matrix adj) w v < 0 := by rw [row_matrix]; linarith [h v]
    have hn := payoff_neg (matrix adj) w p hp bad
    have hnn : 0 ≤ payoff (matrix adj) w p := by
      rw [payoff_transpose (matrix adj) w p]
      apply sum_nonneg
      intro u _
      apply mul_nonneg (hw u)
      rw [col_matrix, hp.2]
      linarith [cols u]
    linarith

omit [DecidableEq V] in
/-- One-sided deleted LP certificates already give both positive weights. -/
theorem two_sided [Nonempty V] (deleted : DeletedLP adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v)
    (bad0 : ∀ v, (∑ u, w0 u) < w0 v + 3 * outWeight adj w0 v) :
    ∃ w ∈ simplex, ∃ p ∈ simplex, ∃ t : ℝ, 1 < t ∧
      (∀ v, 0 < w v) ∧ (∀ v, 0 < p v) ∧
        (∀ v, w v + 3 * outWeight adj w v = t) ∧
        (∀ v, p v + 3 * inWeight adj p v = t) := by
  classical
  obtain ⟨w, hw, p, hp, c, cn, wp, pp, rows, cols⟩ :=
    two_sided_of_full (matrix adj) (full_of_deletedLeft _ (deleted_left adj deleted)) w0 hw0
      (fun v => by rw [row_matrix]; linarith [bad0 v])
  refine ⟨w, hw, p, hp, 1 - c, by linarith, wp, pp, ?_, ?_⟩
  · intro v
    have h := rows v
    rw [row_matrix, hw.2] at h
    linarith
  · intro v
    have h := cols v
    rw [col_matrix, hp.2] at h
    linarith

omit [DecidableEq V] in
theorem atom_lower (noLoop : ∀ v, ¬ adj v v) (deleted : DeletedLP adj)
    (w : V → ℝ) (hw : w ∈ simplex) (t : ℝ)
    (constant : ∀ v, w v + 3 * outWeight adj w v = t) : ∀ x, t - 1 ≤ 2 * w x := by
  classical
  have he (v : V) : row (matrix adj) w v = 1 - t := by
    rw [row_matrix, hw.2]
    linarith [constant v]
  have hb := atom_bound (matrix adj) (deleted_left adj deleted) 2 (matrix_lower adj noLoop)
    w hw.1 (1 - t) he
  intro x
  linarith [hb x]

omit [DecidableEq V] in
theorem order_bound (noLoop : ∀ v, ¬ adj v v) (deleted : DeletedLP adj)
    (w : V → ℝ) (hw : w ∈ simplex) (t : ℝ)
    (constant : ∀ v, w v + 3 * outWeight adj w v = t) :
    (Fintype.card V : ℝ) * (t - 1) ≤ 2 := by
  classical
  have h := sum_le_sum (s := (univ : Finset V))
    (fun x _ => atom_lower adj noLoop deleted w hw t constant x)
  simpa only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hw.2, mul_one] using h

end CH.LinearProgram

#print axioms CH.LinearProgram.lp_iff_distribution
#print axioms CH.LinearProgram.two_sided
#print axioms CH.LinearProgram.atom_lower
#print axioms CH.LinearProgram.order_bound
