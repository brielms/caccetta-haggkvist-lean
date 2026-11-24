module

public import Mathlib.Tactic
public import Mathlib.Topology.Sion
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.style.header false

/-! Finite minimax and the constant-deficit reduction. The minimax existence
proof uses Mathlib's Sion theorem; full support is a stated hypothesis here
and is supplied by graph deletion in CompromiseCritical. -/

open Finset
public section

namespace CH.CompromiseGame

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def simplex : Set (V → ℝ) :=
  {w | (∀ v, 0 ≤ w v) ∧ ∑ v, w v = 1}

@[expose] def point (v : V) (u : V) : ℝ := if u = v then 1 else 0

theorem point_mem (v : V) : point v ∈ simplex := by
  refine ⟨?_, ?_⟩
  · intro u
    simp only [point]
    split_ifs <;> norm_num
  · simp [point]

omit [DecidableEq V] in
theorem simplex_nonempty [Nonempty V] : (simplex (V := V)).Nonempty := by
  classical
  exact ⟨point (Classical.arbitrary V), point_mem _⟩

omit [DecidableEq V] in
theorem simplex_convex : Convex ℝ (simplex (V := V)) := by
  intro w hw p hp a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro v
    exact add_nonneg (mul_nonneg ha (hw.1 v)) (mul_nonneg hb (hp.1 v))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib,
      ← mul_sum, hw.2, hp.2, mul_one, hab]

omit [DecidableEq V] in
theorem simplex_compact : IsCompact (simplex (V := V)) := by
  have hnn : IsClosed {w : V → ℝ | ∀ v, 0 ≤ w v} := by
    have he : {w : V → ℝ | ∀ v, 0 ≤ w v} = ⋂ v, {w | 0 ≤ w v} := by ext; simp
    rw [he]
    exact isClosed_iInter (fun v => isClosed_le continuous_const (continuous_apply v))
  have hsum : IsClosed {w : V → ℝ | ∑ v, w v = 1} := by
    apply isClosed_eq _ continuous_const
    fun_prop
  have hc : IsClosed (simplex (V := V)) := hnn.inter hsum
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : V => (0 : ℝ)) (fun _ => 1))) hc
  intro w hw
  refine ⟨hw.1, ?_⟩
  intro v
  have hv := single_le_sum (fun u (_ : u ∈ (univ : Finset V)) => hw.1 u) (mem_univ v)
  simpa [hw.2] using hv

omit [DecidableEq V] in
theorem simplex_has_positive {p : V → ℝ} (hp : p ∈ simplex) : ∃ v, 0 < p v := by
  by_contra h
  push Not at h
  have hz (v : V) : p v = 0 := by linarith [hp.1 v, h v]
  have he := hp.2
  simp [hz] at he

@[expose] def linearEval (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ v, x v * c v
  map_add' x y := by simp [add_mul, sum_add_distrib]
  map_smul' a x := by simp [mul_sum, mul_assoc]

@[expose] def row (M : V → V → ℝ) (w : V → ℝ) (v : V) : ℝ := ∑ u, M v u * w u
@[expose] def col (M : V → V → ℝ) (p : V → ℝ) (u : V) : ℝ := ∑ v, p v * M v u
@[expose] def payoff (M : V → V → ℝ) (w p : V → ℝ) : ℝ := ∑ v, p v * row M w v

omit [DecidableEq V] in
theorem payoff_transpose (M : V → V → ℝ) (w p : V → ℝ) :
    payoff M w p = ∑ u, w u * col M p u := by
  simp only [payoff, row, col, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  ring

theorem payoff_point_right (M : V → V → ℝ) (w : V → ℝ) (v : V) :
    payoff M w (point v) = row M w v := by simp [payoff, point]

theorem payoff_point_left (M : V → V → ℝ) (p : V → ℝ) (u : V) :
    payoff M (point u) p = col M p u := by rw [payoff_transpose]; simp [point]

omit [DecidableEq V] in
/-- Finite zero-sum minimax, with the column distribution minimizing. -/
theorem exists_saddle [Nonempty V] (M : V → V → ℝ) :
    ∃ w ∈ simplex, ∃ p ∈ simplex,
      ∀ z ∈ simplex, ∀ q ∈ simplex, payoff M w q ≤ payoff M z p := by
  classical
  have hx (p : V → ℝ) : (fun w => payoff M w p) = linearEval (col M p) := by
    funext w
    exact payoff_transpose M w p
  have hy (w : V → ℝ) : (fun p => payoff M w p) = linearEval (row M w) := rfl
  have cont (c : V → ℝ) : Continuous (linearEval c) := by
    change Continuous (fun x : V → ℝ => ∑ v, x v * c v)
    fun_prop
  exact Sion.exists_isSaddlePointOn simplex_nonempty simplex_convex simplex_compact
    (fun p _ => by rw [hx]; exact (cont _).lowerSemicontinuous.lowerSemicontinuousOn simplex)
    (fun p _ => by rw [hx]; exact ((linearEval _).convexOn simplex_convex).quasiconvexOn)
    simplex_convex simplex_nonempty simplex_compact
    (fun w _ => by rw [hy]; exact (cont _).upperSemicontinuous.upperSemicontinuousOn simplex)
    (fun w _ => by rw [hy]; exact ((linearEval _).concaveOn simplex_convex).quasiconcaveOn)

omit [DecidableEq V] in
theorem payoff_neg (M : V → V → ℝ) (w p : V → ℝ) (hp : p ∈ simplex)
    (bad : ∀ v, row M w v < 0) : payoff M w p < 0 := by
  obtain ⟨v, hv⟩ := simplex_has_positive hp
  have h := sum_lt_sum (s := (univ : Finset V)) (g := fun _ => (0 : ℝ))
    (fun u _ => mul_nonpos_of_nonneg_of_nonpos (hp.1 u) (bad u).le)
    ⟨v, mem_univ v, mul_neg_of_pos_of_neg hv (bad v)⟩
  simpa [payoff] using h

omit [DecidableEq V] in
/-- A nonnegative strict counterweight can be normalized without changing signs. -/
theorem normalize_bad [Nonempty V] (M : V → V → ℝ) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, row M w v < 0) :
    ∃ z ∈ simplex, ∀ v, row M z v < 0 := by
  let t := ∑ v, w v
  have tn : 0 ≤ t := sum_nonneg (fun v _ => hw v)
  have tp : 0 < t := by
    by_contra h
    have tz : t = 0 := by linarith
    have wz (v : V) : w v = 0 := by
      have hv : w v ≤ t := single_le_sum (fun u _ => hw u) (mem_univ v)
      linarith [hw v]
    have hb := bad (Classical.arbitrary V)
    simp [row, wz] at hb
  refine ⟨fun v => w v / t, ⟨fun v => div_nonneg (hw v) tn, ?_⟩, ?_⟩
  · rw [← sum_div]
    exact div_self (ne_of_gt tp)
  · intro v
    have he : row M (fun u => w u / t) v = row M w v / t := by
      simp only [row, mul_div_assoc, sum_div]
    rw [he]
    exact div_neg_of_neg_of_pos (bad v) tp

omit [DecidableEq V] in
/-- Finite minimax duality, with no additional duality axiom. -/
theorem fair_iff_no_bad [Nonempty V] (M : V → V → ℝ) :
    (∃ p ∈ simplex, ∀ u, 0 ≤ col M p u) ↔
      ¬ ∃ w ∈ simplex, ∀ v, row M w v < 0 := by
  classical
  constructor
  · rintro ⟨p, hp, hc⟩ ⟨w, hw, hb⟩
    have hn := payoff_neg M w p hp hb
    have hpw : 0 ≤ payoff M w p := by
      rw [payoff_transpose]
      exact sum_nonneg (fun u _ => mul_nonneg (hw.1 u) (hc u))
    linarith
  · intro hno
    obtain ⟨w, hw, p, hp, saddle⟩ := exists_saddle M
    have nonneg : 0 ≤ payoff M w p := by
      by_contra h
      apply hno
      refine ⟨w, hw, ?_⟩
      intro v
      have hv := saddle w hw (point v) (point_mem v)
      rw [payoff_point_right] at hv
      linarith
    refine ⟨p, hp, ?_⟩
    intro u
    have hu := saddle (point u) (point_mem u) p hp
    rw [payoff_point_left] at hu
    exact nonneg.trans hu

omit [DecidableEq V] in
/-- A full-support minimizing distribution makes all dual coordinates equal. -/
theorem critical_reversal [Nonempty V] (M : V → V → ℝ)
    (w0 : V → ℝ) (hw0 : w0 ∈ simplex) (bad0 : ∀ v, row M w0 v < 0)
    (full : ∀ w ∈ simplex, (∀ v, row M w v < 0) → ∀ v, 0 < w v) :
    ∃ w ∈ simplex, ∃ p ∈ simplex, ∃ c : ℝ, c < 0 ∧
      (∀ v, 0 < w v) ∧ (∀ v, row M w v ≤ c) ∧ (∀ u, col M p u = c) := by
  classical
  obtain ⟨w, hw, p, hp, saddle⟩ := exists_saddle M
  let c := payoff M w p
  have cn : c < 0 := (saddle w0 hw0 p hp).trans_lt (payoff_neg M w0 p hp bad0)
  have rows (v : V) : row M w v ≤ c := by
    have h := saddle w hw (point v) (point_mem v)
    simpa [c, payoff_point_right] using h
  have cols (u : V) : c ≤ col M p u := by
    have h := saddle (point u) (point_mem u) p hp
    simpa [c, payoff_point_left] using h
  have wp := full w hw (fun v => (rows v).trans_lt cn)
  have hz : (∑ u, w u * (col M p u - c)) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hw.2, one_mul]
    rw [← payoff_transpose]
    exact sub_self c
  have hz' := (sum_eq_zero_iff_of_nonneg
    (fun u (_ : u ∈ (univ : Finset V)) =>
      mul_nonneg (hw.1 u) (sub_nonneg.mpr (cols u)))).mp hz
  refine ⟨w, hw, p, hp, c, cn, wp, rows, ?_⟩
  intro u
  have he := (mul_eq_zero.mp (hz' u (mem_univ u))).resolve_left (ne_of_gt (wp u))
  linarith

omit [DecidableEq V] in
/-- With the full-support property in both directions, both weighted
surpluses are the same strictly negative constant at every vertex. -/
theorem critical_two_sided [Nonempty V] (M : V → V → ℝ)
    (w0 : V → ℝ) (hw0 : w0 ∈ simplex) (bad0 : ∀ v, row M w0 v < 0)
    (full : ∀ w ∈ simplex, (∀ v, row M w v < 0) → ∀ v, 0 < w v)
    (fullRev : ∀ p ∈ simplex, (∀ u, col M p u < 0) → ∀ u, 0 < p u) :
    ∃ w ∈ simplex, ∃ p ∈ simplex, ∃ c : ℝ, c < 0 ∧
      (∀ v, 0 < w v) ∧ (∀ v, 0 < p v) ∧
        (∀ v, row M w v = c) ∧ (∀ u, col M p u = c) := by
  obtain ⟨w, hw, p, hp, c, cn, wp, rows, cols⟩ := critical_reversal M w0 hw0 bad0 full
  have pp := fullRev p hp (fun u => by rw [cols u]; exact cn)
  have pair : payoff M w p = c := by rw [payoff_transpose]; simp [cols, ← sum_mul, hw.2]
  have hz : (∑ v, p v * (c - row M w v)) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hp.2, one_mul]
    change c - payoff M w p = 0
    rw [pair, sub_self]
  have hz' := (sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ (univ : Finset V)) =>
      mul_nonneg (hp.1 v) (sub_nonneg.mpr (rows v)))).mp hz
  refine ⟨w, hw, p, hp, c, cn, wp, pp, ?_, cols⟩
  intro v
  have he := (mul_eq_zero.mp (hz' v (mem_univ v))).resolve_left (ne_of_gt (pp v))
  linarith

end CH.CompromiseGame

#print axioms CH.CompromiseGame.exists_saddle
#print axioms CH.CompromiseGame.fair_iff_no_bad
#print axioms CH.CompromiseGame.critical_reversal
#print axioms CH.CompromiseGame.critical_two_sided
