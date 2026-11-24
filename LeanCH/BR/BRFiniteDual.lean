import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Finite real dual certificates, following the corpus CompromiseGame
proof with specific imports. A density bridge derives real small-row
statements from rational ones, including weights with zero coordinates. -/
namespace LeanCH.BR.FiniteDual
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def simplex : Set (V → ℝ) := {w | (∀ v, 0 ≤ w v) ∧ ∑ v, w v = 1}
def point (v u : V) : ℝ := if u = v then 1 else 0

theorem point_mem (v : V) : point v ∈ simplex := by
  refine ⟨?_, ?_⟩
  · intro u
    simp only [point]
    split_ifs <;> norm_num
  · simp [point]

theorem simplex_nonempty [Nonempty V] : (simplex (V := V)).Nonempty :=
  ⟨point (Classical.arbitrary V), point_mem _⟩

theorem simplex_convex : Convex ℝ (simplex (V := V)) := by
  intro w hw p hp a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro v
    exact add_nonneg (mul_nonneg ha (hw.1 v)) (mul_nonneg hb (hp.1 v))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib,
      ← mul_sum, hw.2, hp.2, mul_one, hab]

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

def linearEval (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ v, x v * c v
  map_add' x y := by simp [add_mul, sum_add_distrib]
  map_smul' a x := by simp [mul_sum, mul_assoc]

def row (M : V → V → ℝ) (w : V → ℝ) (v : V) : ℝ := ∑ u, M v u * w u
def col (M : V → V → ℝ) (p : V → ℝ) (u : V) : ℝ := ∑ v, p v * M v u
def payoff (M : V → V → ℝ) (w p : V → ℝ) : ℝ := ∑ v, p v * row M w v

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

theorem exists_saddle [Nonempty V] (M : V → V → ℝ) :
    ∃ w ∈ simplex, ∃ p ∈ simplex,
      ∀ z ∈ simplex, ∀ r ∈ simplex, payoff M w r ≤ payoff M z p := by
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

theorem fair_of_no_bad [Nonempty V] (M : V → V → ℝ)
    (hno : ¬ ∃ w ∈ simplex, ∀ v, row M w v < 0) :
    ∃ p ∈ simplex, ∀ u, 0 ≤ col M p u := by
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

/-- Squares pull the strict failure set back to an open set, so density of
rational vectors works even when the original nonnegative weights vanish. -/
theorem real_small_of_rational (R : V → V → ℚ)
    (good : ∀ w : V → ℚ, (∀ v, 0 ≤ w v) → ∃ v, (∑ u, R v u * w u) ≤ ∑ u, w u) :
    ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, row (fun i j => (R i j : ℝ)) w v ≤ ∑ u, w u := by
  intro w hw
  by_contra hn
  push_neg at hn
  let U : Set (V → ℝ) := {x | ∀ i, (∑ j, (x j)^2) < ∑ j, (R i j : ℝ) * (x j)^2}
  have hopen : IsOpen U := by
    have he : U = ⋂ i, {x : V → ℝ | (∑ j, (x j)^2) < ∑ j, (R i j : ℝ) * (x j)^2} := by
      ext x
      simp [U]
    rw [he]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt <;> fun_prop
  have hmem : (fun i => Real.sqrt (w i)) ∈ U := by
    intro i
    simpa only [row, Real.sq_sqrt (hw _)] using hn i
  have hdense : DenseRange (fun x : V → ℚ => fun i => (x i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hopen ⟨_, hmem⟩
  obtain ⟨i, hi⟩ := good (fun j => (x j)^2) (fun j => sq_nonneg _)
  have hreal : (∑ j, (R i j : ℝ) * (x j : ℝ)^2) ≤ ∑ j, (x j : ℝ)^2 := by
    exact_mod_cast hi
  exact (not_lt_of_ge hreal) (hx i)

theorem dual_of_rational_small [Nonempty V] (R : V → V → ℚ)
    (good : ∀ w : V → ℚ, (∀ v, 0 ≤ w v) → ∃ v, (∑ u, R v u * w u) ≤ ∑ u, w u) :
    ∃ p : V → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      ∀ j, (∑ i, p i * (R i j : ℝ)) ≤ 1 := by
  let B : V → V → ℝ := fun i j => 1 - (R i j : ℝ)
  have hno : ¬ ∃ w ∈ simplex, ∀ v, row B w v < 0 := by
    rintro ⟨w, hw, hb⟩
    obtain ⟨v, hv⟩ := real_small_of_rational R good w hw.1
    have h := hb v
    simp only [row, B, sub_mul, one_mul, sum_sub_distrib] at h
    exact (not_lt_of_ge hv) (sub_neg.mp h)
  obtain ⟨p, hp, hc⟩ := fair_of_no_bad B hno
  refine ⟨p, hp.1, hp.2, ?_⟩
  intro j
  have h := hc j
  simp only [col, B, mul_sub, mul_one, sum_sub_distrib, hp.2] at h
  linarith

end LeanCH.BR.FiniteDual
