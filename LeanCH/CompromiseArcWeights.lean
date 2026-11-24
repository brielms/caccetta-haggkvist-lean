module

public import LeanCH.CompromiseWeighted
public import Mathlib.Logic.Relation

set_option linter.style.header false

/-! Scope of the termwise arc-weight scheme in Section 13.1. The theorem
uses the explicit coefficient inequalities, not a purported equivalence
between those sufficient inequalities and every possible Seymour reduction. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted
public section

namespace CH.CompromiseArcWeights

section Paths

variable {V : Type*} (adj : V → V → Prop) (φ : V → V → ℝ)

@[expose] def Termwise : Prop :=
  (∀ v u s, adj v u → adj u s → v ≠ s → ¬ adj v s → φ u s ≤ 1) ∧
  (∀ v u s, adj v u → adj u s → adj v s → φ u s ≤ φ v s)

/-- A coefficient above one propagates to every predecessor of its tail. -/
theorem high_predecessor (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (terms : Termwise adj φ) {v u s : V} (hvu : adj v u)
    (hus : adj u s) (high : 1 < φ u s) : adj v s ∧ 1 < φ v s := by
  have hne : v ≠ s := by
    intro he
    subst v
    exact noDigon u s hus hvu
  have hvs : adj v s := by
    by_contra h
    have hb := terms.1 v u s hvu hus hne h
    linarith
  exact ⟨hvs, high.trans_le (terms.2 v u s hvu hus hvs)⟩

/-- Every arc with a return path has coefficient at most one. -/
theorem bound_of_return_path (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (terms : Termwise adj φ) {u s : V} (hus : adj u s)
    (back : Relation.ReflTransGen adj s u) : φ u s ≤ 1 := by
  by_contra h
  have high : 1 < φ u s := by linarith
  have pull {a b : V} (path : Relation.ReflTransGen adj a b) :
      adj b s ∧ 1 < φ b s → adj a s ∧ 1 < φ a s := by
    induction path with
    | refl => exact fun h => h
    | tail _ hbc ih =>
      intro h
      exact ih (high_predecessor adj φ noDigon terms hbc h.1 h.2)
  have hs := (pull back ⟨hus, high⟩).1
  exact noDigon s s hs hs

theorem bound_of_stronglyConnected (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (terms : Termwise adj φ)
    (connected : ∀ u v, Relation.ReflTransGen adj u v) :
    ∀ u s, adj u s → φ u s ≤ 1 := by
  intro u s hus
  exact bound_of_return_path adj φ noDigon terms hus (connected s u)

end Paths

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def headScore (w : V → ℝ) (φ : V → V → ℝ) (v : V) : ℝ :=
  ∑ a ∈ outN adj v, w a * φ v a

omit [DecidableEq V] in
theorem headScore_bound (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (φ : V → V → ℝ) (bound : ∀ v a, adj v a → φ v a ≤ 1) (v : V) :
    headScore adj w φ v ≤ outWeight adj w v := by
  have h := sum_le_sum (s := outN adj v) (fun a ha =>
    mul_le_mul_of_nonneg_left (bound v a (by simpa using ha)) (hw a))
  simpa [headScore, outWeight, mass] using h

omit [DecidableEq V] in
/-- Even a head score at least the required threshold forces incoming mass
to dominate outgoing mass at every vertex. Equality of the score is not needed. -/
theorem incoming_ge_outgoing (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (φ : V → V → ℝ) (bound : ∀ v a, adj v a → φ v a ≤ 1)
    (threshold : ∀ v, 2 * outWeight adj w v - inWeight adj w v ≤ headScore adj w φ v) :
    ∀ v, outWeight adj w v ≤ inWeight adj w v := by
  intro v
  have hs := headScore_bound adj w hw φ bound v
  have ht := threshold v
  linarith

omit [DecidableEq V] in
/-- Pointwise incoming dominance is equality on the positive weighted support. -/
theorem balanced_on_support (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (dominates : ∀ v, outWeight adj w v ≤ inWeight adj w v) :
    ∀ v, 0 < w v → inWeight adj w v = outWeight adj w v := by
  have hb := weighted_double_count adj w w
  change (∑ v, w v * outWeight adj w v) = ∑ v, w v * inWeight adj w v at hb
  have hn (v : V) : 0 ≤ w v * (inWeight adj w v - outWeight adj w v) :=
    mul_nonneg (hw v) (sub_nonneg.mpr (dominates v))
  have he : (∑ v, w v * (inWeight adj w v - outWeight adj w v)) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← hb, sub_self]
  have hz := (sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ (univ : Finset V)) => hn v)).mp he
  intro v hv
  have ht := hz v (mem_univ v)
  have hd := (mul_eq_zero.mp ht).resolve_left (ne_of_gt hv)
  linarith

omit [DecidableEq V] in
/-- The full explicitly stated scheme is confined to balanced positive support. -/
theorem termwise_scheme_balanced (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (φ : V → V → ℝ) (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (terms : Termwise adj φ) (connected : ∀ u v, Relation.ReflTransGen adj u v)
    (threshold : ∀ v, 2 * outWeight adj w v - inWeight adj w v ≤ headScore adj w φ v) :
    ∀ v, 0 < w v → inWeight adj w v = outWeight adj w v :=
  balanced_on_support adj w hw (incoming_ge_outgoing adj w hw φ
    (bound_of_stronglyConnected adj φ noDigon terms connected) threshold)

end CH.CompromiseArcWeights

#print axioms CH.CompromiseArcWeights.bound_of_return_path
#print axioms CH.CompromiseArcWeights.bound_of_stronglyConnected
#print axioms CH.CompromiseArcWeights.incoming_ge_outgoing
#print axioms CH.CompromiseArcWeights.balanced_on_support
#print axioms CH.CompromiseArcWeights.termwise_scheme_balanced
