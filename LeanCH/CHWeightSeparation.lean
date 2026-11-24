module

public import LeanCH.CHLinearProgram

set_option linter.style.header false

/-! A quantitative constraint coupling the two CH counterweights.
The existence of a weighted Seymour vertex is an explicit hypothesis,
as permitted by the thinking prompt. This is not a proof of CH. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.LinearProgram
public section

namespace CH.WeightSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def variation (w p : V → ℝ) : ℝ := ∑ v, max (p v - w v) 0

omit [DecidableEq V] in
theorem two_mul_variation (w p : V → ℝ) (hw : w ∈ simplex) (hp : p ∈ simplex) :
    2 * variation w p = ∑ v, |p v - w v| := by
  have he (v : V) : 2 * max (p v - w v) 0 = |p v - w v| + (p v - w v) := by
    by_cases h : 0 ≤ p v - w v
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
    · have hn : p v - w v ≤ 0 := le_of_not_ge h
      rw [max_eq_right hn, abs_of_nonpos hn]
      ring
  simp only [variation, mul_sum, he, sum_add_distrib, sum_sub_distrib, hp.2, hw.2]
  ring

omit [DecidableEq V] in
theorem variation_upper (w p : V → ℝ) (hp : p ∈ simplex) (a : ℝ)
    (wl : ∀ v, a ≤ w v) (pl : ∀ v, a ≤ p v) :
    variation w p ≤ 1 - (Fintype.card V : ℝ) * a := by
  have he (v : V) : max (p v - w v) 0 ≤ p v - a := by
    apply max_le
    · linarith [wl v]
    · linarith [pl v]
  have h := sum_le_sum (s := (univ : Finset V)) (fun v _ => he v)
  simpa [variation, sum_sub_distrib, hp.2, sum_const, nsmul_eq_mul] using h

variable (adj : V → V → Prop) [DecidableRel adj]

omit [DecidableEq V] in
theorem closed_in_difference (noLoop : ∀ v, ¬ adj v v) (w p : V → ℝ) (v : V) :
    p v - w v + 3 * (inWeight adj p v - inWeight adj w v) ≤ 3 * variation w p := by
  classical
  let q := fun u => max (p u - w u) 0
  have qn (u : V) : 0 ≤ q u := le_max_right _ _
  have hd : inWeight adj (fun u => p u - w u) v =
      inWeight adj p v - inWeight adj w v := by simp [inWeight, mass, sum_sub_distrib]
  have hi : inWeight adj (fun u => p u - w u) v ≤ inWeight adj q v := by
    exact sum_le_sum (fun u _ => le_max_left _ _)
  have hvnot : v ∉ inN adj v := by simpa using noLoop v
  have hs : (∑ u ∈ insert v (inN adj v), q u) ≤ ∑ u, q u :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _ => qn u)
  rw [sum_insert hvnot] at hs
  have hv : p v - w v ≤ q v := le_max_left _ _
  change q v + inWeight adj q v ≤ variation w p at hs
  rw [hd] at hi
  linarith [qn v]

theorem ball_weight_le (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v z, adj u v → adj v z → ¬ adj z u)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (v : V) :
    w v + outWeight adj w v + inWeight adj w v + secondWeight adj w v ≤ ∑ u, w u := by
  have noLoop (u : V) : ¬ adj u u := fun h => noDigon u u h h
  have hoi : Disjoint (outN adj v) (inN adj v) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact noDigon v a (by simpa using ha) (by simpa using hb)
  have hos : Disjoint (outN adj v) (second adj v) := by
    apply disjoint_left.mpr
    intro a ha hs
    exact ((mem_second adj v a).mp hs).2.1 (by simpa using ha)
  have his : Disjoint (inN adj v) (second adj v) := by
    apply disjoint_left.mpr
    intro a ha hs
    obtain ⟨_, _, b, hvb, hba⟩ := (mem_second adj v a).mp hs
    exact noTri v b a hvb hba (by simpa using ha)
  have hvnot : v ∉ outN adj v ∪ inN adj v ∪ second adj v := by simp [noLoop]
  have hs : (∑ u ∈ insert v (outN adj v ∪ inN adj v ∪ second adj v), w u) ≤ ∑ u, w u :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _ => hw u)
  rw [sum_insert hvnot, sum_union (disjoint_union_left.mpr ⟨hos, his⟩), sum_union hoi] at hs
  simpa [outWeight, inWeight, secondWeight, mass, add_assoc] using hs

/-- The two positive probability weights cannot be closer than the CH
deficit in total variation. Only a Seymour vertex for w is needed. -/
theorem deficit_le_variation (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v z, adj u v → adj v z → ¬ adj z u)
    (w p : V → ℝ) (hw : w ∈ simplex) (t : ℝ)
    (rows : ∀ v, w v + 3 * outWeight adj w v = t)
    (cols : ∀ v, p v + 3 * inWeight adj p v = t)
    (seymour : ∃ v, outWeight adj w v ≤ secondWeight adj w v) :
    t - 1 ≤ variation w p := by
  obtain ⟨v, hv⟩ := seymour
  have ball := ball_weight_le adj noDigon noTri w hw.1 v
  rw [hw.2] at ball
  have hd := closed_in_difference adj (fun u h => noDigon u u h h) w p v
  linarith [rows v, cols v]

/-- Adding the atom bounds in both orientations improves n(t-1) ≤ 2
to (n+2)(t-1) ≤ 2. The weighted Seymour input remains explicit. -/
theorem strengthened_order_bound (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v z, adj u v → adj v z → ¬ adj z u)
    (deleted : DeletedLP adj) (deletedRev : DeletedLP (fun a b => adj b a))
    (w p : V → ℝ) (hw : w ∈ simplex) (hp : p ∈ simplex) (t : ℝ)
    (rows : ∀ v, w v + 3 * outWeight adj w v = t)
    (cols : ∀ v, p v + 3 * inWeight adj p v = t)
    (seymour : ∃ v, outWeight adj w v ≤ secondWeight adj w v) :
    ((Fintype.card V : ℝ) + 2) * (t - 1) ≤ 2 := by
  have noLoop (u : V) : ¬ adj u u := fun h => noDigon u u h h
  have wl := atom_lower adj noLoop deleted w hw t rows
  have hi (v : V) : outWeight (fun a b => adj b a) p v = inWeight adj p v := by
    have he : outN (fun a b => adj b a) v = inN adj v := by ext; simp
    simp [outWeight, inWeight, he]
  have pl := atom_lower (fun a b => adj b a) noLoop deletedRev p hp t
    (fun v => by rw [hi]; exact cols v)
  have lower := deficit_le_variation adj noDigon noTri w p hw t rows cols seymour
  have upper := variation_upper w p hp ((t - 1) / 2)
    (fun v => by linarith [wl v]) (fun v => by linarith [pl v])
  nlinarith

end CH.WeightSeparation

#print axioms CH.WeightSeparation.two_mul_variation
#print axioms CH.WeightSeparation.deficit_le_variation
#print axioms CH.WeightSeparation.strengthened_order_bound
