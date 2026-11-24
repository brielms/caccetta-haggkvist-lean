import LeanCH.BR.BRq3Layer

/-!
# Shared layer tools for `Ball(6,3)`, `TOP(3)` and the rewiring step, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq3_attempt_subagent.md`, §1–§2.

* `Ball q s`, `TOP m`: the ball statements. `Ball q s` is exactly the hypothesis of `br_of_ball`; `TOP m` is the
  strong form (radius = cycle bound) at out-degree three.
* `ball_trans`, `exists_pred`, `ball_shift`, `not_mem_ball_shift`: walking balls of other vertices against the layers
  of `u`.
* `closed_outEq` (Lemma 1, the closed layer): if `N_{k+1} = ∅` then `B_k ∖ {u}` is out-closed with out-degree three.
* `card_ge_of_ball_strict`, `corB_layer_strict` (Lemma 2, strict single exit): if every vertex of `B_k` has at most one
  out-neighbour in `N_{k+1}`, `2 ≤ k`, `k + 1 ≤ q`, then `|B_k| ≥ 2q + 3`.
* `ball_three_three`: `Ball(3,3)`, i.e. `|B_2(u)| ≥ 7` in a 3-free digraph with out-degree three.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

/-- `Ball(q,s)`: every `q`-free digraph with out-degree exactly `s` has `|B_{q-1}(u)| ≥ s(q-1)+1` (the hypothesis of
`br_of_ball`). -/
def Ball (q s : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (W : Finset ℕ), QFree D W q → OutEq s D W →
    ∀ u ∈ W, s * (q - 1) + 1 ≤ (ball D W u (q - 1)).card

/-- `TOP(m)`, the strong form: every `m`-free digraph with out-degree exactly three has `|B_m(u)| ≥ 3m+1`. -/
def TOP (m : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (W : Finset ℕ), QFree D W m → OutEq 3 D W →
    ∀ u ∈ W, 3 * m + 1 ≤ (ball D W u m).card

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

theorem walk_zero {a b : ℕ} (w : Walk D W a b 0) : a = b := by
  cases w; rfl

theorem walk_one {a b : ℕ} (w : Walk D W a b 1) : b ∈ W ∧ D a b = true := by
  cases w with
  | step hb hab w' => cases w'; exact ⟨hb, hab⟩

theorem mem_ball_of_walk {v m j : ℕ} (w : Walk D W u v m) (hm : m ≤ j) (hv : v ∈ W) : v ∈ ball D W u j :=
  mem_ball.mpr ⟨hv, m, hm, w⟩

theorem eq_of_mem_ball_zero {z v : ℕ} (hv : v ∈ ball D W z 0) : v = z := by
  obtain ⟨_, j, hj, w⟩ := mem_ball.mp hv
  obtain rfl : j = 0 := by omega
  exact (walk_zero w).symm

/-- Concatenating balls. -/
theorem ball_trans {z y v i j : ℕ} (hy : y ∈ ball D W z j) (hv : v ∈ ball D W y i) :
    v ∈ ball D W z (j + i) := by
  obtain ⟨_, j', hj', w1⟩ := mem_ball.mp hy
  obtain ⟨hvW, i', hi', w2⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨hvW, j' + i', by omega, w1.append w2⟩

/-- A vertex `v ≠ z` of `B_{j+1}(z)` has an in-neighbour in `B_j(z)`. -/
theorem exists_pred {z v j : ℕ} (hz : z ∈ W) (hv : v ∈ ball D W z (j + 1)) (hvz : v ≠ z) :
    ∃ y ∈ ball D W z j, D y v = true := by
  obtain ⟨_, i, hi, w⟩ := mem_ball.mp hv
  cases i with
  | zero => exact absurd (walk_zero w).symm hvz
  | succ i =>
    obtain ⟨y, wy, _, hyv⟩ := w.unsnoc
    refine ⟨y, mem_ball.mpr ⟨?_, i, by omega, wy⟩, hyv⟩
    rcases wy.end_mem_or with h | h
    · rw [h]; exact hz
    · exact h

/-- If `B_j(z) ⊆ B_m(u)` then `B_{j+1}(z) ⊆ B_{m+1}(u)`. -/
theorem ball_shift {z j m : ℕ} (hz : z ∈ W) (h : ball D W z j ⊆ ball D W u m) :
    ball D W z (j + 1) ⊆ ball D W u (m + 1) := by
  intro v hv
  by_cases hvz : v = z
  · rw [hvz]; exact ball_mono_radius (by omega) (h (self_mem_ball hz))
  · obtain ⟨y, hy, hyv⟩ := exists_pred hz hv hvz
    exact ball_step (h hy) (ball_subset hv) hyv

/-- If `B_j(z) ⊆ B_m(u)`, `z ≠ u` and `m + 1 ≤ q`, then `u ∉ B_{j+1}(z)`. -/
theorem not_mem_ball_shift {q z j m : ℕ} (hfree : QFree D W q) (hu : u ∈ W) (hz : z ∈ W) (hzu : z ≠ u)
    (h : ball D W z j ⊆ ball D W u m) (hm : m + 1 ≤ q) : u ∉ ball D W z (j + 1) := by
  intro hu'
  obtain ⟨y, hy, hyu⟩ := exists_pred hz hu' (Ne.symm hzu)
  exact no_back_arc hfree hu (h hy) hm hyu

/-- Shifting a ball that avoids `N_{m+1}`: if `B_j(z) ⊆ B_m(u)` and no vertex of `B_{j+1}(z)` lies in `N_{m+1}`, then
`B_{j+1}(z) ⊆ B_m(u)`. -/
theorem ball_shift_avoid {z j m : ℕ} (hz : z ∈ W) (h : ball D W z j ⊆ ball D W u m)
    (havoid : ∀ v ∈ ball D W z (j + 1), v ∈ ball D W u (m + 1) → v ∈ ball D W u m) :
    ball D W z (j + 1) ⊆ ball D W u m :=
  fun v hv => havoid v hv (ball_shift hz h hv)

/-! ### Lemma 1: the closed layer -/

/-- **Lemma 1 (closed layer).** If `N_{k+1} = ∅`, `1 ≤ k` and `k + 1 ≤ q`, then `B_k ∖ {u}` is nonempty and out-closed
with out-degree exactly three. -/
theorem closed_outEq {q k : ℕ} (hk : 1 ≤ k) (hkq : k + 1 ≤ q) (hfree : QFree D W q) (hout : OutEq 3 D W)
    (hu : u ∈ W) (h : (ball D W u (k + 1)).card ≤ (ball D W u k).card) :
    OutEq 3 D ((ball D W u k).erase u) ∧ ((ball D W u k).erase u).Nonempty := by
  classical
  have hsub : ball D W u k ⊆ ball D W u (k + 1) := ball_mono_radius (by omega)
  have heq : ball D W u k = ball D W u (k + 1) := Finset.eq_of_subset_of_card_le hsub h
  have hUW : (ball D W u k).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hcl : ∀ y ∈ (ball D W u k).erase u, outN D ((ball D W u k).erase u) y = outN D W y := by
    intro y hy
    ext z
    rw [mem_outN, mem_outN]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hUW hz, h⟩
    · rintro ⟨hzW, hyz⟩
      have hyB := Finset.mem_of_mem_erase hy
      have hzk : z ∈ ball D W u k := by rw [heq]; exact ball_step hyB hzW hyz
      refine ⟨Finset.mem_erase.mpr ⟨?_, hzk⟩, hyz⟩
      intro hzu
      rw [hzu] at hyz
      exact no_back_arc hfree hu hyB (by omega) hyz
  refine ⟨fun y hy => by rw [hcl y hy]; exact hout y (hUW hy), ?_⟩
  obtain ⟨z, hz⟩ : (outN D W u).Nonempty := by rw [← Finset.card_pos, hout u hu]; omega
  refine ⟨z, Finset.mem_erase.mpr ⟨?_, ball_mono_radius hk (mem_ball_one_of_out hz)⟩⟩
  intro hzu
  have h' := (mem_outN.mp hz).2
  rw [hzu] at h'
  exact loopfree hfree (by omega) hu h'

/-! ### Lemma 2: the strict single exit -/

/-- The degree sum of `card_ge_of_ball`, strict: min out `≥ 2`, one vertex of out `≥ 3`, and a ball bound `b` at
radius `q-1` give `|U| ≥ b + 3`. -/
theorem card_ge_of_ball_strict {U : Finset ℕ} {q b : ℕ} (hq : 1 ≤ q) (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, 2 ≤ (outN D U y).card) {y0 : ℕ} (hy0 : y0 ∈ U) (h3 : 3 ≤ (outN D U y0).card)
    (hball : ∀ z ∈ U, b ≤ (ball D U z (q - 1)).card) : b + 3 ≤ U.card := by
  classical
  have hin : ∀ z ∈ U, (U.filter (fun y => D y z = true)).card ≤ U.card - b := by
    intro z hz
    have hsub : U.filter (fun y => D y z = true) ⊆ U \ ball D U z (q - 1) := by
      intro y hy
      obtain ⟨hyU, hyz⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_sdiff.mpr ⟨hyU, fun hyb => no_back_arc hfree hz hyb (by omega) hyz⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at h1
    have h2 := hball z hz
    omega
  have hS : 2 * U.card + 1 ≤ ∑ y ∈ U, (outN D U y).card := by
    rw [← Finset.add_sum_erase U _ hy0]
    have h1 : ∑ _y ∈ U.erase y0, 2 ≤ ∑ y ∈ U.erase y0, (outN D U y).card :=
      Finset.sum_le_sum (fun y hy => hmin y (Finset.mem_of_mem_erase hy))
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_erase_of_mem hy0] at h1
    have hpos : 0 < U.card := Finset.card_pos.mpr ⟨y0, hy0⟩
    omega
  have hsum : 2 * U.card + 1 ≤ U.card * (U.card - b) := by
    calc 2 * U.card + 1 ≤ ∑ y ∈ U, (outN D U y).card := hS
      _ = ∑ z ∈ U, (U.filter (fun y => D y z = true)).card := Compose.ThinRigid.sum_out_eq_sum_in D U
      _ ≤ ∑ _z ∈ U, (U.card - b) := Finset.sum_le_sum hin
      _ = U.card * (U.card - b) := Finset.sum_const_nat (fun _ _ => rfl)
  by_contra hlt
  have h5 : U.card - b ≤ 2 := by omega
  have := Nat.mul_le_mul_left U.card h5
  omega

/-- **Lemma 2 (strict single exit).** If `2 ≤ k`, `k + 1 ≤ q` and every vertex of `B_k` has at most one out-neighbour
in `N_{k+1}`, then `|B_k| ≥ 2q + 3`. -/
theorem corB_layer_strict {q k : ℕ} (hk : 2 ≤ k) (hkq : k + 1 ≤ q) (hfree : QFree D W q) (hout : OutEq 3 D W)
    (hu : u ∈ W)
    (hP : ∀ y ∈ ball D W u k, (outN D W y ∩ (ball D W u (k + 1) \ ball D W u k)).card ≤ 1) :
    2 * q + 3 ≤ (ball D W u k).card := by
  classical
  have hUW : (ball D W u k).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hs : ∀ y ∈ (ball D W u k).erase u,
      outN D W y \ (ball D W u (k + 1) \ ball D W u k) ⊆ outN D ((ball D W u k).erase u) y := by
    intro y hy z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzW, hyz⟩ := mem_outN.mp hz1
    have hyB : y ∈ ball D W u k := Finset.mem_of_mem_erase hy
    have hzB : z ∈ ball D W u (k + 1) := ball_step hyB hzW hyz
    have hzk : z ∈ ball D W u k := by
      by_contra h; exact hz2 (Finset.mem_sdiff.mpr ⟨hzB, h⟩)
    refine mem_outN.mpr ⟨Finset.mem_erase.mpr ⟨?_, hzk⟩, hyz⟩
    intro hzu
    rw [hzu] at hyz
    exact no_back_arc hfree hu hyB (by omega) hyz
  have hmin : ∀ y ∈ (ball D W u k).erase u, 2 ≤ (outN D ((ball D W u k).erase u) y).card := by
    intro y hy
    have h1 := Finset.card_sdiff_add_card_inter (outN D W y) (ball D W u (k + 1) \ ball D W u k)
    have h2 := Finset.card_le_card (hs y hy)
    have h3 := hout y (hUW hy)
    have h4 := hP y (Finset.mem_of_mem_erase hy)
    omega
  -- a vertex of `N_1` keeps all three arcs
  obtain ⟨v, hv⟩ : (outN D W u).Nonempty := by rw [← Finset.card_pos, hout u hu]; omega
  have hvB1 : v ∈ ball D W u 1 := mem_ball_one_of_out hv
  have hvE : v ∈ (ball D W u k).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) hvB1⟩
    intro hvu
    have h' := (mem_outN.mp hv).2
    rw [hvu] at h'
    exact loopfree hfree (by omega) hu h'
  have hv3 : 3 ≤ (outN D ((ball D W u k).erase u) v).card := by
    have hsub : outN D W v ⊆ outN D ((ball D W u k).erase u) v := by
      intro z hz
      refine hs v hvE (Finset.mem_sdiff.mpr ⟨hz, ?_⟩)
      intro hzN
      obtain ⟨hzW, hvz⟩ := mem_outN.mp hz
      exact (Finset.mem_sdiff.mp hzN).2 (ball_mono_radius (by omega) (ball_step hvB1 hzW hvz))
    have := Finset.card_le_card hsub
    rw [hout v (outN_subset hv)] at this
    exact this
  have hfE : QFree D ((ball D W u k).erase u) q := hfree.mono_set hUW
  have hc := card_ge_of_ball_strict (b := 2 * (q - 1) + 1) (by omega) hfE hmin hvE hv3
    (fun z hz => ball_growth q (by omega) D _ hfE hmin z hz (q - 1) (by omega))
  have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := k) hu)
  omega

/-! ### `Ball(3,3)` -/

/-- `|B_2(u)| ≥ 7` in a 3-free digraph with out-degree three. -/
theorem ball_three_three (hfree : QFree D W 3) (hout : OutEq 3 D W) (hu : u ∈ W) :
    7 ≤ (ball D W u 2).card := by
  have h1 := card_ball_one (hfree.mono_bound (by omega)) hout hu
  have h12 : ball D W u 1 ⊆ ball D W u 2 := ball_mono_radius (by omega)
  have e2 := Finset.card_sdiff_add_card_eq_card h12
  have h62 := six_two hfree hout hu
  omega

end LeanCH.BR.BRq3
