import checkpoints.shen_extension.DipCost
import checkpoints.shen_extension.RigidHost

/-!
# Dips at the roots of a rigid host

`Rigid D V q s i` (`RigidHost`): order `q s`, `q = 2 i + 1`, out-degree `≥ s`, `i`-balls exactly
`s i + 1`, `(i+1)`-balls exactly `s (i+1)`. Generic in `q, s, i`; fifth-strip instances through
`rigid_of_top`.

* (P3) `small_root`: a floor `s (i+2) - d` at radius `i + 2` gives a root with
  `|ball (i-1)| ≤ s (i-1) + 1 + d` (two-ball sum rule at radii `(i+2, i-1)`, `Σ reverse = Σ forward`).
  `fifth_small_root`: `LedgerFloors.f5` gives `d = 3`, a root with `E_{i-1} ≤ 3`.
* (P4a) `inner_return`: every root has a row of layer `i` with a head in a layer `1 … i-1`.
* (P4b) `flat_inner_wide`: a root whose first `i - 2` layers have width `s` has
  `|layer (i-1)| ≥ s + 2` and `2 q + 1 ≤ s + |layer (i-1)|`; `flat_inner_false`: impossible when
  `3 s < 2 q + 1`. `fifth_not_flat`: at the fifth-strip top order (`a ≥ 7`) every root has a layer
  among `1 … i-2` of width `≠ s`, i.e. a radius `k ≤ i - 2` with `|ball k| ≥ s k + 2`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.RigidDip
open Finset BRq2 BRq3 FifthStripAll RigidHost DipCost
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer card_ball_succ)

variable {D : CH.Digraph} {V : Finset ℕ} {q s i : ℕ}

/-! ### (P3) a root with small excess -/

/-- **(P3).** A floor `s (i+2) - d` at radius `i+2` gives a root with `|ball (i-1)| ≤ s (i-1) + 1 + d`. -/
theorem small_root (R : Rigid D V q s i) (hi : 1 ≤ i) {d : ℕ} (ne : V.Nonempty)
    (floor : ∀ v ∈ V, s*(i+2) ≤ (ball D V v (i+2)).card + d) :
    ∃ v ∈ V, (ball D V v (i-1)).card ≤ s*(i-1) + 1 + d := by
  by_contra! h
  have two : ∀ v ∈ V, (reverseBall D V v (i-1)).card ≤ s*(i-1) + 1 + d := by
    intro v hv
    have t := reverseBall_add_ball_le (v := v) (i := i+2) (j := i-1) R.free (by rw [R.odd]; omega)
    have f := floor v hv
    have e : V.card = s*(i+2) + s*(i-1) := by
      rw [R.size, R.odd, ← mul_add, mul_comm]; congr 1; omega
    omega
  have lt := sum_lt_sum_of_nonempty ne h
  have le := sum_le_sum two
  rw [sum_reverseBall_eq_sum_ball] at le
  omega

/-- **(P3), fifth strip.** Some root has `|ball (a+2)| ≤ s (a+2) + 4`, i.e. `E_{i-1} ≤ 3`. -/
theorem fifth_small_root {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    (free : QFree D V (2*a+7)) (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) :
    ∃ v ∈ V, (ball D V v (a+2)).card ≤ (a+7)*(a+2) + 4 := by
  have R := rigid_of_top ha L tc free degree size
  have ne : V.Nonempty := by rw [← card_pos, size]; positivity
  have h := small_root (d := 3) R (by omega) ne (fun v hv => by
    have := L.f5 D V free degree v hv
    rw [show a + 3 + 2 = a + 5 by omega]
    omega)
  simpa only [show a + 3 - 1 = a + 2 by omega, show (a+7)*(a+2) + 1 + 3 = (a+7)*(a+2) + 4 by omega] using h

/-! ### (P4a) every root returns from layer `i` -/

/-- **(P4a).** In a rigid host (`2 ≤ s ≤ q`, `1 ≤ i`) every root has a row of layer `i` with a head in
one of the layers `1 … i-1`. -/
theorem inner_return (R : Rigid D V q s i) (hs : 2 ≤ s) (hsq : s ≤ q) (hi : 1 ≤ i) {u : ℕ}
    (hu : u ∈ V) : ∃ x ∈ layer D V i u, ∃ y ∈ outN D V x, ∃ j, 1 ≤ j ∧ j < i ∧ y ∈ layer D V j u := by
  by_contra! none
  have keep : ∀ x ∈ layer D V i u, outN D V x ⊆ layer D V i u ∪ layer D V (i+1) u := by
    intro x xm y ym
    obtain ⟨j, j1, j2, hj⟩ := ShapeClimbRoot.head_mem R.free hu hi (by rw [R.odd]; omega) xm ym
    rcases (by omega : j < i ∨ j = i ∨ j = i + 1) with h | rfl | rfl
    · exact absurd hj (none x xm y ym j j1 h)
    · exact mem_union_left _ hj
    · exact mem_union_right _ hj
  have ant := antipode_card R hu
  have ne : (layer D V i u).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro e
    have e' := ShapeClimbRoot.layer_empty_next (D := D) (V := V) hu (i := i-1)
      (by rwa [Nat.sub_add_cancel hi])
    rw [show i - 1 + 2 = i + 1 by omega] at e'
    rw [e'] at ant
    simp at ant
    omega
  have big : q + 1 ≤ (layer D V i u).card := layer_host_order (c := 1) R.free (sdiff_subset.trans ball_subset) ne
    (fun v hv => R.degree v (sdiff_subset.trans ball_subset hv)) keep (by omega) (order_one q)
  have e := card_ball_succ (D := D) (V := V) (u := u) (i-1)
  rw [Nat.sub_add_cancel hi, R.inner u hu] at e
  have f := R.floor (i-1) (by omega) u hu
  have m : s*i = s*(i-1) + s := by rw [← Nat.mul_succ]; congr 1; omega
  omega

/-! ### (P4b) a root flat to `i - 2` -/

theorem layer_card_of_flat {u : ℕ} {k : ℕ} (hk : 1 ≤ k)
    (flat : ∀ k' ≤ k, (ball D V u k').card = s*k' + 1) : (layer D V k u).card = s := by
  have e := card_ball_succ (D := D) (V := V) (u := u) (k-1)
  rw [Nat.sub_add_cancel hk, flat k le_rfl, flat (k-1) (by omega)] at e
  have m : s*k = s*(k-1) + s := by rw [← Nat.mul_succ]; congr 1; omega
  omega

/-- **(P4b).** In a rigid host (`2 ≤ s`, `s + 2 ≤ q`, `3 ≤ i`), a root whose first `i - 2` layers have
width `s` has `|layer (i-1)| ≥ s + 2` and `2 q + 1 ≤ s + |layer (i-1)|`. -/
theorem flat_inner_wide (R : Rigid D V q s i) (hs : 2 ≤ s) (hsq : s + 2 ≤ q) (hi : 3 ≤ i) {u : ℕ}
    (hu : u ∈ V) (flat : ∀ k ≤ i-2, (ball D V u k).card = s*k + 1) :
    s + 2 ≤ (layer D V (i-1) u).card ∧ 2*q + 1 ≤ s + (layer D V (i-1) u).card := by
  have hq1 : q = 2*i+1 := R.odd
  set w := (layer D V (i-1) u).card with hw
  have e1 := card_ball_succ (D := D) (V := V) (u := u) (i-2)
  rw [show i - 2 + 1 = i - 1 by omega, flat (i-2) le_rfl] at e1
  have e2 := card_ball_succ (D := D) (V := V) (u := u) (i-1)
  rw [show i - 1 + 1 = i by omega, R.inner u hu, e1] at e2
  have m1 : s*(i-1) = s*(i-2) + s := by rw [← Nat.mul_succ]; congr 1; omega
  have m2 : s*i = s*(i-1) + s := by rw [← Nat.mul_succ]; congr 1; omega
  -- `w + |layer i| = 2 s`
  have sum2 : w + (layer D V i u).card = 2*s := by omega
  -- the abstract layers `L j = layer (j+1)`
  have deg := R.degree
  have flatL : ∀ j, j < i - 2 → (layer D V (j+1) u).card = s := fun j hj =>
    layer_card_of_flat (by omega) (fun k' hk' => flat k' (by omega))
  have stepL : ∀ j, j ≤ i - 2 → ∀ v ∈ layer D V (j+1) u, ∀ x ∈ outN D V v,
      ∃ j', j' ≤ j + 1 ∧ x ∈ layer D V (j'+1) u := by
    intro j hj v hv x hx
    obtain ⟨j', j1, j2, hj'⟩ := ShapeClimbRoot.head_mem R.free hu (i := j+1) (by omega) (by omega) hv hx
    exact ⟨j' - 1, by omega, by rwa [Nat.sub_add_cancel j1]⟩
  have parL : 1 ≤ i - 2 → ∀ x ∈ layer D V (i-2+1) u, ∃ p ∈ layer D V (i-2-1+1) u, D p x = true := by
    intro _ x xm
    rw [show i - 2 - 1 + 1 = i - 2 by omega]
    exact ShapeClimbRoot.parent_mem hu (i := i-2) (by omega) xm
  have subL : ∀ j, layer D V (j+1) u ⊆ V := fun j => sdiff_subset.trans ball_subset
  have quotaL : ∀ j, j ≤ i - 2 → ∀ v ∈ layer D V (j+1) u, s ≤ (outN D V v).card :=
    fun j _ v hv => deg v (subL j hv)
  have gi : i - 2 + 1 = i - 1 := by omega
  have gi' : i - 2 + 1 + 1 = i := by omega
  -- the four cases on `w`
  rcases (by omega : w < s ∨ w = s ∨ w = s + 1 ∨ s + 2 ≤ w) with lt | eq | one | big
  · exfalso
    exact FlatPersist.flat_root_persist (h := i-2) R.free (by omega) (by omega) (by omega)
      (by omega) deg hu flat (by rw [show i - 2 + 1 = i - 1 by omega]; omega)
  · exfalso
    refine FlatPersist.flat_root_persist (h := i) R.free (by omega) (by omega) (by omega)
      (by omega) deg hu (fun k hk => ?_) (by rw [R.outer u hu])
    rcases (by omega : k ≤ i - 2 ∨ k = i - 1 ∨ k = i) with h | rfl | rfl
    · exact flat k h
    · rw [e1]; omega
    · exact R.inner u hu
  · exfalso
    exact unit_dip_false (g := i-2) (fun j => layer D V (j+1) u) R.free (by omega) hsq (by omega)
      (by omega) subL flatL (by simp only [gi]; omega) (by simp only [gi']; omega) quotaL stepL parL
  · refine ⟨big, ?_⟩
    have := wide_dip_order (g := i-2) (c := 2) (fun j => layer D V (j+1) u) R.free (by omega) hsq
      (by omega) (by omega) subL flatL quotaL stepL parL (by simp only [gi']; omega)
      (order_two (by omega))
    simp only [gi] at this
    omega

/-- **(P4b), closed form.** If also `3 s < 2 q + 1`, no root of a rigid host is flat to `i - 2`. -/
theorem flat_inner_false (R : Rigid D V q s i) (hs : 2 ≤ s) (hsq : s + 2 ≤ q) (hi : 3 ≤ i)
    (room : 3*s < 2*q + 1) {u : ℕ} (hu : u ∈ V) (flat : ∀ k ≤ i-2, (ball D V u k).card = s*k + 1) :
    False := by
  obtain ⟨-, b⟩ := flat_inner_wide R hs hsq hi hu flat
  have e1 := card_ball_succ (D := D) (V := V) (u := u) (i-2)
  rw [show i - 2 + 1 = i - 1 by omega, flat (i-2) le_rfl] at e1
  have e2 := card_ball_succ (D := D) (V := V) (u := u) (i-1)
  rw [show i - 1 + 1 = i by omega, R.inner u hu, e1] at e2
  have m1 : s*(i-1) = s*(i-2) + s := by rw [← Nat.mul_succ]; congr 1; omega
  have m2 : s*i = s*(i-1) + s := by rw [← Nat.mul_succ]; congr 1; omega
  omega

/-- **Fifth strip, `a ≥ 7`.** At the top order every root has a radius `k ≤ a + 1 = i - 2` with
`|ball k| ≥ s k + 2`. -/
theorem fifth_not_flat {a : ℕ} (ha : 7 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    (free : QFree D V (2*a+7)) (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) {u : ℕ} (hu : u ∈ V) :
    ∃ k ≤ a + 1, (a+7)*k + 2 ≤ (ball D V u k).card := by
  have R := rigid_of_top (by omega) L tc free degree size
  by_contra! h
  exact flat_inner_false R (by omega) (by omega) (by omega) (by omega) hu (fun k hk =>
    le_antisymm (by have := h k (by omega); omega) (R.floor k (by omega) u hu))

/-- **The residual root (fifth strip, `a ≥ 7`).** Some root has `E_{i-1} ≤ 3` (`|ball (a+2)| ≤ s (a+2) + 4`)
and a radius `k ≤ i - 2 = a + 1` with `E_k ≥ 1` (`|ball k| ≥ s k + 2`). Excluding such a root closes the
top order. -/
theorem fifth_residual {a : ℕ} (ha : 7 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    (free : QFree D V (2*a+7)) (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) :
    ∃ v ∈ V, (ball D V v (a+2)).card ≤ (a+7)*(a+2) + 4 ∧
      ∃ k ≤ a + 1, (a+7)*k + 2 ≤ (ball D V v k).card := by
  obtain ⟨v, hv, small⟩ := fifth_small_root (by omega) L tc free degree size
  exact ⟨v, hv, small, fifth_not_flat ha L tc free degree size hv⟩

#print axioms small_root
#print axioms fifth_small_root
#print axioms inner_return
#print axioms layer_card_of_flat
#print axioms flat_inner_wide
#print axioms flat_inner_false
#print axioms fifth_not_flat
#print axioms fifth_residual
end LeanCH.BR.RigidDip
