import checkpoints.shen_extension.FifthStripAllTop
import checkpoints.shen_extension.EqualLayerTransit
import checkpoints.shen_extension.ShapeClimbRoot

/-!
# Fifth strip, top order `qs`, even degree: the parity gap

Cutoff `q = 2a + 7`, degree `s = a + 7`, `a` odd (so `s` is even). Radii `i = a + 3`, `j = a + 4`.

* `seymour_inball`: Seymour on the reach relation `y ∈ ball x k`, capped by
  the in-ball through the two-ball bound. If `2k + r ≤ q`, every `k`-ball has `≥ f` labels and
  every reverse `r`-ball has `≥ g` labels, then `2f + g ≤ |V| + 2`.
* `parity_close_of_infloor`: for odd `a ≥ 5`, a host of order `qs` needs some vertex whose reverse
  `a`-ball has at most `s·a` labels. If every reverse `a`-ball has `≥ s·a + 1` labels, no such host exists.
  Variant `parity_close_of_infloor2` covers `a ≥ 3`, with the floor at radius `a + 2`.
* `tr`, `reverseBall_eq_ball_tr`, `qfree_tr`: the transpose digraph. Reverse balls are the
  transpose's balls.
* `parity_close_of_indegree`: odd `a ≥ 5`, order `qs`, minimum in-degree `≥ s` as well as
  out-degree ⇒ `False`. No rigidity and no ledger are used.
* `rigid_inball_deficit`: in any host of order `qs` (odd `a ≥ 5`) some vertex has a deficient reverse
  `a`-ball. This is the exact obstruction left in the even-`s` case.
* `flat_root_false` / `rigid_flat_false`: brief's fact 4. In the rigid configuration no
  root has all of its first `i` layers of width exactly `s`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAllParity
open Finset BRq2 BRq3 BR45 FifthStripAll
open DotTwoPassShellTransport (layer)

/-- **Seymour with an in-ball cap.** -/
theorem seymour_inball {D : CH.Digraph} {V : Finset ℕ} {q k r f g : ℕ}
    (free : QFree D V q) (hq : 2*k + r ≤ q) (ne : V.Nonempty)
    (first : ∀ v ∈ V, f ≤ (ball D V v k).card)
    (inn : ∀ v ∈ V, g ≤ (reverseBall D V v r).card) : 2*f + g ≤ V.card + 2 := by
  obtain ⟨v0, hv0⟩ := ne
  have g0 := inn v0 hv0
  have h := reach_seymour (A := V.card + 1 - g) free (by omega) ⟨v0, hv0⟩ first
    (fun v hv => by
      have := reverseBall_add_ball_le (v := v) (i := 2*k) (j := r) free (by omega)
      have := inn v hv
      omega)
  have := reverseBall_add_ball_le (v := v0) (i := 2*k) (j := r) free (by omega)
  omega

/-- Odd `a = 2m+1 ≥ 5`: an in-floor at radius `a` closes order `qs`. -/
theorem parity_close_of_infloor {a m : ℕ} (hm : a = 2*m+1) (m2 : 2 ≤ m)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7))
    (inn : ∀ v ∈ V, (a+7)*a+1 ≤ (reverseBall D V v a).card) : False := by
  have h := seymour_inball (k := m+4) (f := (a+7)*(m+4)+1) free (by omega) ne
    (fun v hv => ShenFifthStrip.inner_growth free degree hv (m+4) (by omega)) inn
  have e : (2*a+7)*(a+7) = 2*((a+7)*(m+4)) + (a+7)*a := by subst hm; ring
  omega

/-- Odd `a = 2m+1 ≥ 3`: an in-floor at radius `a+2` closes order `qs`. -/
theorem parity_close_of_infloor2 {a m : ℕ} (hm : a = 2*m+1) (m1 : 1 ≤ m)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7))
    (inn : ∀ v ∈ V, (a+7)*(a+2)+1 ≤ (reverseBall D V v (a+2)).card) : False := by
  have h := seymour_inball (k := m+3) (f := (a+7)*(m+3)+1) free (by omega) ne
    (fun v hv => ShenFifthStrip.inner_growth free degree hv (m+3) (by omega)) inn
  have e : (2*a+7)*(a+7) = 2*((a+7)*(m+3)) + (a+7)*(a+2) := by subst hm; ring
  omega

/-- The exact obstruction: in a host of order `qs`, odd `a ≥ 5`, some vertex has a deficient
reverse `a`-ball (and, for `a ≥ 3`, some vertex has a deficient reverse `(a+2)`-ball). -/
theorem rigid_inball_deficit {a m : ℕ} (hm : a = 2*m+1) (m2 : 2 ≤ m)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7)) :
    (∃ y ∈ V, (reverseBall D V y a).card ≤ (a+7)*a) ∧
      ∃ y ∈ V, (reverseBall D V y (a+2)).card ≤ (a+7)*(a+2) := by
  constructor
  · by_contra h
    push Not at h
    exact parity_close_of_infloor hm m2 free degree ne size (fun v hv => h v hv)
  · by_contra h
    push Not at h
    exact parity_close_of_infloor2 hm (by omega) free degree ne size (fun v hv => h v hv)

/-! ### The transpose digraph -/

/-- The transpose digraph. -/
def tr (D : CH.Digraph) : CH.Digraph := fun v w => D w v

theorem walk_tr {D : CH.Digraph} {V : Finset ℕ} {a b m : ℕ} (w : Walk D V a b m) (ha : a ∈ V) :
    Walk (tr D) V b a m := by
  induction w with
  | refl a => exact .refl a
  | @step a b c k hb hab _ ih =>
    have := (ih hb).snoc ha (show tr D b a = true from hab)
    simpa using this

theorem walk_tr_tr {D : CH.Digraph} {V : Finset ℕ} {a b m : ℕ} (w : Walk (tr D) V a b m)
    (ha : a ∈ V) : Walk D V b a m := walk_tr (D := tr D) w ha

theorem qfree_tr {D : CH.Digraph} {V : Finset ℕ} {q : ℕ} (free : QFree D V q) :
    QFree (tr D) V q := by
  intro a ℓ h1 h2 w
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨_, _, ha, _⟩ := w.unsnoc
  exact free a (m+1) h1 h2 (walk_tr_tr w ha)

theorem reverseBall_eq_ball_tr {D : CH.Digraph} {V : Finset ℕ} {v k : ℕ} (hv : v ∈ V) :
    reverseBall D V v k = ball (tr D) V v k := by
  ext u
  simp only [reverseBall, mem_filter, mem_ball]
  constructor
  · rintro ⟨hu, -, j, hj, w⟩
    exact ⟨hu, j, hj, walk_tr w hu⟩
  · rintro ⟨hu, j, hj, w⟩
    exact ⟨hu, hv, j, hj, walk_tr_tr w hv⟩

theorem outN_tr {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} :
    outN (tr D) V v = V.filter (fun w => D w v = true) := rfl

/-- **Even `s`, both degrees `≥ s`.** Odd `a ≥ 5`: no `q`-free host of order `qs` has minimum
out-degree and minimum in-degree `≥ s`. -/
theorem parity_close_of_indegree {a m : ℕ} (hm : a = 2*m+1) (m2 : 2 ≤ m)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (indegree : ∀ v ∈ V, a+7 ≤ (V.filter (fun w => D w v = true)).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7)) : False :=
  parity_close_of_infloor hm m2 free degree ne size (fun v hv => by
    rw [reverseBall_eq_ball_tr hv]
    exact ShenFifthStrip.inner_growth (qfree_tr free) (fun w hw => by rw [outN_tr]; exact indegree w hw)
      hv a (by omega))

/-! ### Fact 4: a flat root is impossible -/

/-- `h` layers of width exactly `r` around a root, then a layer of width `< r`: impossible. -/
theorem flat_root_false {D : CH.Digraph} {V : Finset ℕ} {q r h u : ℕ}
    (free : QFree D V q) (hr : 0 < r) (hq : r < q) (height : r/2 + h ≤ q) (depth : 0 < h)
    (time : h + 1 ≤ q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (flat : ∀ k ≤ h, (ball D V u k).card = r*k + 1)
    (short : (ball D V u (h+1)).card ≤ r*(h+1)) : False := by
  have lay : ∀ k, k < h → (layer D V (k+1) u).card = r := by
    intro k hk
    have e := ShapeClimbRoot.card_ball_succ (D := D) (V := V) (u := u) k
    rw [flat (k+1) (by omega), flat k (by omega)] at e
    have : r*(k+1) = r*k + r := by ring
    omega
  have cap := EqualLayerTransit.end_capacity (D := D) (V := V) (q := q) (r := r) (h := h)
    (fun i => layer D V (i+1) u) free hr hq height depth
    (fun i => sdiff_subset.trans ball_subset) lay
    (fun i _ => ShapeClimbRoot.layer_disjoint (by omega))
    (fun i _ v hv => degree v (sdiff_subset.trans ball_subset hv))
    (fun i hi v hv x hx => by
      obtain ⟨j, j1, j2, hj⟩ := ShapeClimbRoot.head_mem free hu (i := i+1) (by omega) (by omega) hv hx
      exact ⟨j - 1, by omega, by rwa [Nat.sub_add_cancel j1]⟩)
  have e := ShapeClimbRoot.card_ball_succ (D := D) (V := V) (u := u) h
  rw [flat h le_rfl] at e
  have : r*(h+1) = r*h + r := by ring

  omega

/-- **Fact 4 in the rigid configuration.** At order `qs` (`a ≥ 2`), no root has
`|ball k| = s k + 1` for every `k ≤ i = a + 3`. -/
theorem rigid_flat_false {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) {u : ℕ} (hu : u ∈ V)
    (flat : ∀ k ≤ a+3, (ball D V u k).card = (a+7)*k + 1) : False := by
  have rig := top_rigid ha L tc free degree size u hu
  exact flat_root_false free (by omega) (by omega) (by omega) (by omega) (by omega) degree hu flat
    (by rw [show a+3+1 = a+4 by omega, rig.2])

#print axioms seymour_inball
#print axioms parity_close_of_infloor
#print axioms parity_close_of_infloor2
#print axioms rigid_inball_deficit
#print axioms parity_close_of_indegree
#print axioms flat_root_false
#print axioms rigid_flat_false

/-- **Reduction to the next out-layer.** Odd `a = 2m+1 ≥ 3`, order `qs`: if every out-ball at
radius `j + 1 = a + 5` has `≥ s(a+5)` labels, the two-ball bound at `(a+5, a+2)`, together with
`Σ reverse = Σ forward` and the out-floor `L.f2`, makes every reverse `(a+2)`-ball exactly
`s(a+2)+1`, and `parity_close_of_infloor2` applies. No rigidity is used. -/
theorem parity_close_of_next_layer {a m : ℕ} (hm : a = 2*m+1) (m1 : 1 ≤ m) (L : LedgerFloors a)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7))
    (next : ∀ v ∈ V, (a+7)*(a+5) ≤ (ball D V v (a+5)).card) : False := by
  have r := two_balls_boundary_cards (q := 2*a+7) (i := a+5) (j := a+2)
    (a := (a+7)*(a+5)) (b := (a+7)*(a+2)+1) free (by omega) next
    (fun v hv => L.f2 D V free degree v hv) (by
      have e : (2*a+7)*(a+7) = (a+7)*(a+5) + (a+7)*(a+2) := by ring
      omega)
  exact parity_close_of_infloor2 hm m1 free degree ne size (fun v hv => (r v hv).2.2.ge)

#print axioms parity_close_of_next_layer
end LeanCH.BR.FifthStripAllParity
