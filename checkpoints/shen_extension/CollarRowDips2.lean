import checkpoints.shen_extension.CollarRowDips

/-!
# B2 on the row `r = q + 1`: reduction to a one-return law

A root `u` of out-degree exactly `q + 1`, layers `X, Y, Z, W`. B2 says: widths
`(q + 1, q + 1, q + 1)` force `|W| ≥ q`.

`CollarRowDips.flat_run_residual` (`6 ≤ q`) leaves one configuration: a label `t ∈ Y` whose
heads are exactly `Z`. This file reduces B2 to one law about that configuration:

* `OnceReturn D V u`: if some `t ∈ Y` has `outN t = Z`, then at most one label of `Z` has a head
  in `X ∪ Y`.
* `flat_run_fourth_of_once` (`6 ≤ q`): `OnceReturn` implies B2. If `z₀` is the only returning
  label, a sink of `D[Z - z₀]` has all its `q + 1` heads in `W ∪ {z₀}`.

`OnceReturn` is **not proved here**. Small-case SAT inspection (local radius-4 ball, all rows of
`u, X, Y, Z` of out-degree at least `q + 1` with heads inside the ball, no cycle of length at most
`q`, `W` unconstrained) finds no counterexample at `q = 4, 5, 6`: two returning labels of `Z` are
impossible once `t` exists. The same inspection shows, for one return `z → p` (`q = 6`): `p ∈ Y`
(never `X`, for `q ≥ 5`), `p` has no head in `X`, and at most one label of `Y - t` points to `z`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarRowDips
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open TubeAtCutoff (IsSink too_few row_ball classify x_ball layer_in layer_out)

variable {D : CH.Digraph}

/-- **The one-return law** at the root `u`: if a label `t` of the second layer has exactly the
third layer as its heads, at most one label of the third layer has a head in the first two
layers. -/
def OnceReturn (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop :=
  ∀ t ∈ layer D V 2 u, outN D V t = layer D V 3 u →
    ∀ z₁ ∈ layer D V 3 u, ∀ z₂ ∈ layer D V 3 u, ∀ w₁ ∈ V, ∀ w₂ ∈ V,
      D z₁ w₁ = true → D z₂ w₂ = true →
      (w₁ ∈ outN D V u ∨ w₁ ∈ layer D V 2 u) → (w₂ ∈ outN D V u ∨ w₂ ∈ layer D V 2 u) →
      z₁ = z₂

/-- **B2 from the one-return law.** A root with exactly `q + 1` heads and exactly `q + 1` labels
in its second and third layers, in a `q`-free digraph of minimum out-degree at least `q + 1`,
`6 ≤ q`, satisfying `OnceReturn`: the fourth layer has at least `q` labels. -/
theorem flat_run_fourth_of_once {V : Finset ℕ} {q u : ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (hu : u ∈ V) (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (second : (layer D V 2 u).card = q + 1) (third : (layer D V 3 u).card = q + 1)
    (once : OnceReturn D V u) :
    q ≤ (layer D V 4 u).card := by
  classical
  by_contra! thin
  obtain ⟨t, tY, tZ, -⟩ := flat_run_residual free hq hu heads deg second third (by omega)
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set W := layer D V 4 u with hWdef
  have hZ : Z ⊆ V := fun w hw => ball_subset (layer_in hw)
  have fZ : QFree D Z q := free.mono_set hZ
  have rowZ : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z ∨ w ∈ W := by
    intro z hz w wV zw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hz) wV zw (by omega)
    exact classify hu wb wu
  have one := once t tY tZ
  obtain ⟨z0, hz0, keep⟩ : ∃ z0 ∈ Z, ∀ z ∈ Z, z ≠ z0 → ∀ w ∈ V, D z w = true → w ∈ Z ∨ w ∈ W := by
    by_cases some : ∃ z ∈ Z, ∃ w ∈ V, D z w = true ∧ (w ∈ X ∨ w ∈ Y)
    · obtain ⟨z0, hz0, w0, w0V, zw0, hw0⟩ := some
      refine ⟨z0, hz0, fun z hz ne w wV zw => ?_⟩
      rcases rowZ z hz w wV zw with h | h | h | h
      · exact (ne (one z hz z0 hz0 w wV w0 w0V zw zw0 (Or.inl h) hw0)).elim
      · exact (ne (one z hz z0 hz0 w wV w0 w0V zw zw0 (Or.inr h) hw0)).elim
      · exact Or.inl h
      · exact Or.inr h
    · obtain ⟨z0, hz0⟩ : Z.Nonempty := card_pos.mp (by omega)
      refine ⟨z0, hz0, fun z hz _ w wV zw => ?_⟩
      rcases rowZ z hz w wV zw with h | h | h | h
      · exact (some ⟨z, hz, w, wV, zw, Or.inl h⟩).elim
      · exact (some ⟨z, hz, w, wV, zw, Or.inr h⟩).elim
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨s, sZ', ssink⟩ := exists_sink (fZ.mono_set (erase_subset z0 Z))
    (card_pos.mp (by rw [card_erase_of_mem hz0]; omega)) (by rw [card_erase_of_mem hz0]; omega)
  have sZ := mem_of_mem_erase sZ'
  refine too_few (V := V) (T := insert z0 W) ?_
    (by have := card_insert_le z0 W; omega) (deg s (hZ sZ))
  intro w hw
  obtain ⟨wV, sw⟩ := mem_outN.mp hw
  rcases keep s sZ (ne_of_mem_erase sZ') w wV sw with h | h
  · by_cases e : w = z0
    · rw [e]; exact mem_insert_self _ _
    · exact (ssink w (mem_erase.mpr ⟨e, h⟩) sw).elim
  · exact mem_insert_of_mem h

/-- B2 as a width pattern: `r = q + 1`, `6 ≤ q`, widths `(r, r, r)`, fourth at most `r - 2`. -/
def dipB2 (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (q + 1 = r ∧ 6 ≤ q ∧ 3 ≤ ws.length ∧ ws.getD 1 0 = r ∧ ws.getD 2 0 = r ∧
    (if 4 ≤ ws.length then ws.getD 3 0 else last) + 2 ≤ r)

/-- `dipB2` is sound wherever the one-return law holds. -/
theorem dipB2_sound_of_once (q r : ℕ) (law : ∀ (D : CH.Digraph) (V : Finset ℕ) (u : ℕ),
    QFree D V q → (∀ v ∈ V, r ≤ (outN D V v).card) → u ∈ V → OnceReturn D V u) :
    ShapeClimbX.SoundX q r (dipB2 q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨qr, hq, len, w2, w3, w4⟩ := of_decide_eq_true h
  subst qr
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := flat_run_fourth_of_once free hq hu root deg (by omega) (by omega)
    (law D V u free deg hu)
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    have e : ws.length + 1 = 4 := by omega
    rw [e] at bound
    omega

#print axioms flat_run_fourth_of_once
#print axioms dipB2_sound_of_once
end LeanCH.BR.CollarRowDips
