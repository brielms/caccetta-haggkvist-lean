import checkpoints.shen_extension.Supplier54
import checkpoints.shen_extension.Profile54

/-!
# Supplier54 without hypotheses

`tables`: the fields of `Supplier54.Tables` are `Profile54`'s Lemma 3 (`reach_three_two … five`,
`nine_row`) and Lemma P (`budget_floor`). The B2, B3, B4 statements of `Supplier54` follow
unconditionally (`q = 6`, `r = 9`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Supplier54Close
open Finset BRq2 BRq3 ThinSuppliers OneHead Supplier54
open DotTwoPassShellTransport (layer)

variable {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- Lemma 3 and Lemma P from `Profile54`. -/
theorem tables : Tables D where
  t2 _ fr dg _ hx := Profile54.reach_three_two fr hx le_rfl dg
  t3 _ fr dg _ hx := Profile54.reach_three_three fr hx le_rfl dg
  t4 _ fr dg _ hx := Profile54.reach_three_four fr hx le_rfl dg
  t5 _ fr dg _ hx := Profile54.reach_three_five fr hx le_rfl dg
  nine _ fr dg _ hx h9 := Profile54.nine_row fr hx h9 dg
  budget _ fr _ XF _ _ hX hR := Profile54.budget_floor fr le_rfl XF hX hR

/-- **B2.** `(w_2, w_3) = (8, 8)`: `|W| + |J| ≥ 16`. -/
theorem wj_sixteen' (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) : 16 ≤ (layer D V 4 u).card + (layer D V 5 u).card :=
  wj_sixteen tables free reg hu tight

/-- **B2.** `(w_2, w_3) = (8, 8)`: a row of `Y` complete to `Z` has `|B_3| ≥ 28`. -/
theorem complete_y_28' (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) {s : ℕ} (hs : s ∈ layer D V 2 u)
    (full : layer D V 3 u ⊆ outN D V s) : 28 ≤ (ball D V s 3).card :=
  complete_y_28 tables free reg hu tight hs full

/-- **B3.** Thin root with `|B_3| = 27`: `|W| ≥ 8`. -/
theorem w_eight' (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (thin : Thin D V 9 u) (b3 : (ball D V u 3).card = 27) : 8 ≤ (layer D V 4 u).card :=
  w_eight tables free reg hu thin b3

/-- **B3.** Thin root with `|B_3| = 27`: every complete head has `|B_3| ≥ 29`. -/
theorem complete_x_29' (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (thin : Thin D V 9 u) (b3 : (ball D V u 3).card = 27) {x : ℕ} (hx : x ∈ complete D V u) :
    29 ≤ (ball D V x 3).card :=
  complete_x_29 tables free reg hu thin b3 hx

/-- **B4.** `(w_2, w_3) = (8, 8)`: at least five rows in `zSet D V (layer D V 3 u)`. -/
theorem zSet_count' (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) : 5 ≤ (zSet D V (layer D V 3 u)).card :=
  zSet_count tables free reg hu tight

#print axioms tables
#print axioms wj_sixteen'
#print axioms complete_y_28'
#print axioms w_eight'
#print axioms complete_x_29'
#print axioms zSet_count'

end LeanCH.BR.Supplier54Close
