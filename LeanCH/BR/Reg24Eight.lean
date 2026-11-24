import LeanCH.BR.BR36Root

/-!
# The 8-vertex lemma (Lemma 1(v) of `Z8_attempt_subagent.md`), Lean 4.35.0

Paper source: `checkpoints/boundary_20261111/Z8_attempt_subagent.md`, Lemma 1 (audited in
`Z8_audit_subagent.md`). Only the bound `e ≤ 21` of (v) is formalised, not its equality clause.

Setting: a set `S` of 8 labels in a loopless digraph without directed cycles of length `≤ 3`, in
which every member has at least 2 heads inside `S`.

* `closure` (Lemma 1(i)): for `y ∈ N⁺_S(x)`, every head of `y` in `S` lies in
  `C(x) := {z ∈ S ∖ x : z ↛ x}`.
* `eight_vertex`: every `x ∈ S` has `2 in_S(x) + out_S(x) ≤ 8`.
* `eight_arcs` (Lemma 1(v)): `e(S) ≤ 21`, by summing `eight_vertex` (`3e ≤ 64`).

Departure from the paper: (iii)-(v) are replaced by the single weighted inequality
`2 in + out ≤ 8`, the supporting line of the paper's feasible `(in, out)` pairs. Since
`|C(x)| = 7 - in_S(x)`, it says `out + 6 ≤ 2 |C(x)|`. A failure has one of two shapes:
* `N⁺_S(x) = C(x)` with at most 5 vertices, excluded by CH(2) (`BR(3,2)` through `ch_subset`);
* `|C(x)| = out + 1` with `out ≤ 3`, excluded by `small_out`: every head of `x` then has a head
  inside `N⁺_S(x)`.
-/

namespace LeanCH.BR.Reg24

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

variable {G : CH.Digraph} {n : Nat}

/-- **Closure (Lemma 1(i)).** If `x → y` inside `S`, every head of `y` in `S` is neither `x` nor
a parent of `x`. -/
theorem closure (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {S : Finset Nat} (hS : S ⊆ Finset.range n) {x y : Nat} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : G x y = true) :
    oc G S y ≤ oc G ((S.erase x).filter (fun z => ¬ G z x = true)) y := by
  have lt : ∀ z ∈ S, z < n := fun z hz => Finset.mem_range.mp (hS hz)
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzS, hyz⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hzS⟩, ?_⟩, hyz⟩
  · rintro rfl
    exact no2 loopless noShort (lt z hx) (lt y hy) hxy hyz
  · intro hzx
    exact no3 loopless noShort (lt x hx) (lt y hy) (lt z hzS) hxy hyz hzx

/-- **Per-vertex bound.** In an 8-set with internal minimum out-degree 2,
`2 in_S(x) + out_S(x) ≤ 8`. -/
theorem eight_vertex (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {S : Finset Nat} (hS : S ⊆ Finset.range n) (hcard : S.card = 8)
    (keep : ∀ x ∈ S, 2 ≤ oc G S x) {x : Nat} (hx : x ∈ S) :
    2 * ic G S x + oc G S x ≤ 8 := by
  classical
  have lt : ∀ z ∈ S, z < n := fun z hz => Finset.mem_range.mp (hS hz)
  set Y := S.filter (fun y => G x y = true) with hY
  set C := (S.erase x).filter (fun z => ¬ G z x = true) with hC
  have hYc : Y.card = oc G S x := rfl
  -- `|C| + in_S(x) = 7`
  have hCcard : C.card + ic G S x = 7 := by
    have h1 : ((S.erase x).filter (fun z => G z x = true)).card + C.card = (S.erase x).card :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.card_erase_of_mem hx, hcard] at h1
    have h2 : ((S.erase x).filter (fun z => G z x = true)).card = ic G S x :=
      ic_erase_eq (loopless x (lt x hx))
    omega
  -- `N⁺_S(x) ⊆ C`
  have hYC : Y ⊆ C := by
    intro y hy
    obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hyS⟩, ?_⟩
    · rintro rfl; rw [loopless y (lt y hyS)] at hxy; exact Bool.false_ne_true hxy
    · intro hyx; exact no2 loopless noShort (lt x hx) (lt y hyS) hxy hyx
  -- every head of `x` keeps 2 heads inside `C`
  have hkeep : ∀ y ∈ Y, 2 ≤ oc G C y := by
    intro y hy
    obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
    exact le_trans (keep y hyS) (closure loopless noShort hS hx hyS hxy)
  have hYle : Y.card ≤ C.card := Finset.card_le_card hYC
  have hx2 := keep x hx
  have hCS : C ⊆ Finset.range n := fun z hz =>
    hS (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1)
  by_contra hcon
  rcases (by omega : C.card ≤ Y.card ∨ C.card = Y.card + 1 ∨ Y.card + 2 ≤ C.card) with h | h | h
  · -- `N⁺_S(x) = C`, a set of at most 5 vertices with internal minimum out-degree 2: CH(2)
    have hEq : Y = C := Finset.eq_of_subset_of_card_le hYC h
    rw [hEq] at hkeep
    exact LeanCH.BR.BR36.ch_subset (by norm_num) LeanCH.BR.SmallBR.br_two hCS
      (Finset.card_pos.mp (by omega)) (by omega) loopless noShort hkeep
  · -- `C = N⁺_S(x) + one vertex` and `out_S(x) ≤ 3`: every head has a head inside `N⁺_S(x)`
    have hYS : Y ⊆ Finset.range n := fun z hz => hCS (hYC hz)
    refine small_out loopless noShort hYS (by omega) (Finset.card_pos.mp (by omega)) ?_
    intro y hy
    have h1 := oc_sdiff (G := G) hYC y
    have h2 := oc_le (G := G) (C \ Y) y
    have h3 := Finset.card_sdiff_add_card_eq_card hYC
    have h4 := hkeep y hy
    exact exists_of_oc (by omega)
  · omega

/-- **Lemma 1(v).** An 8-set with internal minimum out-degree 2 spans at most 21 arcs. -/
theorem eight_arcs (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {S : Finset Nat} (hS : S ⊆ Finset.range n) (hcard : S.card = 8)
    (keep : ∀ x ∈ S, 2 ≤ oc G S x) : ∑ x ∈ S, oc G S x ≤ 21 := by
  have h := Finset.sum_le_sum (fun x hx => eight_vertex loopless noShort hS hcard keep hx)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, smul_eq_mul] at h
  have hs := swap G S S
  omega

end LeanCH.BR.Reg24
