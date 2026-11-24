import checkpoints.shen_extension.ReachLedgerCatalog

/-!
# The strict count on the cutoff-four diagonal, for every degree

Lean 4.35.0. Free parameters: the graph, the order `n = |V|`, the cutoff `q ≥ 4`, the degree `r`
and the third-ball floor `b`. No number is fixed.

Setting: a `q`-free graph with exact outdegree `r`. In closed-ball units, call a row
*tight* when `|ball v 2| = 2r`, *high* when `|ball v 2| = 2r + 1`, *strict* when
`|ball v 2| > 2r + 1`. Hypotheses, all graph statements with `r` free:

* `floor2`: `2r ≤ |ball v 2|` for every row (the paper's `f₂ ≥ 2r − 1`);
* `floor3`: `b ≤ |ball v 3|` for every row, with `3r ≤ b + 1` (the paper's `f₃ ≥ 3r − 2`);
* `regular`: no tight row that heads no strict row has a first layer keeping two heads inside on
  every row.

Results:

* `strict_core`: the supplier law, the tied chains and the classes of roots leave two linear
  facts about the number `c` of second-shell classes.
* `strict_count`: `c` eliminated; one inequality in `n`, `q`, `r`, `b`, the number of strict rows,
  their excess and the gaps.
* `below_diagonal`: at `n = 4r − 1` the hypotheses are contradictory. A regime theorem.
* `two_strict_diagonal`: at `n = 4r`, the hard diagonal of cutoff four, at least two rows are
  strict. For every `r ≥ 1` and every `q ≥ 4`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.StrictCount
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

local notation "strictRows(" D ", " V ", " r ")" =>
  Finset.filter (fun v => 2 * r + 1 < Finset.card (ball D V v 2)) V
local notation "highRows(" D ", " V ", " r ")" =>
  Finset.filter (fun v => Finset.card (ball D V v 2) = 2 * r + 1) V
local notation "bankRows(" D ", " V ", " r ")" =>
  Finset.filter (fun v => outN D (Finset.filter (fun v => 2 * r + 1 < Finset.card (ball D V v 2)) V) v = ∅)
    (Finset.filter (fun v => Finset.card (ball D V v 2) = 2 * r) V)
local notation "excess(" D ", " V ", " r ")" =>
  Finset.sum V (fun v => Finset.card (ball D V v 2) - (2 * r + 2))
local notation "gaps(" D ", " V ")" => Finset.sum V (fun v => Finset.card (gap D V 2 2 v))

/-- Arithmetic: a bound containing `2 c` and a bound on `k c` combine with `c` eliminated. -/
theorem combine_classes {k L P T c R : ℕ} (X : L ≤ P + T + 2 * c) (Y : 2 * (k * c) + R ≤ P) :
    k * L + R ≤ k * (P + T) + P := by
  have Z := Nat.mul_le_mul_left k X
  have d : k * (P + T + 2 * c) = k * (P + T) + 2 * (k * c) := by ring
  omega

/-- **Strict core.** `c` is the number of distinct second shells among the tight rows that head
no strict row. The first fact is the supplier law with the roots of each class paid by gaps; the
second is the class count against the budget. -/
theorem strict_core {r b : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (exact : ∀ v ∈ V, (outN D V v).card = r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, b ≤ (ball D V v 3).card) (hb : 3 * r ≤ b + 1)
    (regular : ∀ v ∈ bankRows(D, V, r),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card) :
    ∃ c,
      2 * (V.card + (strictRows(D, V, r)).card + excess(D, V, r))
          + 2 * ((strictRows(D, V, r)).card * b) + V.card * (2 * r + 2 * r)
        ≤ V.card * (V.card + 1) + 2 * ((strictRows(D, V, r)).card * V.card) + 2 * c ∧
      2 * ((q + 1) * c) + (V.card * (2 * r + 2 * r) + gaps(D, V)
          + 4 * (strictRows(D, V, r)).card + 2 * excess(D, V, r))
        ≤ V.card * (V.card + 1) := by
  classical
  have degree : ∀ y ∈ V, r ≤ (outN D V y).card := fun y hy => (exact y hy).ge
  have sup := tight_supply (i := 2) (j := 3) (a := 2 * r) free (by omega) (by omega) floor2
  have third : ∑ _s ∈ strictRows(D, V, r), b ≤ ∑ s ∈ strictRows(D, V, r), (ball D V s 3).card :=
    sum_le_sum (fun s hs => floor3 s (mem_filter.mp hs).1)
  rw [sum_const, smul_eq_mul] at third
  have spend := budget (i := 2) (j := 2) free (by omega) floor2 floor2
  have lv := levels (fun v => (ball D V v 2).card) (2 * r) 2 V
  rw [sum_range_succ, sum_range_one] at lv
  simp only [add_zero] at lv
  have root : ∀ v ∈ bankRows(D, V, r), v ∈ V ∧ (ball D V v 1).card = r + 1 ∧
      (ball D V v 2 \ ball D V v 1).card + 1 = r ∧
      ∀ x ∈ ball D V v 1, (ball D V x 2).card ≤ 2 * r + 1 := by
    intro v hv
    obtain ⟨hT, noS⟩ := mem_filter.mp hv
    obtain ⟨vv, tight⟩ := mem_filter.mp hT
    have one : (ball D V v 1).card = r + 1 := by rw [ball_one free (by omega) vv, exact v vv]
    have incl : ball D V v 1 ⊆ ball D V v 2 := ball_mono_radius (by omega)
    have le := card_le_card incl
    refine ⟨vv, one, by rw [card_sdiff_of_subset incl, one, tight]; omega, ?_⟩
    intro x hx
    obtain ⟨xV, j, hj, walk⟩ := mem_ball.mp hx
    match j, hj, walk with
    | 0, _, walk =>
      cases walk
      omega
    | 1, _, walk =>
      cases walk with
      | step _ arc rest =>
        cases rest
        by_contra big
        have bad : x ∈ outN D (strictRows(D, V, r)) v :=
          mem_outN.mpr ⟨mem_filter.mpr ⟨xV, by omega⟩, arc⟩
        rw [noS] at bad
        simp at bad
    | n + 2, hj, _ => omega
  have live : ∀ v ∈ bankRows(D, V, r),
      ∃ x ∈ ball D V v 1, ball D V v 2 \ ball D V v 1 ⊆ outN D V x := by
    intro v hv
    obtain ⟨vv, one, sh, _⟩ := root v hv
    have cf := complete_or_fragment (t := 2) (r := r) (k := 1) (v := v) free degree vv (by omega)
    simp only [Nat.reduceAdd] at cf
    rcases cf (by omega) with h | h
    · exact h
    · exact absurd h (regular v hv)
  have high : ∀ v ∈ bankRows(D, V, r), ∀ x ∈ ball D V v 1,
      ball D V v 2 \ ball D V v 1 ⊆ outN D V x → x ∈ highRows(D, V, r) := by
    intro v hv x xk full
    obtain ⟨vv, one, sh, capv⟩ := root v hv
    have fl := complete_floor (k := 1) (r := r) (v := v) (x := x) free (by omega) degree
    simp only [Nat.reduceAdd] at fl
    have fl := fl (by omega) xk full
    have f3 := floor3 v vv
    have c := capv x xk
    exact mem_filter.mpr ⟨ball_subset xk, by omega⟩
  have cc := class_count (k := 1) (r := r) (c := 2 * r + 1) (R := bankRows(D, V, r))
    (H := highRows(D, V, r)) free (by omega) degree
  simp only [Nat.reduceAdd] at cc
  have cc := cc (fun y hy => (exact y (mem_filter.mp hy).1).le)
    (fun y hy => (mem_filter.mp hy).2.le) (fun v hv => (root v hv).2.2.1)
    (fun v hv => by obtain ⟨vv, one, sh, _⟩ := root v hv; have := floor3 v vv; omega)
    live high
  have cr := class_roots (r := r) (R := bankRows(D, V, r)) free (by omega)
    (fun v hv => (root v hv).1) (fun v hv => exact v (root v hv).1)
  have gs : ∑ v ∈ bankRows(D, V, r), (gap D V 2 2 v).card ≤ gaps(D, V) :=
    sum_le_sum_of_subset (fun v hv => (root v hv).1)
  have part : (highRows(D, V, r)).card + (strictRows(D, V, r)).card
      = (V.filter (fun v => 2 * r < (ball D V v 2).card)).card := by
    rw [← card_union_of_disjoint, ← filter_or]
    · refine congrArg card (filter_congr (fun v _ => ?_))
      constructor <;> intro h <;> omega
    · exact disjoint_filter.mpr (fun v _ e lt => by omega)
  exact ⟨((bankRows(D, V, r)).image (fun v => ball D V v 2 \ ball D V v 1)).card,
    by omega, by omega⟩

/-- **Strict count.** One inequality in the order, the cutoff, the degree, the third-ball floor,
the number of strict rows, their excess and the gaps. -/
theorem strict_count {r b : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (exact : ∀ v ∈ V, (outN D V v).card = r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, b ≤ (ball D V v 3).card) (hb : 3 * r ≤ b + 1)
    (regular : ∀ v ∈ bankRows(D, V, r),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card) :
    (q + 1) * (2 * (V.card + (strictRows(D, V, r)).card + excess(D, V, r))
          + 2 * ((strictRows(D, V, r)).card * b) + V.card * (2 * r + 2 * r))
      + (V.card * (2 * r + 2 * r) + gaps(D, V)
          + 4 * (strictRows(D, V, r)).card + 2 * excess(D, V, r))
    ≤ (q + 1) * (V.card * (V.card + 1) + 2 * ((strictRows(D, V, r)).card * V.card))
      + V.card * (V.card + 1) := by
  obtain ⟨c, X, Y⟩ := strict_core free hq exact floor2 floor3 hb regular
  exact combine_classes X Y

/-- **Below the diagonal.** At order `4r − 1` the two floors and the first-layer hypothesis are
contradictory, for every degree and every cutoff from four on. -/
theorem below_diagonal {r : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hr : 1 ≤ r)
    (size : V.card + 1 = 4 * r) (exact : ∀ v ∈ V, (outN D V v).card = r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, 3 * r - 1 ≤ (ball D V v 3).card)
    (regular : ∀ v ∈ bankRows(D, V, r),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card) :
    False := by
  obtain ⟨c, X, Y⟩ := strict_core (b := 3 * r - 1) free hq exact floor2 floor3 (by omega) regular
  have five := Nat.mul_le_mul_right c (show 5 ≤ q + 1 by omega)
  have sq : V.card * (V.card + 1) = V.card * (2 * r + 2 * r) := by
    rw [show V.card + 1 = 2 * r + 2 * r by omega]
  have hs : (strictRows(D, V, r)).card = 0 := by omega
  rw [hs] at X
  omega

/-- **Two strict rows on the diagonal.** At order `4r`, for every degree `r ≥ 1` and every cutoff
`q ≥ 4`, at least two rows are strict. -/
theorem two_strict_diagonal {r : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hr : 1 ≤ r)
    (size : V.card = 4 * r) (exact : ∀ v ∈ V, (outN D V v).card = r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, 3 * r - 1 ≤ (ball D V v 3).card)
    (regular : ∀ v ∈ bankRows(D, V, r),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card) :
    2 ≤ (strictRows(D, V, r)).card := by
  obtain ⟨c, X, Y⟩ := strict_core (b := 3 * r - 1) free hq exact floor2 floor3 (by omega) regular
  have five := Nat.mul_le_mul_right c (show 5 ≤ q + 1 by omega)
  have e : 2 * r + 2 * r = V.card := by omega
  have sq : V.card * (V.card + 1) = V.card * (2 * r + 2 * r) + V.card := by
    rw [e, Nat.mul_add, Nat.mul_one]
  by_contra few
  have hs : (strictRows(D, V, r)).card = 0 ∨ (strictRows(D, V, r)).card = 1 := by omega
  rcases hs with hs | hs <;> rw [hs] at X Y <;> omega

#print axioms strict_core
#print axioms strict_count
#print axioms below_diagonal
#print axioms two_strict_diagonal
end LeanCH.BR.StrictCount
