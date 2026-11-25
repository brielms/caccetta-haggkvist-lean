import checkpoints.shen_extension.BankCount
import checkpoints.shen_extension.TubeAtCutoff

/-!
# The second collar: tight roots one layer deeper

Every out-degree is exactly `q + 2`, and there is no closed walk of length at most `q`. For a root
`u` write `X` for its heads (`q + 2` labels), `Y` for its second layer and `Z` for its third. Call
`u` *tight* (`Tight`) when `|Y| = q + 1` and `|Z| ≤ q + 1`. This is `CollarLedger` one layer
deeper: there the loop was `X` on the row `r = q + 1`; here it is `Y` on the row `r = q + 2`.

Paper source: degree-nine dossier, Appendix 27 bullets 2, 3, 6 and Appendix 17 (`r = 9`, `q = 7`).
Everything below is generic in `q`; the smallest `q` is stated with each result.

* `few_two` (generic, `2 ≤ q`): on at most `q + 2` labels with minimum out-degree one, at most
  half the rows have two heads. A row with two heads has its `(q-1)`-ball of at least `q + 1`
  labels (`ball_grow_two`), so at most one parent; every row has at most two; and the in-degrees
  sum to the out-degrees.
* `complete_near` (`3 ≤ q`): so every row reaches, within `q - 2` steps, a row with one head:
  otherwise its `(q-2)`-ball, of at least `q` labels, consists of rows with two heads.
* **Target 1** `no_return` (`3 ≤ q`, only `|Y| = q + 1` needed): no label of `Y` points to `X` or
  to `u`. A row of `X` with one head in `X` heads all of `Y` (`x_complete`); every row of `X`
  reaches one within `q - 2`; an arc `Y → X` then closes a walk of length at most `q`. This
  replaces the dossier's case analysis of the shape of `X` (Hamiltonian cycle with at most two
  chords, or a chordless `(q+1)`-cycle and an extra label).
* **Target 2** `loop_complete` (`3 ≤ q`): rows of `Y` stay in `Y ∪ Z` (`y_keep`), so `Y` is a loop
  (one head each in `Y`), `|Z| = q + 1`, and every row of `Y` heads all of `Z`.
* **Target 3** `loop_inherit`, `loop_ball` (`3 ≤ q`): `B(j+2) u ⊆ {u} ∪ X ∪ Y ∪ B j y`, hence
  `|B (j+2) u| + j ≤ |B j y| + 2q + 3` for `y ∈ Y`, `j ≤ q`.
* **Target 4** `loops_equal` (`3 ≤ q`): tight roots whose second layers meet have equal ones.
* **Target 5** `same_far`, `twins_gap` (`2 ≤ q`, no tightness needed): two distinct roots with
  the same second layer are not within `q` of each other, so they are gaps at all radii
  `i, j ≤ q`. (The dossier has "within four" at `q = 7`.)
* **Target 6** `no_tight` (`3 ≤ q`): the count through `BankCount.bank_count_disjoint`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarTwo
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)

variable {D : CH.Digraph} {q : ℕ}

/-! ### Rows with two heads in a small set -/

/-- A row with two heads: its balls grow from three labels, until they hold more than `q`. -/
theorem ball_grow_two {S : Finset ℕ} {x : ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) (hx : x ∈ S) (two : 2 ≤ (outN D S x).card) :
    ∀ j, 1 ≤ j → j + 1 ≤ q → j + 2 ≤ (ball D S x j).card := by
  intro j hj1 hjq
  have b1 : (ball D S x 1).card = (outN D S x).card + 1 := ReachLedger.ball_one free hq hx
  rcases TubeAtCutoff.closed_or_grow (D := D) (S := S) (v := x) (a := 1) (M := j - 1) with
    ⟨k, hk1, hkj, cl⟩ | g
  · have next : ∀ a ∈ ball D S x k, ∃ w ∈ ball D S x k, D a w = true := by
      intro a ha
      obtain ⟨w, hw⟩ := card_pos.mp
        (show 0 < (outN D S a).card by have := deg a (ball_subset ha); omega)
      obtain ⟨wS, aw⟩ := mem_outN.mp hw
      exact ⟨w, cl a ha w wS aw, aw⟩
    have big := ReachLedger.closed_chain (V := S) (S := ball D S x k) free ball_subset
      ⟨x, self_mem_ball hx⟩ next
    have := card_le_card (ball_mono_radius (D := D) (W := S) (u := x) (show k ≤ j by omega))
    omega
  · have e : 1 + (j - 1) = j := by omega
    rw [e] at g
    omega

/-- **Few rows with two heads.** On at most `q + 2` labels, `q`-free, minimum out-degree one:
at most half the rows have two heads. -/
theorem few_two {S : Finset ℕ} (free : QFree D S q) (hq : 2 ≤ q)
    (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) (size : S.card ≤ q + 2) :
    2 * (S.filter (fun v => 2 ≤ (outN D S v).card)).card ≤ S.card := by
  rw [card_filter]
  have up : ∀ v ∈ S, 2 + (if 2 ≤ (outN D S v).card then 1 else 0) ≤ (ball D S v 1).card := by
    intro v hv
    rw [ReachLedger.ball_one free (by omega) hv]
    have := deg v hv
    split_ifs <;> omega
  have down : ∀ v ∈ S,
      (reverseBall D S v 1).card + (if 2 ≤ (outN D S v).card then 1 else 0) ≤ 3 := by
    intro v hv
    have rb := reverseBall_add_ball_le (D := D) (W := S) (v := v) (i := q - 1) (j := 1) free
      (by omega)
    split_ifs with h
    · have := ball_grow_two free (by omega) deg hv h (q - 1) (by omega) (by omega)
      omega
    · have := ball_grow free deg hv (q - 1) (by omega)
      omega
  have s1 := sum_le_sum up
  have s2 := sum_le_sum down
  rw [sum_add_distrib, sum_const, smul_eq_mul] at s1 s2
  have e := sum_reverseBall_eq_sum_ball D S 1
  omega

/-- **A row with one head nearby.** On at most `q + 2` labels, `q`-free, minimum out-degree one,
`3 ≤ q`: every row reaches a row with a single head within `q - 2` steps. -/
theorem complete_near {S : Finset ℕ} (free : QFree D S q) (hq : 3 ≤ q)
    (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) (size : S.card ≤ q + 2) {x : ℕ} (hx : x ∈ S) :
    ∃ c ∈ ball D S x (q - 2), (outN D S c).card ≤ 1 := by
  by_contra none
  push Not at none
  have few := few_two free (by omega) deg size
  have xT : 2 ≤ (outN D S x).card := by have := none x (self_mem_ball hx); omega
  have big := ball_grow_two free (by omega) deg hx xT (q - 2) (by omega) (by omega)
  have sub : ball D S x (q - 2) ⊆ S.filter (fun v => 2 ≤ (outN D S v).card) :=
    fun c hc => mem_filter.mpr ⟨ball_subset hc, by have := none c hc; omega⟩
  have := card_le_card sub
  omega

/-! ### The root -/

/-- Widths `q + 1` and at most `q + 1` in the second and third layers. -/
def Tight (D : CH.Digraph) (V : Finset ℕ) (q u : ℕ) : Prop :=
  (layer D V 2 u).card = q + 1 ∧ (layer D V 3 u).card ≤ q + 1

section root
variable {V : Finset ℕ} {u : ℕ}

/-- Every row of `X` has a head in `X`. -/
theorem x_heads (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (wide : (layer D V 2 u).card = q + 1) :
    ∀ x ∈ outN D V u, 1 ≤ (outN D (outN D V u) x).card :=
  DipCost.layer_host (fun x hx => (reg x (outN_subset hx)).ge) (head_keep free hq hu)
    (by omega)

/-- A row of `X` with one head in `X` heads all of `Y`. -/
theorem x_complete (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (wide : (layer D V 2 u).card = q + 1) {x : ℕ} (hx : x ∈ outN D V u)
    (one : (outN D (outN D V u) x).card ≤ 1) : layer D V 2 u ⊆ outN D V x := by
  classical
  have keep := head_keep free hq hu
  have cover : outN D V x ⊆ outN D (outN D V u) x ∪ (layer D V 2 u ∩ outN D V x) := by
    intro w hw
    rcases mem_union.mp (keep x hx hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
  have c := (card_le_card cover).trans (card_union_le _ _)
  rw [reg x (outN_subset hx)] at c
  have full : layer D V 2 u ∩ outN D V x = layer D V 2 u :=
    eq_of_subset_of_card_le inter_subset_left (by omega)
  intro w hw
  rw [← full] at hw
  exact (mem_inter.mp hw).2

/-- **Target 1: no arcs back from `Y`.** If the second layer has `q + 1` labels, `3 ≤ q`, no
label of it points to the root or to a head of the root. -/
theorem no_return (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (wide : (layer D V 2 u).card = q + 1) {y : ℕ} (hy : y ∈ layer D V 2 u)
    {w : ℕ} (hw : w ∈ insert u (outN D V u)) : ¬ D y w = true := by
  intro yw
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have yV : y ∈ V := ball_subset yb
  rcases mem_insert.mp hw with rfl | wX
  · exact no_back_arc free hu yb (by omega) yw
  · have XV : outN D V u ⊆ V := outN_subset
    obtain ⟨c, cb, one⟩ := complete_near (free.mono_set XV) hq
      (x_heads free (by omega) reg hu wide) (reg u hu).le wX
    have cX : c ∈ outN D V u := ball_subset cb
    have cy : D c y = true :=
      (mem_outN.mp (x_complete free (by omega) reg hu wide cX one hy)).2
    obtain ⟨-, k, hk, walk⟩ := mem_ball.mp cb
    exact free w (k + 1 + 1) (by omega) (by omega)
      (((walk.mono XV).snoc yV cy).snoc (XV wX) yw)

/-- Rows of `Y` stay in `Y ∪ Z`. -/
theorem y_keep (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (wide : (layer D V 2 u).card = q + 1) :
    ∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u := by
  intro y hy w hw
  obtain ⟨wV, yw⟩ := mem_outN.mp hw
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have wb : w ∈ ball D V u 3 := ball_step yb wV yw
  have n1 : w ∉ ball D V u 1 := by
    intro h
    rcases (mem_ball_one hu).mp h with e | h
    · exact no_return free hq reg hu wide hy (e ▸ mem_insert_self u (outN D V u)) yw
    · exact no_return free hq reg hu wide hy (mem_insert_of_mem h) yw
  by_cases n2 : w ∈ ball D V u 2
  · exact mem_union_left _ (mem_layer.mpr ⟨n2, n1⟩)
  · exact mem_union_right _ (mem_layer.mpr ⟨wb, n2⟩)

/-- **Target 2: `Y` is a loop complete to `Z`.** At a tight root, `3 ≤ q`: every row of `Y` has
exactly one head in `Y`, the third layer has exactly `q + 1` labels, and every row of `Y` heads
all of it. -/
theorem loop_complete (free : QFree D V q) (hq : 3 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2) (hu : u ∈ V) (tight : Tight D V q u) :
    (∀ y ∈ layer D V 2 u, (outN D (layer D V 2 u) y).card = 1) ∧
      (layer D V 3 u).card = q + 1 ∧ ∀ y ∈ layer D V 2 u, layer D V 3 u ⊆ outN D V y := by
  classical
  obtain ⟨wide, third⟩ := tight
  have keep := y_keep free hq reg hu wide
  have inner := DipCost.layer_host (X := layer D V 2 u) (Y := layer D V 3 u) (c := 1)
    (fun y hy => (reg y (layer_subset hy)).ge) keep (by omega)
  have one := loop_unique_head (free.mono_set layer_subset) (by omega) wide inner
  have count : ∀ y ∈ layer D V 2 u,
      q + 2 ≤ 1 + (layer D V 3 u ∩ outN D V y).card := by
    intro y hy
    have cover : outN D V y ⊆ outN D (layer D V 2 u) y ∪ (layer D V 3 u ∩ outN D V y) := by
      intro w hw
      rcases mem_union.mp (keep y hy hw) with h | h
      · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [one y hy, reg y (layer_subset hy)] at c
    exact c
  obtain ⟨y0, hy0⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
  have le0 := card_le_card (inter_subset_left : layer D V 3 u ∩ outN D V y0 ⊆ layer D V 3 u)
  have width : (layer D V 3 u).card = q + 1 := by
    have := count y0 hy0
    omega
  refine ⟨one, width, fun y hy => ?_⟩
  have full : layer D V 3 u ∩ outN D V y = layer D V 3 u :=
    eq_of_subset_of_card_le inter_subset_left (by have := count y hy; omega)
  intro w hw
  rw [← full] at hw
  exact (mem_inter.mp hw).2

/-- **Target 3: inheritance.** Under the second collar, everything within `j + 2` of the root is
the root, a head, a label of `Y`, or within `j` of the given label `y` of `Y`. -/
theorem loop_inherit (hu : u ∈ V)
    (xkeep : ∀ x ∈ outN D V u, outN D V x ⊆ outN D V u ∪ layer D V 2 u)
    (ykeep : ∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u)
    {y : ℕ} (hy : y ∈ layer D V 2 u) (full : layer D V 3 u ⊆ outN D V y) :
    ∀ j, ball D V u (j + 2) ⊆ (insert u (outN D V u) ∪ layer D V 2 u) ∪ ball D V y j := by
  classical
  have yV : y ∈ V := layer_subset hy
  intro j
  induction j with
  | zero =>
    intro w hw
    refine mem_union_left _ ?_
    by_cases h1 : w ∈ ball D V u 1
    · rcases (mem_ball_one hu).mp h1 with rfl | h
      · exact mem_union_left _ (mem_insert_self _ _)
      · exact mem_union_left _ (mem_insert_of_mem h)
    · exact mem_union_right _ (mem_layer.mpr ⟨hw, h1⟩)
  | succ j ih =>
    intro w hw
    have up : ball D V y j ⊆ ball D V y (j + 1) := ball_mono_radius (Nat.le_succ j)
    have hw' : w ∈ ball D V u ((j + 2) + 1) := by
      rwa [show j + 2 + 1 = j + 1 + 2 by omega]
    by_cases old : w ∈ ball D V u (j + 2)
    · rcases mem_union.mp (ih old) with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (up h)
    · obtain ⟨p, pb, pw⟩ := ball_succ_pred hu hw' old
      have wV : w ∈ V := ball_subset hw
      rcases mem_union.mp (ih pb) with h | h
      · rcases mem_union.mp h with h | pY
        · rcases mem_insert.mp h with rfl | pX
          · exact mem_union_left _ (mem_union_left _
              (mem_insert_of_mem (mem_outN.mpr ⟨wV, pw⟩)))
          · rcases mem_union.mp (xkeep p pX (mem_outN.mpr ⟨wV, pw⟩)) with a | a
            · exact mem_union_left _ (mem_union_left _ (mem_insert_of_mem a))
            · exact mem_union_left _ (mem_union_right _ a)
        · rcases mem_union.mp (ykeep p pY (mem_outN.mpr ⟨wV, pw⟩)) with a | a
          · exact mem_union_left _ (mem_union_right _ a)
          · have yw := (mem_outN.mp (full a)).2
            exact mem_union_right _ (ball_mono_radius (by omega : 1 ≤ j + 1)
              ((mem_ball_one yV).mpr (Or.inr (mem_outN.mpr ⟨wV, yw⟩))))
      · exact mem_union_right _ (ball_step h wV pw)

/-- **Target 3: the loop rows are fat.** At a tight root, `3 ≤ q`, for each `y ∈ Y` and
`j ≤ q`: `|B (j+2) u| + j ≤ |B j y| + 2q + 3`. (The root, `q + 2` heads, `q + 1` labels of `Y`,
less the `j + 1` labels of `Y` that `y` reaches round the loop.) -/
theorem loop_ball (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (tight : Tight D V q u) {y : ℕ} (hy : y ∈ layer D V 2 u) {j : ℕ}
    (hj : j ≤ q) : (ball D V u (j + 2)).card + j ≤ (ball D V y j).card + 2 * q + 3 := by
  classical
  obtain ⟨one, -, all⟩ := loop_complete free hq reg hu tight
  have wide := tight.1
  have inh := loop_inherit hu (head_keep free (by omega) hu) (y_keep free hq reg hu wide) hy
    (all y hy) j
  have YV : layer D V 2 u ⊆ V := layer_subset
  have loopBall : ball D (layer D V 2 u) y j ⊆ ball D V y j ∩ layer D V 2 u := by
    intro w hw
    obtain ⟨wY, i, hi, walk⟩ := mem_ball.mp hw
    exact mem_inter.mpr ⟨mem_ball.mpr ⟨YV wY, i, hi, walk.mono YV⟩, wY⟩
  have grow := ball_grow (free.mono_set YV) (fun v hv => (one v hv).ge) hy j hj
  have inside := card_le_card loopBall
  have split : ball D V u (j + 2) ⊆
      (insert u (outN D V u) ∪ layer D V 2 u) ∪ (ball D V y j \ layer D V 2 u) := by
    intro w hw
    rcases mem_union.mp (inh hw) with h | h
    · exact mem_union_left _ h
    · by_cases wY : w ∈ layer D V 2 u
      · exact mem_union_left _ (mem_union_right _ wY)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨h, wY⟩)
  have c := (card_le_card split).trans (card_union_le _ _)
  have c1 := card_union_le (insert u (outN D V u)) (layer D V 2 u)
  have c2 := card_insert_le u (outN D V u)
  rw [reg u hu] at c2
  have parts := card_sdiff_add_card_inter (ball D V y j) (layer D V 2 u)
  omega

/-- From a root, every label beyond the second layer is reached from a label of the second
layer, two steps sooner. -/
theorem through_second (hu : u ∈ V) :
    ∀ k, ∀ w ∈ ball D V u (k + 2), w ∉ ball D V u 2 → ∃ y ∈ layer D V 2 u, w ∈ ball D V y k := by
  intro k
  induction k with
  | zero => intro w hw out; exact (out hw).elim
  | succ k ih =>
    intro w hw out
    have hw' : w ∈ ball D V u ((k + 2) + 1) := by
      rwa [show k + 2 + 1 = k + 1 + 2 by omega]
    have wV : w ∈ V := ball_subset hw
    by_cases old : w ∈ ball D V u (k + 2)
    · obtain ⟨y, hy, wy⟩ := ih w old out
      exact ⟨y, hy, ball_mono_radius (Nat.le_succ k) wy⟩
    · obtain ⟨p, pb, pw⟩ := ball_succ_pred hu hw' old
      by_cases p2 : p ∈ ball D V u 2
      · by_cases p1 : p ∈ ball D V u 1
        · exact (out (ball_step p1 wV pw)).elim
        · refine ⟨p, mem_layer.mpr ⟨p2, p1⟩, ?_⟩
          exact ball_mono_radius (by omega : 1 ≤ k + 1)
            ((mem_ball_one (ball_subset pb)).mpr (Or.inr (mem_outN.mpr ⟨wV, pw⟩)))
      · obtain ⟨y, hy, py⟩ := ih p pb p2
        exact ⟨y, hy, ball_step py wV pw⟩

/-- **Target 5: same second layer, far apart.** Two distinct roots with the same second layer:
neither is within `q` of the other (`2 ≤ q`; no tightness needed). -/
theorem same_far (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    {u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (ne : u ≠ u')
    (same : layer D V 2 u = layer D V 2 u') : u' ∉ ball D V u q := by
  classical
  intro h
  by_cases n1 : u' ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp n1 with e | h1
    · exact ne e.symm
    · -- a head with the same second layer has the same heads, hence a loop
      have sub : outN D V u' ⊆ outN D V u := by
        intro w hw
        rcases mem_union.mp (head_keep free hq hu u' h1 hw) with a | a
        · exact a
        · rw [same] at a
          exact ((mem_layer.mp a).2 ((mem_ball_one hu').mpr (Or.inr hw))).elim
      have eq : outN D V u' = outN D V u :=
        eq_of_subset_of_card_le sub (by rw [reg u hu, reg u' hu'])
      rw [← eq] at h1
      exact loopfree free (by omega) hu' (mem_outN.mp h1).2
  by_cases n2 : u' ∈ ball D V u 2
  · have : u' ∈ layer D V 2 u' := same ▸ mem_layer.mpr ⟨n2, n1⟩
    exact (mem_layer.mp this).2 (self_mem_ball hu')
  · have h' : u' ∈ ball D V u ((q - 2) + 2) := by rwa [show q - 2 + 2 = q by omega]
    obtain ⟨y, hy, back⟩ := through_second hu (q - 2) u' h' n2
    rw [same] at hy
    obtain ⟨yb, ny⟩ := mem_layer.mp hy
    obtain ⟨-, a, ha, wa⟩ := mem_ball.mp back
    obtain ⟨-, b, hb, wb⟩ := mem_ball.mp yb
    rcases Nat.eq_zero_or_pos b with rfl | bpos
    · exact (ny (FlatAtCutoff.walk_zero wb ▸ self_mem_ball hu')).elim
    · exact free y (a + b) (by omega) (by omega) (wa.append wb)

/-- **Target 5, ledger form.** Two distinct roots with the same second layer are gaps of each
other at all radii `i, j ≤ q`. -/
theorem twins_gap (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    {u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (ne : u ≠ u')
    (same : layer D V 2 u = layer D V 2 u') {i j : ℕ} (hi : i ≤ q) (hj : j ≤ q) :
    u' ∈ gap D V i j u :=
  mem_gap.mpr ⟨hu', fun h => same_far free hq reg hu hu' ne same (ball_mono_radius hi h),
    fun h => same_far free hq reg hu' hu (Ne.symm ne) same.symm (ball_mono_radius hj h)⟩

end root

/-- **Target 4: loops are equal or disjoint.** Two tight roots whose second layers share a label
have the same second layer (`3 ≤ q`). -/
theorem loops_equal {V : Finset ℕ} (free : QFree D V q) (hq : 3 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (tight : Tight D V q u) (tight' : Tight D V q u')
    {x : ℕ} (hx : x ∈ layer D V 2 u) (hx' : x ∈ layer D V 2 u') :
    layer D V 2 u = layer D V 2 u' := by
  classical
  obtain ⟨one, -, all⟩ := loop_complete free hq reg hu tight
  obtain ⟨one', -, all'⟩ := loop_complete free hq reg hu' tight'
  have keep := y_keep free hq reg hu tight.1
  have keep' := y_keep free hq reg hu' tight'.1
  -- a common row hands its loop successor over
  have step : ∀ a ∈ layer D V 2 u, a ∈ layer D V 2 u' → ∀ b ∈ layer D V 2 u, D a b = true →
      b ∈ layer D V 2 u' := by
    intro a ha ha' b hb ab
    by_contra off
    have bV := layer_subset hb
    have bZ' : b ∈ layer D V 3 u' :=
      (mem_union.mp (keep' a ha' (mem_outN.mpr ⟨bV, ab⟩))).resolve_left off
    obtain ⟨s, hs⟩ := card_pos.mp
      (by rw [one' a ha']; exact Nat.one_pos : 0 < (outN D (layer D V 2 u') a).card)
    obtain ⟨sY', as⟩ := mem_outN.mp hs
    have sV := layer_subset sY'
    have sne : s ≠ b := fun e => off (e ▸ sY')
    have sY : s ∉ layer D V 2 u := by
      intro h
      have both : ({s, b} : Finset ℕ) ⊆ outN D (layer D V 2 u) a := by
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact mem_outN.mpr ⟨h, as⟩
        · rw [mem_singleton.mp hz]
          exact mem_outN.mpr ⟨hb, ab⟩
      have := card_le_card both
      rw [one a ha, card_pair sne] at this
      omega
    have sZ : s ∈ layer D V 3 u :=
      (mem_union.mp (keep a ha (mem_outN.mpr ⟨sV, as⟩))).resolve_left sY
    have bs := (mem_outN.mp ((all b hb) sZ)).2
    have sb := (mem_outN.mp ((all' s sY') bZ')).2
    exact digonfree free (by omega) bV sV bs sb
  -- every label of the loop is reached from `x` inside the loop
  have reach : ball D (layer D V 2 u) x q = layer D V 2 u := by
    refine eq_of_subset_of_card_le ball_subset ?_
    have := ball_grow (free.mono_set (layer_subset (D := D) (V := V) (R := 2) (u := u)))
      (fun v hv => (one v hv).ge) hx q le_rfl
    rw [tight.1]
    exact this
  have walk : ∀ k a y, a ∈ layer D V 2 u → a ∈ layer D V 2 u' →
      Walk D (layer D V 2 u) a y k → y ∈ layer D V 2 u' := by
    intro k
    induction k with
    | zero =>
      intro a y _ ha' w
      cases w
      exact ha'
    | succ k ih =>
      intro a y ha ha' w
      cases w with
      | step bY ab rest => exact ih _ y bY (step a ha ha' _ bY ab) rest
  have sub : layer D V 2 u ⊆ layer D V 2 u' := by
    intro y hy
    rw [← reach] at hy
    obtain ⟨-, k, -, w⟩ := mem_ball.mp hy
    exact walk k x y hx hx' w
  exact eq_of_subset_of_card_le sub (by rw [tight.1, tight'.1])

/-- **Target 6: tight roots are outvoted.** Floors `a`, `b` at radii `i`, `j` and `a'`, `b'` at
radii `i + 2`, `j + 2` for tight rows; `A + B` for the two balls of a row that is not tight
together. If loose rows reach the level `|V| + 1`, the loop rows of a tight root exceed it by `π`
(through `loop_ball`), tight rows fall short by at most `δ`, and `m (δ + 1) < m² + (q + 1) π`
for every `m`, then no root is tight. Proved through `BankCount.bank_count_disjoint`: savers
are the tight roots, the class of a tight root is the largest tight root with the same second
layer, and the bank of a class is that second layer (`q + 1` rows). -/
theorem no_tight {V : Finset ℕ} {i j a b A B a' b' π δ : ℕ} (free : QFree D V q) (hq : 3 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2) (hij : i + j ≤ q)
    (fa : ∀ v ∈ V, Tight D V q v → a ≤ (ball D V v i).card)
    (fb : ∀ v ∈ V, Tight D V q v → b ≤ (ball D V v j).card)
    (fa' : ∀ v ∈ V, Tight D V q v → a' ≤ (ball D V v (i + 2)).card)
    (fb' : ∀ v ∈ V, Tight D V q v → b' ≤ (ball D V v (j + 2)).card)
    (loose : ∀ v ∈ V, ¬ Tight D V q v → A + B ≤ (ball D V v i).card + (ball D V v j).card)
    (loosepay : V.card + 1 ≤ A + B)
    (bankrow : V.card + 1 + π + 2 * (2 * q + 3) ≤ a' + b' + i + j)
    (tightpay : V.card + 1 ≤ a + b + δ)
    (pay : ∀ m, m * (δ + 1) < m * m + (q + 1) * π) :
    ∀ v ∈ V, ¬ Tight D V q v := by
  classical
  set S := V.filter (fun v => Tight D V q v) with hS
  set cls : ℕ → ℕ := fun u => (S.filter (fun w => layer D V 2 w = layer D V 2 u)).sup id
    with hcls
  have rep : ∀ u ∈ S, cls u ∈ S ∧ layer D V 2 (cls u) = layer D V 2 u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (S.filter (fun w => layer D V 2 w = layer D V 2 u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : cls u = w := he
    rw [this]
    exact mem_filter.mp hw
  have cong : ∀ u u', layer D V 2 u = layer D V 2 u' → cls u = cls u' := by
    intro u u' h
    simp only [hcls, h]
  have sv : S ⊆ V := filter_subset _ _
  have tightOf : ∀ u ∈ S, u ∈ V ∧ Tight D V q u := fun u hu => mem_filter.mp hu
  have empty : S = ∅ := by
    refine BankCount.bank_count_disjoint (b := q + 1) (bank := fun c => layer D V 2 c)
      (π := π) (δ := δ) free hij sv
      (fun u _ => layer_subset)
      (fun u hu => (tightOf _ (rep u hu).1).2.1.ge)
      (fun u hu => ?_) (fun v hv vS => ?_) (fun u hu x hx => ?_)
      (fun u hu u' hu' hc ne => ?_) (fun u hu u' hu' ne => ?_) pay
    · obtain ⟨uV, ut⟩ := tightOf u hu
      have := fa u uV ut
      have := fb u uV ut
      omega
    · have vt : ¬ Tight D V q v := fun h => vS (mem_filter.mpr ⟨hv, h⟩)
      have := loose v hv vt
      omega
    · obtain ⟨wS, -⟩ := rep u hu
      obtain ⟨wV, wt⟩ := tightOf _ wS
      have bi := loop_ball free hq reg wV wt hx (j := i) (by omega)
      have bj := loop_ball free hq reg wV wt hx (j := j) (by omega)
      have := fa' _ wV wt
      have := fb' _ wV wt
      omega
    · have same : layer D V 2 u = layer D V 2 u' := by
        rw [← (rep u hu).2, ← (rep u' hu').2, hc]
      exact twins_gap free (by omega) reg (sv hu) (sv hu') (Ne.symm ne) same
        (by omega) (by omega)
    · rw [disjoint_left]
      intro x hx hx'
      obtain ⟨wS, we⟩ := rep u hu
      obtain ⟨wS', we'⟩ := rep u' hu'
      obtain ⟨wV, wt⟩ := tightOf _ wS
      obtain ⟨wV', wt'⟩ := tightOf _ wS'
      have := loops_equal free hq reg wV wV' wt wt' hx hx'
      rw [we, we'] at this
      exact ne (cong u u' this)
  intro v hv h
  have : v ∈ S := mem_filter.mpr ⟨hv, h⟩
  rw [empty] at this
  simp at this

/-! ### Instances at `r = 9`, `q = 7` (inclusive ball floors) -/

/-- **60 vertices.** Floors `26, 34, 41, 48` at radii `3, 4, 5, 6` on tight rows and a joint
floor `61` at radii `3, 4` on the other rows: `π = δ = 1`, and `2m < m² + 8` for every `m`. -/
theorem no_tight_sixty {V : Finset ℕ} (free : QFree D V 7)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 60)
    (f3 : ∀ v ∈ V, Tight D V 7 v → 26 ≤ (ball D V v 3).card)
    (f4 : ∀ v ∈ V, Tight D V 7 v → 34 ≤ (ball D V v 4).card)
    (f5 : ∀ v ∈ V, Tight D V 7 v → 41 ≤ (ball D V v 5).card)
    (f6 : ∀ v ∈ V, Tight D V 7 v → 48 ≤ (ball D V v 6).card)
    (loose : ∀ v ∈ V, ¬ Tight D V 7 v → 61 ≤ (ball D V v 3).card + (ball D V v 4).card) :
    ∀ v ∈ V, ¬ Tight D V 7 v := by
  refine no_tight (i := 3) (j := 4) (A := 61) (B := 0) (π := 1) (δ := 1) free (by norm_num) reg
    (by norm_num) f3 f4 f5 f6 (fun v hv h => by have := loose v hv h; omega) (by omega)
    (by omega) (by omega) (fun m => ?_)
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m <;> omega
  · have := Nat.mul_le_mul_right m h
    omega

/-- **61 vertices.** The same with floor `42` at radius `5` on tight rows and joint floor `62` on
the other rows: `π = 1`, `δ = 2`, and `3m < m² + 8` for every `m`. -/
theorem no_tight_sixtyone {V : Finset ℕ} (free : QFree D V 7)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 61)
    (f3 : ∀ v ∈ V, Tight D V 7 v → 26 ≤ (ball D V v 3).card)
    (f4 : ∀ v ∈ V, Tight D V 7 v → 34 ≤ (ball D V v 4).card)
    (f5 : ∀ v ∈ V, Tight D V 7 v → 42 ≤ (ball D V v 5).card)
    (f6 : ∀ v ∈ V, Tight D V 7 v → 48 ≤ (ball D V v 6).card)
    (loose : ∀ v ∈ V, ¬ Tight D V 7 v → 62 ≤ (ball D V v 3).card + (ball D V v 4).card) :
    ∀ v ∈ V, ¬ Tight D V 7 v := by
  refine no_tight (i := 3) (j := 4) (A := 62) (B := 0) (π := 1) (δ := 2) free (by norm_num) reg
    (by norm_num) f3 f4 f5 f6 (fun v hv h => by have := loose v hv h; omega) (by omega)
    (by omega) (by omega) (fun m => ?_)
  rcases Nat.lt_or_ge m 4 with h | h
  · interval_cases m <;> omega
  · have := Nat.mul_le_mul_right m h
    omega

#print axioms few_two
#print axioms complete_near
#print axioms no_return
#print axioms loop_complete
#print axioms loop_inherit
#print axioms loop_ball
#print axioms loops_equal
#print axioms same_far
#print axioms twins_gap
#print axioms no_tight
#print axioms no_tight_sixty
#print axioms no_tight_sixtyone
end LeanCH.BR.CollarTwo
