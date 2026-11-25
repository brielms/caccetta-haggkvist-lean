import checkpoints.shen_extension.OneHead

/-!
# Suppliers at thin roots, `q = 6`, `r = 9`

`free : QFree D V 6`, every out-degree `9`, a root `u ∈ V`. Layers `X = outN D V u`,
`Y = layer D V 2 u`, `Z = layer D V 3 u`, `W = layer D V 4 u`, `J = layer D V 5 u`.
`ThinSuppliers.Thin D V 9 u` is `|Y| = 8`; `ThinSuppliers.TightR D V 9 u` is `|Y| = 8`,
`|Z| ≤ 8`, i.e. the profile `(w_2, w_3) = (8, 8)` (`third_wide` gives `|Z| ≥ 8`).

Reach and return (generic layers, `q = 6`, `r = 9`):
* `x_reach` (thin root): every head `x` reaches all of layer `2 + t` within `3 + t` steps (A2 on
  `X`, `OneHead.lone_two_six`, then a complete head, `ThinSuppliers.complete_full`).
  `no_back_x`: no arc from layers `2 … 4` into `X`; `no_back_u`: none from layers `≤ 5` to `u`.
* `y_reach` (tight root): every row of `Y` reaches all of layer `3 + t` within `2 + t` steps (A2
  with `k = 1` on `Y`, `ThinSuppliers.y_full`). `no_back_y`: no arc from layers `3 … 6` into `Y`.

Generic in `q`, `r`: `x_reach_y_g`, `no_back_x_g`, `no_back_u_g`, `y_reach_z_g`, `no_back_y_g`,
`good_y_g`, B1 `s5_generic`, the B2/B3 core `layer_ball`, B4 `zRows`, `zRows_count`,
`zRows_exclusive`, `zSet_exclusive`.
Instances (`q = 6`, `r = 9`): B1 `s5_incidence`, B2 `y_ball` / `wj_sixteen` / `complete_y_28`,
B3 `x_ball` / `w_eight` / `complete_x_29`, B4 `zSet`, `zSet_count`. The layer floors
`wj_sixteen` and `w_eight` are fragment-budget arithmetic with the `q = 6` growth table.

Lemma 3 (the growth table) and Lemma P (the pair budget) enter through `Tables D`, whose fields
are exactly the statements of `Profile54.reach_three_two … five`, `Profile54.nine_row` and
`Profile54.budget_floor` (with `Profile54.reach D F 3 x` unfolded to
`((ball D F x 3).erase x).card`). They are discharged in `Supplier54Close.lean` once
`Profile54` has an olean.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Supplier54
open Finset BRq2 BRq3 ThinSuppliers OneHead
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)

variable {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-! ### Generic helpers -/

theorem ball_mono_set {W W' : Finset ℕ} (h : W ⊆ W') {x k : ℕ} :
    ball D W x k ⊆ ball D W' x k := by
  intro v hv
  obtain ⟨vW, j, hj, w⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨h vW, j, hj, w.mono h⟩

theorem layer_disj {i j : ℕ} (h : i < j) : Disjoint (layer D V i u) (layer D V j u) := by
  rw [disjoint_left]
  intro v hi hj
  exact (mem_layer.mp hj).2 (ball_mono_radius (by omega) (mem_layer.mp hi).1)

theorem heads_disj (hu : u ∈ V) {j : ℕ} (hj : 2 ≤ j) : Disjoint (outN D V u) (layer D V j u) := by
  rw [disjoint_left]
  intro v hv hl
  exact (mem_layer.mp hl).2 (ball_mono_radius (by omega) ((mem_ball_one hu).mpr (Or.inr hv)))

/-- If `x` reaches all of layer `j ≥ 1` within `m` steps, it reaches layer `j + t` within
`m + t`. -/
theorem layers_from (hu : u ∈ V) {x j m : ℕ} (hj : 1 ≤ j) (base : layer D V j u ⊆ ball D V x m) :
    ∀ t, layer D V (j + t) u ⊆ ball D V x (m + t) := by
  intro t
  induction t with
  | zero => simpa using base
  | succ t ih =>
    intro v hv
    obtain ⟨p, hp, pv⟩ := ShapeClimbRoot.parent_mem hu (i := j + t) (by omega) hv
    exact ball_step (ih hp) (layer_subset hv) pv

/-- A label within `k + 3` of `u` but not within `k` lies in layer `k + 1`, `k + 2` or `k + 3`. -/
theorem three_layers {k t : ℕ} (h1 : t ∈ ball D V u (k + 3)) (h0 : t ∉ ball D V u k) :
    t ∈ layer D V (k + 1) u ∪ layer D V (k + 2) u ∪ layer D V (k + 3) u := by
  by_cases a : t ∈ ball D V u (k + 1)
  · exact mem_union_left _ (mem_union_left _
      (mem_layer.mpr ⟨a, by rw [show k + 1 - 1 = k by omega]; exact h0⟩))
  by_cases b : t ∈ ball D V u (k + 2)
  · exact mem_union_left _ (mem_union_right _
      (mem_layer.mpr ⟨b, by rw [show k + 2 - 1 = k + 1 by omega]; exact a⟩))
  · exact mem_union_right _ (mem_layer.mpr ⟨h1, by rw [show k + 3 - 1 = k + 2 by omega]; exact b⟩)

/-- Heads outside `F` lie in `E`: then `|outN V v| ≤ |outN F v| + |E|`. -/
theorem keep_count {F E : Finset ℕ} {v : ℕ} (cover : outN D V v ⊆ F ∪ E) :
    (outN D V v).card ≤ (outN D F v).card + E.card := by
  have : outN D V v ⊆ outN D F v ∪ E := by
    intro t ht
    rcases mem_union.mp (cover ht) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp ht).2⟩)
    · exact mem_union_right _ h
  exact (card_le_card this).trans (card_union_le _ _)

theorem out_le {F : Finset ℕ} (FV : F ⊆ V) {v : ℕ} : (outN D F v).card ≤ (outN D V v).card :=
  card_le_card fun t ht => mem_outN.mpr ⟨FV (mem_outN.mp ht).1, (mem_outN.mp ht).2⟩

/-- Four pairwise disjoint sets inside `T`. -/
theorem four_pieces {A B C E T : Finset ℕ} (dAB : Disjoint A B) (dAC : Disjoint A C)
    (dAE : Disjoint A E) (dBC : Disjoint B C) (dBE : Disjoint B E) (dCE : Disjoint C E)
    (hA : A ⊆ T) (hB : B ⊆ T) (hC : C ⊆ T) (hE : E ⊆ T) :
    A.card + B.card + C.card + E.card ≤ T.card := by
  have d1 : Disjoint C E := dCE
  have d2 : Disjoint B (C ∪ E) := disjoint_union_right.mpr ⟨dBC, dBE⟩
  have d3 : Disjoint A (B ∪ (C ∪ E)) :=
    disjoint_union_right.mpr ⟨dAB, disjoint_union_right.mpr ⟨dAC, dAE⟩⟩
  have := card_le_card (union_subset hA (union_subset hB (union_subset hC hE)))
  rw [card_union_of_disjoint d3, card_union_of_disjoint d2, card_union_of_disjoint d1] at this
  omega

/-! ### Generic in `q`, `r`: reach and return at a thin root -/

section generic
variable {q r : ℕ}

/-- Every head of a thin root reaches all of `Y` within three steps (`2 ≤ q`, `r ≤ q + 3`,
`r ≤ 2q`): A2 with `k = 2` on `X`, then a complete head. -/
theorem x_reach_y_g (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r ≤ q + 3) (hr2 : r ≤ 2 * q) {x : ℕ}
    (hx : x ∈ outN D V u) : layer D V 2 u ⊆ ball D V x 3 := by
  obtain ⟨c, cb, cl⟩ := lone_within (free.mono_set outN_subset) (by omega)
    (x_heads_r free hq reg hu thin) (k := 2) hq (by rw [reg u hu]; omega)
    (by rw [reg u hu]; omega) hx
  have full := complete_full free hq reg hu thin (x := c) cl
  intro y hy
  exact ball_step (ball_mono_set outN_subset cb) (layer_subset hy) (mem_outN.mp (full hy)).2

/-- **No return into `X` (generic).** No row of layer `j`, `2 ≤ j`, `j + 2 ≤ q`, points to a head
of a thin root (`r ≤ q + 3`, `r ≤ 2q`). At `q = 6`: layers `2 … 4`. -/
theorem no_back_x_g (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r ≤ q + 3) (hr2 : r ≤ 2 * q) {j : ℕ} (hj2 : 2 ≤ j)
    (hj : j + 2 ≤ q) {v : ℕ} (hv : v ∈ layer D V j u) {x : ℕ} (hx : x ∈ outN D V u) :
    ¬ D v x = true := by
  have := layers_from hu (by norm_num) (x_reach_y_g free hq reg hu thin hr hr2 hx) (j - 2)
  rw [show 2 + (j - 2) = j by omega] at this
  exact no_back_arc free (outN_subset hx) (this hv) (by omega)

/-- No row of layer `j`, `j + 1 ≤ q`, points to the root. -/
theorem no_back_u_g (free : QFree D V q) (hu : u ∈ V) {j : ℕ} (hj : j + 1 ≤ q) {v : ℕ}
    (hv : v ∈ layer D V j u) : ¬ D v u = true :=
  no_back_arc free hu (mem_layer.mp hv).1 hj

/-- At a root with `w_2 = w_3 = r - 1` every row of `Y` reaches all of `Z` within two steps
(`3 ≤ q`, `r ≤ q + 3`, `r + 1 ≤ 2q`): A2 with `k = 1` on `Y`. -/
theorem y_reach_z_g (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r ≤ q + 3) (hr2 : r + 1 ≤ 2 * q) {y : ℕ}
    (hy : y ∈ layer D V 2 u) : layer D V 3 u ⊆ ball D V y 2 := by
  have yc := tight.1
  obtain ⟨c, cb, cl⟩ := lone_within (free.mono_set layer_subset) (by omega)
    (y_heads free hq reg hu tight hr2) (k := 1) (by omega) (by omega) (by omega) hy
  have full := y_full free hq reg hu tight hr2 cl
  intro z hz
  exact ball_step (ball_mono_set layer_subset cb) (layer_subset hz) (mem_outN.mp (full hz)).2

/-- **No return into `Y` (generic).** Same root: no row of layer `j`, `3 ≤ j ≤ q`, points into
`Y`. -/
theorem no_back_y_g (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r ≤ q + 3) (hr2 : r + 1 ≤ 2 * q) {j : ℕ}
    (hj3 : 3 ≤ j) (hj : j ≤ q) {v : ℕ} (hv : v ∈ layer D V j u) {y : ℕ}
    (hy : y ∈ layer D V 2 u) : ¬ D v y = true := by
  have := layers_from hu (by norm_num) (y_reach_z_g free hq reg hu tight hr hr2 hy) (j - 3)
  rw [show 3 + (j - 3) = j by omega] at this
  exact no_back_arc free (layer_subset hy) (this hv) (by omega)

/-- A good row of `Y` points to all of `Z`, its one remaining head is its `Y`-head, which also
points to all of `Z` (`3 ≤ q`, `r + 1 ≤ 2q`, `w_3 = r - 1`). -/
theorem good_y_g (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr2 : r + 1 ≤ 2 * q) {s : ℕ}
    (hs : s ∈ good D (layer D V 2 u)) :
    layer D V 3 u ⊆ outN D V s ∧ outN D V s \ layer D V 3 u = {hd D (layer D V 2 u) s} ∧
      layer D V 3 u ⊆ outN D V (hd D (layer D V 2 u) s) := by
  have deg := y_heads free hq reg hu tight hr2
  have keep := y_keep_r free hq reg hu tight.1 hr2
  obtain ⟨sl, hl⟩ := mem_good.mp hs
  have sY := lone_subset sl
  refine ⟨y_full free hq reg hu tight hr2 sl, ?_, y_full free hq reg hu tight hr2 hl⟩
  ext w
  constructor
  · intro hw
    obtain ⟨hw1, hw2⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (keep s sY hw1) with h | h
    · have : w ∈ outN D (layer D V 2 u) s := mem_outN.mpr ⟨h, (mem_outN.mp hw1).2⟩
      rwa [hd_spec deg sl] at this
    · exact absurd h hw2
  · intro hw
    rw [mem_singleton.mp hw]
    obtain ⟨hY, arc⟩ := hd_mem deg sl
    exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨layer_subset hY, arc⟩,
      fun hz => disjoint_left.mp (layer_disj (D := D) (V := V) (u := u) (by norm_num : 2 < 3)) hY hz⟩

/-- **B1 (generic).** `QFree D V q`, `6 ≤ q`, out-degree `r`, `2 ≤ r ≤ q + 3`, root with
`w_2 = w_3 = r - 1`. (i) No arc from layers `2 … 4` into `X` or to `u`. (ii) No arc from layers
`3, 4` into `Y`; every row of `Y` keeps its heads in `Y ∪ Z` with one in `Y`. (iii) At least
`q - 1` good rows of `Y` (`OneHead.good_count`), each complete to `Z` with complete remaining
head. (`6 ≤ q` is used only for layer `4` in (i): walks `5 + 1 ≤ q`.) -/
theorem s5_generic (free : QFree D V q) (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr1 : 2 ≤ r) (hr : r ≤ q + 3) :
    (∀ j, 2 ≤ j → j ≤ 4 → ∀ v ∈ layer D V j u, ∀ t ∈ insert u (outN D V u), ¬ D v t = true) ∧
    (∀ j, 3 ≤ j → j ≤ 4 → ∀ v ∈ layer D V j u, ∀ t ∈ layer D V 2 u, ¬ D v t = true) ∧
    (∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u ∧
      1 ≤ (outN D (layer D V 2 u) y).card) ∧
    q ≤ (good D (layer D V 2 u)).card + 1 ∧
    (∀ s ∈ good D (layer D V 2 u), layer D V 3 u ⊆ outN D V s ∧
      outN D V s \ layer D V 3 u = {hd D (layer D V 2 u) s} ∧
      layer D V 3 u ⊆ outN D V (hd D (layer D V 2 u) s)) := by
  have thin := tight.1
  have yc := tight.1
  have hr2 : r + 1 ≤ 2 * q := by omega
  have deg := y_heads free (by omega) reg hu tight hr2
  have keep := y_keep_r free (by omega) reg hu thin hr2
  refine ⟨fun j h2 h4 v hv t ht => ?_, fun j h3 h4 v hv t ht => ?_,
    fun y hy => ⟨keep y hy, deg y hy⟩, ?_, fun s hs => good_y_g free (by omega) reg hu tight hr2 hs⟩
  · rcases mem_insert.mp ht with rfl | hx
    · exact no_back_u_g free hu (by omega) hv
    · exact no_back_x_g free (by omega) reg hu thin hr (by omega) h2 (by omega) hv hx
  · exact no_back_y_g free (by omega) reg hu tight hr hr2 h3 (by omega) hv ht
  · obtain ⟨y0, hy0⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
    exact good_count (free.mono_set layer_subset) (by omega) deg ⟨y0, hy0⟩ (by omega)

/-- **B2/B3 core (generic).** `A` is a set of rows within `i ≥ 1` of `u` in which every row keeps
a head, `s ∈ A` points to all of layer `i + 1`. Then for `k ≤ q`:
`|B_k(s)| ≥ (k + 1) + |L_{i+1}| + … + |L_{i+k}|` (itself and `k` further labels of `A`, and the
next `k` layers). Complete heads of a thin root: `A = X`, `i = 1`; complete rows of `Y` at a root
with `w_3 = r - 1`: `A = Y`, `i = 2`. -/
theorem layer_ball (free : QFree D V q) (hu : u ∈ V) {A : Finset ℕ} {i s k : ℕ}
    (hi : 1 ≤ i) (AV : A ⊆ V) (Ab : ∀ v ∈ A, v ∈ ball D V u i) (hs : s ∈ A)
    (deg : ∀ v ∈ A, 1 ≤ (outN D A v).card) (full : layer D V (i + 1) u ⊆ outN D V s)
    (hk : k ≤ q) :
    (k + 1) + ∑ t ∈ range k, (layer D V (i + 1 + t) u).card ≤ (ball D V s k).card := by
  classical
  have sV := AV hs
  have A1 := LoopCollar.ball_grow (free.mono_set AV) deg hs k hk
  have base : layer D V (i + 1) u ⊆ ball D V s 1 :=
    fun z hz => (mem_ball_one sV).mpr (Or.inr (full hz))
  have far : ∀ t ∈ range k, layer D V (i + 1 + t) u ⊆ ball D V s k := by
    intro t ht
    have := layers_from hu (j := i + 1) (m := 1) (by omega) base t
    exact this.trans (ball_mono_radius (by rw [mem_range] at ht; omega))
  have cU : ((range k).biUnion (fun t => layer D V (i + 1 + t) u)).card =
      ∑ t ∈ range k, (layer D V (i + 1 + t) u).card := by
    apply card_biUnion
    intro t _ t' _ ne
    show Disjoint (layer D V (i + 1 + t) u) (layer D V (i + 1 + t') u)
    rcases lt_or_gt_of_ne ne with h | h
    · exact layer_disj (by omega)
    · exact (layer_disj (by omega)).symm
  have dis : Disjoint (ball D A s k) ((range k).biUnion (fun t => layer D V (i + 1 + t) u)) := by
    rw [disjoint_left]
    intro v hv hvU
    obtain ⟨t, -, ht⟩ := mem_biUnion.mp hvU
    exact (mem_layer.mp ht).2 (ball_mono_radius (by omega) (Ab v (ball_subset hv)))
  have sub : ball D A s k ∪ (range k).biUnion (fun t => layer D V (i + 1 + t) u) ⊆
      ball D V s k :=
    union_subset (ball_mono_set AV) (fun v hv => by
      obtain ⟨t, ht, hv'⟩ := mem_biUnion.mp hv
      exact far t ht hv')
  have := card_le_card sub
  rw [card_union_of_disjoint dis, cU] at this
  omega

/-- Rows pointing to all of `Z`, with exactly one other head, which also points to all of `Z`.
Depends only on `D`, `V` and the set `Z`. -/
noncomputable def zRows (D : CH.Digraph) (V Z : Finset ℕ) : Finset ℕ :=
  V.filter (fun s => Z ⊆ outN D V s ∧ (outN D V s \ Z).card = 1 ∧
    ∀ e ∈ outN D V s \ Z, Z ⊆ outN D V e)

/-- **B4 (generic count).** Same root as `s5_generic`: at least `q - 1` rows in
`zRows D V (layer D V 3 u)`. -/
theorem zRows_count (free : QFree D V q) (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr1 : 2 ≤ r) (hr : r ≤ q + 3) :
    q ≤ (zRows D V (layer D V 3 u)).card + 1 := by
  obtain ⟨-, -, -, cnt, each⟩ := s5_generic free hq reg hu tight hr1 hr
  have sub : good D (layer D V 2 u) ⊆ zRows D V (layer D V 3 u) := by
    intro s hs
    obtain ⟨full, rest, full'⟩ := each s hs
    have sY := lone_subset (mem_good.mp hs).1
    refine mem_filter.mpr ⟨layer_subset sY, full, ?_, ?_⟩
    · rw [rest, card_singleton]
    · intro e he
      rw [rest, mem_singleton] at he
      rw [he]
      exact full'
  have := card_le_card sub
  omega

/-- **B4, exclusivity (generic).** A row cannot lie in `zRows` for two different sets of the same
size (`2 ≤ q`). -/
theorem zRows_exclusive (free : QFree D V q) (hq : 2 ≤ q) {Z Z' : Finset ℕ} (ne : Z ≠ Z')
    (hc : Z.card = Z'.card) {s : ℕ} (h : s ∈ zRows D V Z) (h' : s ∈ zRows D V Z') : False := by
  obtain ⟨-, sub, -, all⟩ := mem_filter.mp h
  obtain ⟨-, sub', -, all'⟩ := mem_filter.mp h'
  have out : ∀ {A B : Finset ℕ}, A ≠ B → A.card = B.card → ∃ t ∈ B, t ∉ A := by
    intro A B nAB cAB
    by_contra hall
    push Not at hall
    exact nAB (eq_of_subset_of_card_le hall (by omega)).symm
  obtain ⟨t, t_in, t_out⟩ := out ne hc
  obtain ⟨t', t'_in, t'_out⟩ := out (Ne.symm ne) hc.symm
  have tm : t ∈ outN D V s \ Z := mem_sdiff.mpr ⟨sub' t_in, t_out⟩
  have tm' : t' ∈ outN D V s \ Z' := mem_sdiff.mpr ⟨sub t'_in, t'_out⟩
  have a1 := (mem_outN.mp (all t tm t'_in)).2
  have a2 := (mem_outN.mp (all' t' tm' t_in)).2
  have tV := (mem_outN.mp (mem_sdiff.mp tm).1).1
  have t'V := (mem_outN.mp (mem_sdiff.mp tm').1).1
  exact free t 2 (by omega) hq (.step t'V a1 (.step tV a2 (.refl t)))

end generic

/-! ### Instances at `q = 6`, `r = 9` -/

section root

theorem x_reach_y (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (thin : Thin D V 9 u) {x : ℕ} (hx : x ∈ outN D V u) : layer D V 2 u ⊆ ball D V x 3 :=
  x_reach_y_g free (by norm_num) reg hu thin (by norm_num) (by norm_num) hx

theorem x_reach (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (thin : Thin D V 9 u) {x : ℕ} (hx : x ∈ outN D V u) :
    ∀ t, layer D V (2 + t) u ⊆ ball D V x (3 + t) :=
  layers_from hu (by norm_num) (x_reach_y free reg hu thin hx)

/-- **No return into `X`.** At a thin root no row of layers `2 … 4` points to a head of `u`. -/
theorem no_back_x (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (thin : Thin D V 9 u) {j : ℕ} (hj2 : 2 ≤ j) (hj4 : j ≤ 4) {v : ℕ} (hv : v ∈ layer D V j u)
    {x : ℕ} (hx : x ∈ outN D V u) : ¬ D v x = true :=
  no_back_x_g free (by norm_num) reg hu thin (by norm_num) (by norm_num) hj2 (by omega) hv hx

/-- No row of layers `≤ 5` points to the root. -/
theorem no_back_u (free : QFree D V 6) (hu : u ∈ V) {j : ℕ} (hj : j ≤ 5) {v : ℕ}
    (hv : v ∈ layer D V j u) : ¬ D v u = true :=
  no_back_u_g free hu (by omega) hv

/-- At a tight root every row of `Y` reaches all of `Z` within two steps. -/
theorem y_reach_z (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) {y : ℕ} (hy : y ∈ layer D V 2 u) : layer D V 3 u ⊆ ball D V y 2 :=
  y_reach_z_g free (by norm_num) reg hu tight (by norm_num) (by norm_num) hy

theorem y_reach (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) {y : ℕ} (hy : y ∈ layer D V 2 u) :
    ∀ t, layer D V (3 + t) u ⊆ ball D V y (2 + t) :=
  layers_from hu (by norm_num) (y_reach_z free reg hu tight hy)

/-- **No return into `Y`.** At a tight root no row of layers `3 … 6` points into `Y`. -/
theorem no_back_y (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) {j : ℕ} (hj3 : 3 ≤ j) (hj6 : j ≤ 6) {v : ℕ}
    (hv : v ∈ layer D V j u) {y : ℕ} (hy : y ∈ layer D V 2 u) : ¬ D v y = true :=
  no_back_y_g free (by norm_num) reg hu tight (by norm_num) (by norm_num) hj3 hj6 hv hy

/-- **B1 (S5 incidence)**, instance `q = 6`, `r = 9` of `s5_generic`: root with
`(w_2, w_3) = (8, 8)`, at least five good rows of `Y`. -/
theorem s5_incidence (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) :
    (∀ j, 2 ≤ j → j ≤ 4 → ∀ v ∈ layer D V j u, ∀ t ∈ insert u (outN D V u), ¬ D v t = true) ∧
    (∀ j, 3 ≤ j → j ≤ 4 → ∀ v ∈ layer D V j u, ∀ t ∈ layer D V 2 u, ¬ D v t = true) ∧
    (∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u ∧
      1 ≤ (outN D (layer D V 2 u) y).card) ∧
    5 ≤ (good D (layer D V 2 u)).card ∧
    (∀ s ∈ good D (layer D V 2 u), layer D V 3 u ⊆ outN D V s ∧
      outN D V s \ layer D V 3 u = {hd D (layer D V 2 u) s} ∧
      layer D V 3 u ⊆ outN D V (hd D (layer D V 2 u) s)) := by
  obtain ⟨a, b, c, d, e⟩ := s5_generic free le_rfl reg hu tight (by norm_num) (by norm_num)
  exact ⟨a, b, c, by omega, e⟩

/-! ### Ball sizes of suppliers (instances of `layer_ball`) -/

/-- **B2, ball part.** At a tight root a row `s` of `Y` pointing to all of `Z` has
`|B_3(s)| ≥ 4 + |Z| + |W| + |J|` (`layer_ball`, `A = Y`, `i = 2`, `k = 3`). -/
theorem y_ball (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (tight : TightR D V 9 u) {s : ℕ} (hs : s ∈ layer D V 2 u) (full : layer D V 3 u ⊆ outN D V s) :
    4 + (layer D V 3 u).card + (layer D V 4 u).card + (layer D V 5 u).card ≤
      (ball D V s 3).card := by
  have h := layer_ball free hu (A := layer D V 2 u) (i := 2) (k := 3) (by norm_num) layer_subset
    (fun v hv => (mem_layer.mp hv).1) hs (y_heads free (by norm_num) reg hu tight (by norm_num))
    full (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.reduceAdd, zero_add] at h
  omega

/-- **B3, ball part.** At a thin root a complete head `x` has
`|B_3(x)| ≥ 4 + |Y| + |Z| + |W|` (`layer_ball`, `A = X`, `i = 1`, `k = 3`). -/
theorem x_ball (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (thin : Thin D V 9 u) {x : ℕ} (hx : x ∈ complete D V u) :
    4 + (layer D V 2 u).card + (layer D V 3 u).card + (layer D V 4 u).card ≤
      (ball D V x 3).card := by
  have h := layer_ball free hu (A := outN D V u) (i := 1) (k := 3) le_rfl outN_subset
    (fun v hv => (mem_ball_one hu).mpr (Or.inr hv)) (complete_subset hx)
    (x_heads_r free (by norm_num) reg hu thin) (complete_full free (by norm_num) reg hu thin hx)
    (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.reduceAdd, zero_add] at h
  omega

end root

/-! ### Lemma 3 and Lemma P as hypotheses -/

/-- The growth table (Lemma 3) and the pair budget (Lemma P) at `q = 6`, in the shape of
`Profile54.reach_three_two … five`, `Profile54.nine_row`, `Profile54.budget_floor`. -/
structure Tables (D : CH.Digraph) : Prop where
  t2 : ∀ F : Finset ℕ, QFree D F 6 → (∀ v ∈ F, 2 ≤ (outN D F v).card) →
    ∀ x ∈ F, 6 ≤ ((ball D F x 3).erase x).card
  t3 : ∀ F : Finset ℕ, QFree D F 6 → (∀ v ∈ F, 3 ≤ (outN D F v).card) →
    ∀ x ∈ F, 9 ≤ ((ball D F x 3).erase x).card
  t4 : ∀ F : Finset ℕ, QFree D F 6 → (∀ v ∈ F, 4 ≤ (outN D F v).card) →
    ∀ x ∈ F, 11 ≤ ((ball D F x 3).erase x).card
  t5 : ∀ F : Finset ℕ, QFree D F 6 → (∀ v ∈ F, 5 ≤ (outN D F v).card) →
    ∀ x ∈ F, 13 ≤ ((ball D F x 3).erase x).card
  nine : ∀ F : Finset ℕ, QFree D F 6 → (∀ v ∈ F, 2 ≤ (outN D F v).card) →
    ∀ x ∈ F, (outN D F x).card = 9 → 12 ≤ ((ball D F x 3).erase x).card
  budget : ∀ F : Finset ℕ, QFree D F 6 → ∀ X : Finset ℕ, X ⊆ F → ∀ a b : ℕ,
    (∀ x ∈ X, a ≤ ((ball D F x 3).erase x).card) →
    (∀ v ∈ F \ X, b ≤ ((ball D F v 3).erase v).card) →
    2 * (X.card * a + (F \ X).card * b) ≤ F.card * (F.card - 1)

/-- A fragment `F` of two disjoint parts `X ∪ R`: rows of `X` keep nine heads in `F`, rows of
`R` keep at least `d ≥ 2`. Then the budget fails in the cases used below. -/
theorem fragment_budget (T : Tables D) {X R : Finset ℕ} (dis : Disjoint X R)
    (fr : QFree D (X ∪ R) 6) (nineX : ∀ x ∈ X, (outN D (X ∪ R) x).card = 9) {d : ℕ}
    (hd : 2 ≤ d) (hd9 : d ≤ 9) (degR : ∀ v ∈ R, d ≤ (outN D (X ∪ R) v).card) :
    (d = 2 → 2 * (X.card * 12 + R.card * 6) ≤ (X.card + R.card) * (X.card + R.card - 1)) ∧
    (d = 3 → 2 * (X.card * 12 + R.card * 9) ≤ (X.card + R.card) * (X.card + R.card - 1)) ∧
    (d = 4 → 2 * (X.card * 11 + R.card * 11) ≤ (X.card + R.card) * (X.card + R.card - 1)) ∧
    (5 ≤ d → 2 * (X.card * 13 + R.card * 13) ≤ (X.card + R.card) * (X.card + R.card - 1)) := by
  have XF : X ⊆ X ∪ R := subset_union_left
  have dif : (X ∪ R) \ X = R := by
    ext v
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, n⟩
      · exact absurd h n
      · exact h
    · intro h
      exact ⟨Or.inr h, fun hx => disjoint_left.mp dis hx h⟩
  have cF : (X ∪ R).card = X.card + R.card := card_union_of_disjoint dis
  have deg : ∀ v ∈ X ∪ R, d ≤ (outN D (X ∪ R) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [nineX v h]; exact hd9
    · exact degR v h
  have deg2 : ∀ v ∈ X ∪ R, 2 ≤ (outN D (X ∪ R) v).card := fun v hv => hd.trans (deg v hv)
  have onX : ∀ x ∈ X, 12 ≤ ((ball D (X ∪ R) x 3).erase x).card :=
    fun x hx => T.nine _ fr deg2 x (XF hx) (nineX x hx)
  have B := fun a b hX hR => T.budget (X ∪ R) fr X XF a b hX hR
  rw [dif, cF] at B
  refine ⟨fun e => B 12 6 onX (fun v hv => T.t2 _ fr deg2 v (mem_union_right _ hv)),
    fun e => B 12 9 onX (fun v hv => T.t3 _ fr (fun w hw => by rw [← e]; exact deg w hw) v
      (mem_union_right _ hv)),
    fun e => B 11 11 (fun x hx => T.t4 _ fr (fun w hw => by rw [← e]; exact deg w hw) x (XF hx))
      (fun v hv => T.t4 _ fr (fun w hw => by rw [← e]; exact deg w hw) v (mem_union_right _ hv)),
    fun e => B 13 13 (fun x hx => T.t5 _ fr (fun w hw => e.trans (deg w hw)) x (XF hx))
      (fun v hv => T.t5 _ fr (fun w hw => e.trans (deg w hw)) v (mem_union_right _ hv))⟩

section root2

/-- **B2, `|W| + |J| ≥ 16`.** Root with `(w_2, w_3) = (8, 8)`. -/
theorem wj_sixteen (T : Tables D) (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hu : u ∈ V) (tight : TightR D V 9 u) :
    16 ≤ (layer D V 4 u).card + (layer D V 5 u).card := by
  have thin := tight.1
  have z8 := tight_third free (by norm_num) reg hu tight (by norm_num)
  have w8 := (tight_ball_four free (by norm_num) reg hu tight (by norm_num) (by norm_num)).1
  have zkeep := z_keep free (by norm_num) reg hu tight (by norm_num) (by norm_num)
  by_contra small
  push Not at small
  have FV : layer D V 3 u ∪ layer D V 4 u ⊆ V := union_subset layer_subset layer_subset
  have fr : QFree D (layer D V 3 u ∪ layer D V 4 u) 6 := free.mono_set FV
  have dis : Disjoint (layer D V 3 u) (layer D V 4 u) := layer_disj (by norm_num)
  have nineZ : ∀ z ∈ layer D V 3 u, (outN D (layer D V 3 u ∪ layer D V 4 u) z).card = 9 := by
    intro z hz
    have c := keep_count (F := layer D V 3 u ∪ layer D V 4 u) (E := ∅) (v := z)
      (by rw [union_empty]; exact zkeep z hz)
    have := out_le (D := D) FV (v := z)
    rw [reg z (layer_subset hz)] at c this
    simp only [card_empty] at c
    omega
  have degW : ∀ v ∈ layer D V 4 u,
      (layer D V 4 u).card - 6 ≤ (outN D (layer D V 3 u ∪ layer D V 4 u) v).card := by
    intro v hv
    have cover : outN D V v ⊆ (layer D V 3 u ∪ layer D V 4 u) ∪ layer D V 5 u := by
      intro t ht
      obtain ⟨tV, vt⟩ := mem_outN.mp ht
      have t5 : t ∈ ball D V u (2 + 3) := ball_step (mem_layer.mp hv).1 tV vt
      have t2 : t ∉ ball D V u 2 := by
        intro h
        by_cases h1 : t ∈ ball D V u 1
        · rcases (mem_ball_one hu).mp h1 with e | hx
          · rw [e] at vt
            exact no_back_u free hu (by norm_num) hv vt
          · exact no_back_x free reg hu thin (by norm_num) le_rfl hv hx vt
        · exact no_back_y free reg hu tight (by norm_num) (by norm_num) hv
            (mem_layer.mpr ⟨h, h1⟩) vt
      exact three_layers t5 t2
    have c := keep_count cover
    rw [reg v (layer_subset hv)] at c
    omega
  have cF := fragment_budget T dis fr nineZ (d := (layer D V 4 u).card - 6) (by omega) (by omega)
    degW
  obtain ⟨c2, c3, c4, c5⟩ := cF
  have z8' : (layer D V 3 u).card = 8 := by omega
  rw [z8'] at c2 c3 c4 c5
  obtain ⟨w, hw⟩ : ∃ w, (layer D V 4 u).card = w := ⟨_, rfl⟩
  rw [hw] at c2 c3 c4 c5 small w8
  have lo : 8 ≤ w := by omega
  have hi : w ≤ 15 := by omega
  interval_cases w
  · have := c2 rfl; norm_num at this
  · have := c3 rfl; norm_num at this
  · have := c4 rfl; norm_num at this
  all_goals (have := c5 (by norm_num); norm_num at this)

/-- **B2.** At a root with `(w_2, w_3) = (8, 8)`, a row of `Y` pointing to all of `Z` has
`|B_3| ≥ 28`. -/
theorem complete_y_28 (T : Tables D) (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hu : u ∈ V) (tight : TightR D V 9 u) {s : ℕ} (hs : s ∈ layer D V 2 u)
    (full : layer D V 3 u ⊆ outN D V s) : 28 ≤ (ball D V s 3).card := by
  have := y_ball free reg hu tight hs full
  have := wj_sixteen T free reg hu tight
  have := tight_third free (by norm_num) reg hu tight (by norm_num)
  omega

/-- **B3, `|W| ≥ 8`.** A thin root with `|B_3| = 27` (profile `(8, 9)`). -/
theorem w_eight (T : Tables D) (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hu : u ∈ V) (thin : Thin D V 9 u) (b3 : (ball D V u 3).card = 27) :
    8 ≤ (layer D V 4 u).card := by
  have L := (balls_by_layers free (by norm_num) reg hu).2.2
  have yc := thin
  unfold Thin at yc
  have z9 : (layer D V 3 u).card = 9 := by omega
  have ykeep := y_keep_r free (by norm_num) reg hu thin (by norm_num)
  by_contra small
  push Not at small
  have FV : layer D V 2 u ∪ layer D V 3 u ⊆ V := union_subset layer_subset layer_subset
  have fr : QFree D (layer D V 2 u ∪ layer D V 3 u) 6 := free.mono_set FV
  have dis : Disjoint (layer D V 2 u) (layer D V 3 u) := layer_disj (by norm_num)
  have nineY : ∀ y ∈ layer D V 2 u, (outN D (layer D V 2 u ∪ layer D V 3 u) y).card = 9 := by
    intro y hy
    have c := keep_count (F := layer D V 2 u ∪ layer D V 3 u) (E := ∅) (v := y)
      (by rw [union_empty]; exact ykeep y hy)
    have := out_le (D := D) FV (v := y)
    rw [reg y (layer_subset hy)] at c this
    simp only [card_empty] at c
    omega
  have degZ : ∀ v ∈ layer D V 3 u, 2 ≤ (outN D (layer D V 2 u ∪ layer D V 3 u) v).card := by
    intro v hv
    have cover : outN D V v ⊆ (layer D V 2 u ∪ layer D V 3 u) ∪ layer D V 4 u := by
      intro t ht
      obtain ⟨tV, vt⟩ := mem_outN.mp ht
      have t4 : t ∈ ball D V u (1 + 3) := ball_step (mem_layer.mp hv).1 tV vt
      have t1 : t ∉ ball D V u 1 := by
        intro h1
        rcases (mem_ball_one hu).mp h1 with e | hx
        · rw [e] at vt
          exact no_back_u free hu (by norm_num) hv vt
        · exact no_back_x free reg hu thin (by norm_num) (by norm_num) hv hx vt
      exact three_layers t4 t1
    have c := keep_count cover
    rw [reg v (layer_subset hv)] at c
    omega
  have cF := (fragment_budget T dis fr nineY (d := 2) le_rfl (by norm_num) degZ).1 rfl
  have y8 : (layer D V 2 u).card = 8 := by omega
  rw [y8, z9] at cF
  norm_num at cF

/-- **B3.** A complete head `x` of a thin root with `|B_3| = 27` has `|B_3(x)| ≥ 29`. -/
theorem complete_x_29 (T : Tables D) (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hu : u ∈ V) (thin : Thin D V 9 u) (b3 : (ball D V u 3).card = 27) {x : ℕ}
    (hx : x ∈ complete D V u) : 29 ≤ (ball D V x 3).card := by
  have := x_ball free reg hu thin hx
  have := w_eight T free reg hu thin b3
  have L := (balls_by_layers free (by norm_num) reg hu).2.2
  have yc := thin
  unfold Thin at yc
  omega

/-! ### B4: packaging by the third layer -/

/-- Rows with `|B_3| ≥ 28` pointing to all of `Z`, with exactly one other head, which also points
to all of `Z`. Depends only on `D`, `V` and the set `Z`. -/
noncomputable def zSet (D : CH.Digraph) (V Z : Finset ℕ) : Finset ℕ :=
  V.filter (fun s => 28 ≤ (ball D V s 3).card ∧ Z ⊆ outN D V s ∧ (outN D V s \ Z).card = 1 ∧
    ∀ e ∈ outN D V s \ Z, Z ⊆ outN D V e)

/-- **B4.** A root with `(w_2, w_3) = (8, 8)` has at least five rows in
`zSet D V (layer D V 3 u)`. -/
theorem zSet_count (T : Tables D) (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hu : u ∈ V) (tight : TightR D V 9 u) : 5 ≤ (zSet D V (layer D V 3 u)).card := by
  obtain ⟨-, -, -, five, each⟩ := s5_incidence free reg hu tight
  refine five.trans (card_le_card fun s hs => ?_)
  obtain ⟨full, rest, full'⟩ := each s hs
  have sY := lone_subset (mem_good.mp hs).1
  refine mem_filter.mpr ⟨layer_subset sY, complete_y_28 T free reg hu tight sY full, full, ?_, ?_⟩
  · rw [rest, card_singleton]
  · intro e he
    rw [rest, mem_singleton] at he
    rw [he]
    exact full'

/-- **B4, exclusivity.** A row cannot lie in `zSet` for two different sets of the same size
(`2 ≤ q`): the two remaining heads would point to each other. -/
theorem zSet_exclusive {q : ℕ} (free : QFree D V q) (hq : 2 ≤ q) {Z Z' : Finset ℕ} (ne : Z ≠ Z')
    (hc : Z.card = Z'.card) {s : ℕ} (h : s ∈ zSet D V Z) (h' : s ∈ zSet D V Z') : False := by
  obtain ⟨-, -, sub, one, all⟩ := mem_filter.mp h
  obtain ⟨-, -, sub', one', all'⟩ := mem_filter.mp h'
  -- `Z'` has a label outside `Z`, necessarily the remaining head of `s` for `Z`
  have out : ∀ {A B : Finset ℕ}, A ≠ B → A.card = B.card → ∃ t ∈ B, t ∉ A := by
    intro A B nAB cAB
    by_contra hall
    push Not at hall
    exact nAB (eq_of_subset_of_card_le hall (by omega)).symm
  obtain ⟨t, t_in, t_out⟩ := out ne hc
  obtain ⟨t', t'_in, t'_out⟩ := out (Ne.symm ne) hc.symm
  have tm : t ∈ outN D V s \ Z := mem_sdiff.mpr ⟨sub' t_in, t_out⟩
  have tm' : t' ∈ outN D V s \ Z' := mem_sdiff.mpr ⟨sub t'_in, t'_out⟩
  have a1 := (mem_outN.mp (all t tm t'_in)).2
  have a2 := (mem_outN.mp (all' t' tm' t_in)).2
  have tV := (mem_outN.mp (mem_sdiff.mp tm).1).1
  have t'V := (mem_outN.mp (mem_sdiff.mp tm').1).1
  exact free t 2 (by omega) hq (.step t'V a1 (.step tV a2 (.refl t)))

end root2

#print axioms x_reach_y_g
#print axioms no_back_x_g
#print axioms no_back_y_g
#print axioms good_y_g
#print axioms s5_generic
#print axioms layer_ball
#print axioms zRows_count
#print axioms zRows_exclusive
#print axioms x_reach
#print axioms no_back_x
#print axioms no_back_y
#print axioms s5_incidence
#print axioms y_ball
#print axioms x_ball
#print axioms wj_sixteen
#print axioms complete_y_28
#print axioms w_eight
#print axioms complete_x_29
#print axioms zSet_count
#print axioms zSet_exclusive

end LeanCH.BR.Supplier54
