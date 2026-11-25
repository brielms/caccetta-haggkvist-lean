import checkpoints.shen_extension.Supplier54
import checkpoints.shen_extension.Profile54

/-!
# Two suppliers at a root that is not thin (`r = q + 3`; instance `q = 6`, `r = 9`)

`free : QFree D V q`, every out-degree `q + 3`, a root `u ∈ V` with layers
`X = outN D V u`, `Y = layer D V 2 u`, `Z = layer D V 3 u`, `W = layer D V 4 u`,
`J = layer D V 5 u`, `|Y| = q + 3`, `|Z| = q + 2` (at `q = 6`: `|Y| = 9`, `|Z| = 8`).

* A *tail* (`IsTail`) is a row with a head in `X`. `oSet` = rows of `Y` reaching a tail by a
  walk inside `Y`; `aSet = Y \ oSet`.
* Lemma 6 (`a_cover`, `a_deg`, `a_counts`, `lone_complete`, `good_two`, `good_supplier`):
  rows of `A` keep their heads in `A ∪ Z`; `|A| ≥ q + 1`, so `|O| ≤ 2`; at least
  `2q + 2 - |A|` rows of `A` are complete to `Z`; at least two good rows (suppliers).
  At `|A| = q + 3` the good count is `OneHead.good_top`.
* Lemma 7 (`no_return`, generic, `6 ≤ q`): no arc from `Z` or `W` into `{u} ∪ X ∪ Y`.
  The proof differs from the paper: `low_near` (degree-two CH) shows that every row of `X`
  has itself or an `X`-head with at most `q - 2` heads in `X`; that row has at least five
  heads in `Y` and meets one of the `≥ q - 1` complete rows of `A` (`x_meet`). So step (d)
  needs nothing from Lemma 5.
* Lemma 8 (`w_big` generic `|W| ≥ q + 2`; `wj_sixteen` instance `q = 6`;
  `complete_ball_A` generic `|B_3(s)| ≥ 4 + |Z| + |W| + |J|`).
* S2 (`zSetB`, `two_suppliers` generic; `two_suppliers_54`, `s2_of_hO` instance, concluding
  with `Supplier54.zSet`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.SupplierFat54
open Finset BRq2 BRq3 ThinSuppliers OneHead
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)

variable {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}

/-! ### Generic helpers -/

theorem ball_mono_set {W W' : Finset ℕ} (h : W ⊆ W') {x k : ℕ} :
    ball D W x k ⊆ ball D W' x k := by
  intro v hv
  obtain ⟨vW, j, hj, w⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨h vW, j, hj, w.mono h⟩

theorem ball_cons {y x v k : ℕ} (xV : x ∈ V) (yx : D y x = true) (hv : v ∈ ball D V x k) :
    v ∈ ball D V y (k + 1) := by
  obtain ⟨vV, j, hj, w⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨vV, j + 1, by omega, .step xV yx w⟩

theorem layer_disj {i j : ℕ} (h : i < j) : Disjoint (layer D V i u) (layer D V j u) := by
  rw [disjoint_left]
  intro v hi hj
  exact (mem_layer.mp hj).2 (ball_mono_radius (by omega) (mem_layer.mp hi).1)

theorem layers_from (hu : u ∈ V) {x j m : ℕ} (hj : 1 ≤ j) (base : layer D V j u ⊆ ball D V x m) :
    ∀ t, layer D V (j + t) u ⊆ ball D V x (m + t) := by
  intro t
  induction t with
  | zero => simpa using base
  | succ t ih =>
    intro v hv
    obtain ⟨p, hp, pv⟩ := ShapeClimbRoot.parent_mem hu (i := j + t) (by omega) hv
    exact ball_step (ih hp) (layer_subset hv) pv

theorem keep_count {F E : Finset ℕ} {v : ℕ} (cover : outN D V v ⊆ F ∪ E) :
    (outN D V v).card ≤ (outN D F v).card + E.card := by
  have : outN D V v ⊆ outN D F v ∪ E := by
    intro t ht
    rcases mem_union.mp (cover ht) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp ht).2⟩)
    · exact mem_union_right _ h
  exact (card_le_card this).trans (card_union_le _ _)

theorem four_pieces {A B C E T : Finset ℕ} (dAB : Disjoint A B) (dAC : Disjoint A C)
    (dAE : Disjoint A E) (dBC : Disjoint B C) (dBE : Disjoint B E) (dCE : Disjoint C E)
    (hA : A ⊆ T) (hB : B ⊆ T) (hC : C ⊆ T) (hE : E ⊆ T) :
    A.card + B.card + C.card + E.card ≤ T.card := by
  have d2 : Disjoint B (C ∪ E) := disjoint_union_right.mpr ⟨dBC, dBE⟩
  have d3 : Disjoint A (B ∪ (C ∪ E)) :=
    disjoint_union_right.mpr ⟨dAB, disjoint_union_right.mpr ⟨dAC, dAE⟩⟩
  have := card_le_card (union_subset hA (union_subset hB (union_subset hC hE)))
  rw [card_union_of_disjoint d3, card_union_of_disjoint d2, card_union_of_disjoint dCE] at this
  omega

theorem in_ball_two (hu : u ∈ V) {w : ℕ} (h : w ∈ ball D V u 2) :
    w = u ∨ w ∈ outN D V u ∨ w ∈ layer D V 2 u := by
  by_cases h1 : w ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp h1 with e | hx
    · exact Or.inl e
    · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (mem_layer.mpr ⟨h, h1⟩))

/-- Within `k + 2` but not within `k`: layer `k + 1` or `k + 2`. -/
theorem two_layers {k t : ℕ} (h1 : t ∈ ball D V u (k + 2)) (h0 : t ∉ ball D V u k) :
    t ∈ layer D V (k + 1) u ∪ layer D V (k + 2) u := by
  by_cases a : t ∈ ball D V u (k + 1)
  · exact mem_union_left _ (mem_layer.mpr ⟨a, by rw [show k + 1 - 1 = k by omega]; exact h0⟩)
  · exact mem_union_right _ (mem_layer.mpr ⟨h1, by rw [show k + 2 - 1 = k + 1 by omega]; exact a⟩)

theorem three_layers {k t : ℕ} (h1 : t ∈ ball D V u (k + 3)) (h0 : t ∉ ball D V u k) :
    t ∈ layer D V (k + 1) u ∪ layer D V (k + 2) u ∪ layer D V (k + 3) u := by
  by_cases b : t ∈ ball D V u (k + 2)
  · exact mem_union_left _ (two_layers b h0)
  · exact mem_union_right _ (mem_layer.mpr ⟨h1, by rw [show k + 3 - 1 = k + 2 by omega]; exact b⟩)

/-- A row of the second layer points into `X ∪ Y ∪ Z` (`3 ≤ q`). -/
theorem y_cover (free : QFree D V q) (hq : 3 ≤ q) (hu : u ∈ V) {y : ℕ}
    (hy : y ∈ layer D V 2 u) :
    outN D V y ⊆ outN D V u ∪ layer D V 2 u ∪ layer D V 3 u := by
  intro w hw
  obtain ⟨wV, yw⟩ := mem_outN.mp hw
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have wb : w ∈ ball D V u 3 := ball_step yb wV yw
  by_cases n2 : w ∈ ball D V u 2
  · rcases in_ball_two hu n2 with e | hx | hY
    · rw [e] at yw
      exact absurd yw (no_back_arc free hu yb (by omega))
    · exact mem_union_left _ (mem_union_left _ hx)
    · exact mem_union_left _ (mem_union_right _ hY)
  · exact mem_union_right _ (mem_layer.mpr ⟨wb, n2⟩)

/-! ### Tails, `O` and `A` -/

/-- A row with a head among the heads of `u`. -/
def IsTail (D : CH.Digraph) (V : Finset ℕ) (u y : ℕ) : Prop := ∃ x ∈ outN D V u, D y x = true

/-- `O`: rows of `Y` that reach a tail by a walk inside `Y`. -/
noncomputable def oSet (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ := by
  classical
  exact (layer D V 2 u).filter (fun y => ∃ t, IsTail D V u t ∧ ∃ j, Walk D (layer D V 2 u) y t j)

/-- `A = Y \ O`. -/
noncomputable def aSet (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  layer D V 2 u \ oSet D V u

theorem mem_oSet {y : ℕ} : y ∈ oSet D V u ↔
    y ∈ layer D V 2 u ∧ ∃ t, IsTail D V u t ∧ ∃ j, Walk D (layer D V 2 u) y t j := by
  classical
  unfold oSet
  exact mem_filter

theorem oSet_subset : oSet D V u ⊆ layer D V 2 u := fun _ h => (mem_oSet.mp h).1

theorem aSet_subset : aSet D V u ⊆ layer D V 2 u := sdiff_subset

theorem aSet_V : aSet D V u ⊆ V := aSet_subset.trans layer_subset

theorem tail_o {y : ℕ} (hy : y ∈ layer D V 2 u) (ht : IsTail D V u y) : y ∈ oSet D V u :=
  mem_oSet.mpr ⟨hy, y, ht, 0, .refl y⟩

theorem o_pre {y w : ℕ} (hy : y ∈ layer D V 2 u) (hw : w ∈ oSet D V u) (yw : D y w = true) :
    y ∈ oSet D V u := by
  obtain ⟨wY, t, tt, j, walk⟩ := mem_oSet.mp hw
  exact mem_oSet.mpr ⟨hy, t, tt, j + 1, .step wY yw walk⟩

theorem oa_card : (oSet D V u).card + (aSet D V u).card = (layer D V 2 u).card := by
  unfold aSet
  rw [card_sdiff_of_subset oSet_subset]
  have := card_le_card (oSet_subset (D := D) (V := V) (u := u))
  omega

theorem a_nonempty (hO : oSet D V u ≠ layer D V 2 u) : (aSet D V u).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have := oa_card (D := D) (V := V) (u := u)
  rw [h, card_empty] at this
  exact hO (eq_of_subset_of_card_le oSet_subset (by omega))

/-! ### Lemma 6 -/

section six
variable (free : QFree D V q) (hu : u ∈ V)

include free hu in
/-- **Lemma 6(i).** A row of `A` points only into `A ∪ Z` (`3 ≤ q`). -/
theorem a_cover (hq : 3 ≤ q) {a : ℕ} (ha : a ∈ aSet D V u) :
    outN D V a ⊆ aSet D V u ∪ layer D V 3 u := by
  obtain ⟨aY, aO⟩ := mem_sdiff.mp ha
  intro w hw
  rcases mem_union.mp (y_cover free hq hu aY hw) with h | hZ
  · rcases mem_union.mp h with hx | hY
    · exact absurd (tail_o aY ⟨w, hx, (mem_outN.mp hw).2⟩) aO
    · by_cases wO : w ∈ oSet D V u
      · exact absurd (o_pre aY wO (mem_outN.mp hw).2) aO
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hY, wO⟩)
  · exact mem_union_right _ hZ

include free hu in
/-- **Lemma 6(ii).** Every row of `A` has a head in `A`. -/
theorem a_deg (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hZ : (layer D V 3 u).card = q + 2) : ∀ a ∈ aSet D V u, 1 ≤ (outN D (aSet D V u) a).card := by
  intro a ha
  have c := keep_count (a_cover free hu hq ha)
  rw [reg a (aSet_V ha), hZ] at c
  omega

include free hu in
/-- **Lemma 6(iii).** `|A| ≥ q + 1` and at least `2q + 2 - |A|` one-head rows. -/
theorem a_counts (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) :
    q + 1 ≤ (aSet D V u).card ∧ 2 * q + 2 ≤ (aSet D V u).card + (lone D (aSet D V u)).card ∧
      (aSet D V u).card ≤ q + 3 := by
  have le : (aSet D V u).card ≤ q + 3 := by
    have := oa_card (D := D) (V := V) (u := u); omega
  have c := one_head_count (free.mono_set aSet_V) (by omega) (a_deg free hu hq reg hZ) ne (by omega)
  have := card_le_card (lone_subset (D := D) (S := aSet D V u))
  exact ⟨by omega, c, le⟩

include free hu in
/-- **Lemma 6(iv).** A one-head row of `A` points to all of `Z`. -/
theorem lone_complete (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hZ : (layer D V 3 u).card = q + 2) {p : ℕ} (hp : p ∈ lone D (aSet D V u)) :
    layer D V 3 u ⊆ outN D V p :=
  lone_full (r := q + 3) (a_cover free hu hq (lone_subset hp)) (reg p (aSet_V (lone_subset hp))).ge
    (mem_lone.mp hp).2 (by omega)

end six

section six2
variable (free : QFree D V q) (hu : u ∈ V)

include free hu in
/-- **Lemma 6(v).** At least two good rows of `A` (`OneHead.good_count`, and
`OneHead.good_top` when `|A| = q + 3`; `6 ≤ q`). -/
theorem good_two (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) : 2 ≤ (good D (aSet D V u)).card := by
  obtain ⟨-, -, le⟩ := a_counts free hu (by omega) reg hY hZ ne
  by_cases top : (aSet D V u).card = q + 3
  · exact good_top (free.mono_set aSet_V) hq (a_deg free hu (by omega) reg hZ) top
  · have := good_count (free.mono_set aSet_V) (by omega) (a_deg free hu (by omega) reg hZ) ne
      (by omega)
    omega

include free hu in
/-- **Lemma 6(vi).** A good row `s` of `A` points to all of `Z`, its one other head is its
`A`-head, which also points to all of `Z`. -/
theorem good_supplier (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hZ : (layer D V 3 u).card = q + 2) {s : ℕ} (hs : s ∈ good D (aSet D V u)) :
    layer D V 3 u ⊆ outN D V s ∧
      outN D V s \ layer D V 3 u = {hd D (aSet D V u) s} ∧
      layer D V 3 u ⊆ outN D V (hd D (aSet D V u) s) := by
  obtain ⟨sl, hl⟩ := mem_good.mp hs
  have deg := a_deg free hu hq reg hZ
  refine ⟨lone_complete free hu hq reg hZ sl, ?_, lone_complete free hu hq reg hZ hl⟩
  ext w
  constructor
  · intro hw
    obtain ⟨hw1, hw2⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (a_cover free hu hq (lone_subset sl) hw1) with h | h
    · have : w ∈ outN D (aSet D V u) s := mem_outN.mpr ⟨h, (mem_outN.mp hw1).2⟩
      rwa [hd_spec deg sl] at this
    · exact absurd h hw2
  · intro hw
    rw [mem_singleton.mp hw]
    obtain ⟨hA, arc⟩ := hd_mem deg sl
    exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨aSet_V hA, arc⟩,
      fun hz => disjoint_left.mp (layer_disj (D := D) (V := V) (u := u) (by norm_num : 2 < 3))
        (aSet_subset hA) hz⟩

end six2

/-! ### Lemma 7 -/

/-- **Low row nearby (generic).** In a `q`-free set `X` with `|X| ≤ 2q` and `|X| + 1 ≤ 2m`,
every row has at most `m - 1` heads, or a head with at most `m - 1` heads (degree-two CH on
the heads of `x`). -/
theorem low_near {X : Finset ℕ} (free : QFree D X q) (hq : 2 ≤ q) {m : ℕ}
    (hm : X.card + 1 ≤ 2 * m) (hX : X.card ≤ 2 * q) {x : ℕ} (hx : x ∈ X) :
    (outN D X x).card < m ∨ ∃ c ∈ outN D X x, (outN D X c).card < m := by
  by_contra h
  push Not at h
  obtain ⟨hk, hall⟩ := h
  set N := outN D X x with hN
  have NX : N ⊆ X := outN_subset
  have xN : x ∉ N := fun h => loopfree free (by omega) hx (mem_outN.mp h).2
  have iXN : insert x N ⊆ X := insert_subset hx NX
  have cI : (insert x N).card = N.card + 1 := card_insert_of_notMem xN
  have cR : (X \ insert x N).card = X.card - (N.card + 1) := by
    rw [card_sdiff_of_subset iXN, cI]
  have le := card_le_card iXN
  have deg2 : ∀ h ∈ N, 2 ≤ (outN D N h).card := by
    intro h hh
    obtain ⟨hX', xh⟩ := mem_outN.mp hh
    have cover : outN D X h ⊆ N ∪ (X \ insert x N) := by
      intro w hw
      obtain ⟨wX, hw'⟩ := mem_outN.mp hw
      by_cases wN : w ∈ N
      · exact mem_union_left _ wN
      · refine mem_union_right _ (mem_sdiff.mpr ⟨wX, fun hi => ?_⟩)
        rcases mem_insert.mp hi with e | e
        · rw [e] at hw'
          exact digonfree free hq hx hX' xh hw'
        · exact wN e
    have c : (outN D X h).card ≤ (outN D N h).card + (X \ insert x N).card := by
      have : outN D X h ⊆ outN D N h ∪ (X \ insert x N) := by
        intro t ht
        rcases mem_union.mp (cover ht) with e | e
        · exact mem_union_left _ (mem_outN.mpr ⟨e, (mem_outN.mp ht).2⟩)
        · exact mem_union_right _ e
      exact (card_le_card this).trans (card_union_le _ _)
    have := hall h hh
    omega
  have ne : N.Nonempty := card_pos.mp (by omega)
  have := Profile54.two_order (free.mono_set NX) (by omega) ne deg2
  omega


/-- Reaching `Z` within `m` reaches `W` within `m + 1`. -/
theorem w_of_z (hu : u ∈ V) {v m : ℕ} (base : layer D V 3 u ⊆ ball D V v m) :
    layer D V 4 u ⊆ ball D V v (m + 1) := by
  intro w hw
  obtain ⟨p, hp, pw⟩ := ShapeClimbRoot.parent_mem (D := D) (V := V) (u := u) hu (i := 3)
    (by norm_num) hw
  exact ball_step (base hp) (layer_subset hw) pw

section seven
variable (free : QFree D V q) (hu : u ∈ V)

include free hu in
/-- `X`-heads plus `Y`-heads of a head of `u` number at least `q + 3`. -/
theorem x_split (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3) {x : ℕ}
    (hx : x ∈ outN D V u) :
    q + 3 ≤ (outN D (outN D V u) x).card + (outN D (layer D V 2 u) x).card := by
  have keep := LoopCollar.head_keep free hq hu x hx
  have sub : outN D V x ⊆ outN D (outN D V u) x ∪ outN D (layer D V 2 u) x := by
    intro w hw
    obtain ⟨-, a⟩ := mem_outN.mp hw
    rcases mem_union.mp (keep hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, a⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨h, a⟩)
  have := (card_le_card sub).trans (card_union_le _ _)
  rw [reg x (outN_subset hx)] at this
  exact this

include free hu in
/-- **Lemma 7, steps (a)-(d).** Every head of `u` reaches a one-head row of `A` within two
steps (`6 ≤ q`). -/
theorem x_meet (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {x : ℕ} (hx : x ∈ outN D V u) :
    ∃ a ∈ lone D (aSet D V u), a ∈ ball D V x 2 := by
  obtain ⟨-, cnt, le⟩ := a_counts free hu (by omega) reg hY hZ ne
  have XV : outN D V u ⊆ V := outN_subset
  have hXc : (outN D V u).card = q + 3 := reg u hu
  have meet : ∀ c ∈ outN D V u, (outN D (outN D V u) c).card < q - 1 →
      ∃ a ∈ lone D (aSet D V u), D c a = true := by
    intro c hc low
    have sp := x_split free hu (by omega) reg hc
    by_contra none
    have dis : Disjoint (outN D (layer D V 2 u) c) (lone D (aSet D V u)) := by
      rw [disjoint_left]
      intro a ha hl
      exact none ⟨a, hl, (mem_outN.mp ha).2⟩
    have sub : outN D (layer D V 2 u) c ∪ lone D (aSet D V u) ⊆ layer D V 2 u :=
      union_subset outN_subset (lone_subset.trans aSet_subset)
    have := card_le_card sub
    rw [card_union_of_disjoint dis] at this
    omega
  rcases low_near (free.mono_set XV) (by omega) (m := q - 1) (by rw [hXc]; omega)
      (by rw [hXc]; omega) hx with h | ⟨c, hc, h⟩
  · obtain ⟨a, ha, xa⟩ := meet x hx h
    have aV := aSet_V (lone_subset ha)
    exact ⟨a, ha, mem_ball.mpr ⟨aV, 1, by norm_num, .step aV xa (.refl a)⟩⟩
  · obtain ⟨cX, xc⟩ := mem_outN.mp hc
    obtain ⟨a, ha, ca⟩ := meet c cX h
    have aV := aSet_V (lone_subset ha)
    exact ⟨a, ha, mem_ball.mpr ⟨aV, 2, le_rfl, .step (XV cX) xc (.step aV ca (.refl a))⟩⟩

include free hu in
theorem x_reach_z (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {x : ℕ} (hx : x ∈ outN D V u) :
    layer D V 3 u ⊆ ball D V x 3 := by
  obtain ⟨a, ha, ab⟩ := x_meet free hu hq reg hY hZ ne hx
  intro z hz
  exact ball_step ab (layer_subset hz) (mem_outN.mp (lone_complete free hu (by omega) reg hZ ha hz)).2

include free hu in
theorem a_reach_z (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {a : ℕ} (ha : a ∈ aSet D V u) :
    layer D V 3 u ⊆ ball D V a 3 := by
  obtain ⟨-, -, le⟩ := a_counts free hu hq reg hY hZ ne
  obtain ⟨c, cb, cl⟩ := lone_within (free.mono_set aSet_V) (by omega) (a_deg free hu hq reg hZ)
    (k := 2) (by omega) (by omega) (by omega) ha
  intro z hz
  exact ball_step (ball_mono_set aSet_V cb) (layer_subset hz)
    (mem_outN.mp (lone_complete free hu hq reg hZ cl hz)).2

include free hu in
/-- **Lemma 7(e).** Every row of `Y` reaches all of `Z` within four steps (`6 ≤ q`). -/
theorem y_reach_z (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {y : ℕ} (hy : y ∈ layer D V 2 u) :
    layer D V 3 u ⊆ ball D V y 4 := by
  have yV := layer_subset hy
  by_cases hA : y ∈ aSet D V u
  · exact (a_reach_z free hu (by omega) reg hY hZ ne hA).trans (ball_mono_radius (by norm_num))
  by_cases ht : IsTail D V u y
  · obtain ⟨x, hx, yx⟩ := ht
    exact fun z hz => ball_cons (outN_subset hx) yx (x_reach_z free hu hq reg hY hZ ne hx hz)
  by_cases hp : ∃ a ∈ aSet D V u, D y a = true
  · obtain ⟨a, ha, ya⟩ := hp
    exact fun z hz => ball_cons (aSet_V ha) ya (a_reach_z free hu (by omega) reg hY hZ ne ha hz)
  have yO : y ∈ oSet D V u := by
    by_contra h
    exact hA (mem_sdiff.mpr ⟨hy, h⟩)
  have cover : outN D V y ⊆ (oSet D V u).erase y ∪ layer D V 3 u := by
    intro w hw
    obtain ⟨wV, yw⟩ := mem_outN.mp hw
    rcases mem_union.mp (y_cover free (by omega) hu hy hw) with h | hz
    · rcases mem_union.mp h with hx | hY'
      · exact absurd ⟨w, hx, yw⟩ ht
      · by_cases wA : w ∈ aSet D V u
        · exact absurd ⟨w, wA, yw⟩ hp
        · have wO : w ∈ oSet D V u := by
            by_contra h'
            exact wA (mem_sdiff.mpr ⟨hY', h'⟩)
          refine mem_union_left _ (mem_erase.mpr ⟨?_, wO⟩)
          rintro rfl
          exact loopfree free (by omega) yV yw
    · exact mem_union_right _ hz
  obtain ⟨cA, -, -⟩ := a_counts free hu (by omega) reg hY hZ ne
  have oc := oa_card (D := D) (V := V) (u := u)
  have one : (outN D ((oSet D V u).erase y) y).card ≤ 1 := by
    have := card_le_card (outN_subset (D := D) (W := (oSet D V u).erase y) (y := y))
    rw [card_erase_of_mem yO] at this
    omega
  have full := lone_full (r := q + 3) cover (reg y yV).ge one (by omega)
  intro z hz
  exact ball_mono_radius (by norm_num : 1 ≤ 4) ((mem_ball_one yV).mpr (Or.inr (full hz)))

include free hu in
/-- **Lemma 7.** No arc from `Z` or `W` to `u`, into `X` or into `Y` (`6 ≤ q`). -/
theorem no_return (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {j : ℕ} (hj3 : 3 ≤ j) (hj4 : j ≤ 4) {t : ℕ}
    (ht : t ∈ layer D V j u) {v : ℕ}
    (hv : v = u ∨ v ∈ outN D V u ∨ v ∈ layer D V 2 u) : ¬ D t v = true := by
  have tb : t ∈ ball D V u 4 := ball_mono_radius hj4 (mem_layer.mp ht).1
  rcases hv with rfl | hx | hy
  · exact no_back_arc free hu tb (by omega)
  · have zb := x_reach_z free hu hq reg hY hZ ne hx
    have wb := w_of_z hu zb
    have : t ∈ ball D V v 4 := by
      obtain rfl | rfl : j = 3 ∨ j = 4 := by omega
      · exact ball_mono_radius (by norm_num) (zb ht)
      · exact wb ht
    exact no_back_arc free (outN_subset hx) this (by omega)
  · have zb := y_reach_z free hu hq reg hY hZ ne hy
    have wb := w_of_z hu zb
    have : t ∈ ball D V v 5 := by
      obtain rfl | rfl : j = 3 ∨ j = 4 := by omega
      · exact ball_mono_radius (by norm_num) (zb ht)
      · exact wb ht
    exact no_back_arc free (layer_subset hy) this (by omega)

/-! ### Lemma 8 -/

include free hu in
/-- Rows of `Z` point into `Z ∪ W`. -/
theorem z_cover (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {z : ℕ} (hz : z ∈ layer D V 3 u) :
    outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
  intro w hw
  obtain ⟨wV, zw⟩ := mem_outN.mp hw
  have wb : w ∈ ball D V u (2 + 2) := ball_step (mem_layer.mp hz).1 wV zw
  have n2 : w ∉ ball D V u 2 := fun h =>
    no_return free hu hq reg hY hZ ne le_rfl (by norm_num) hz (in_ball_two hu h) zw
  exact two_layers wb n2

include free hu in
/-- Rows of `W` point into `Z ∪ W ∪ J`. -/
theorem w_cover (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {w : ℕ} (hw : w ∈ layer D V 4 u) :
    outN D V w ⊆ layer D V 3 u ∪ layer D V 4 u ∪ layer D V 5 u := by
  intro t ht
  obtain ⟨tV, wt⟩ := mem_outN.mp ht
  have tb : t ∈ ball D V u (2 + 3) := ball_step (mem_layer.mp hw).1 tV wt
  have n2 : t ∉ ball D V u 2 := fun h =>
    no_return free hu hq reg hY hZ ne (by norm_num) le_rfl hw (in_ball_two hu h) wt
  exact three_layers tb n2

include free hu in
/-- **Lemma 8, `|W| ≥ q + 2`.** Otherwise every row of `Z` has two heads in `Z`
(degree-two CH on `q + 2` labels). -/
theorem w_big (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) : q + 2 ≤ (layer D V 4 u).card := by
  by_contra small
  have deg : ∀ z ∈ layer D V 3 u, 2 ≤ (outN D (layer D V 3 u) z).card := by
    intro z hz
    have c := keep_count (z_cover free hu hq reg hY hZ ne hz)
    rw [reg z (layer_subset hz)] at c
    omega
  obtain ⟨z0, hz0⟩ : (layer D V 3 u).Nonempty := card_pos.mp (by omega)
  have := Profile54.two_order (free.mono_set layer_subset) (by omega) ⟨z0, hz0⟩ deg
  omega

include free hu in
/-- **Lemma 8, ball part (generic, `3 ≤ q`).** A row `s` of `A` pointing to all of `Z` has
`|B_3(s)| ≥ 4 + |Z| + |W| + |J|`. -/
theorem complete_ball_A (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hZ : (layer D V 3 u).card = q + 2) {s : ℕ} (hs : s ∈ aSet D V u)
    (full : layer D V 3 u ⊆ outN D V s) :
    4 + (layer D V 3 u).card + (layer D V 4 u).card + (layer D V 5 u).card ≤
      (ball D V s 3).card := by
  have AV : aSet D V u ⊆ V := aSet_V
  have sV := AV hs
  have A4 := LoopCollar.ball_grow (free.mono_set AV) (a_deg free hu hq reg hZ) hs 3 hq
  have base : layer D V 3 u ⊆ ball D V s 1 := fun z hz => (mem_ball_one sV).mpr (Or.inr (full hz))
  have hW : layer D V 4 u ⊆ ball D V s 2 := layers_from hu (j := 3) (m := 1) (by norm_num) base 1
  have hJ : layer D V 5 u ⊆ ball D V s 3 := layers_from hu (j := 3) (m := 1) (by norm_num) base 2
  have AY : ball D (aSet D V u) s 3 ⊆ layer D V 2 u := ball_subset.trans aSet_subset
  have := four_pieces (A := ball D (aSet D V u) s 3) (B := layer D V 3 u) (C := layer D V 4 u)
    (E := layer D V 5 u) (T := ball D V s 3)
    ((layer_disj (by norm_num : 2 < 3)).mono_left AY) ((layer_disj (by norm_num : 2 < 4)).mono_left AY)
    ((layer_disj (by norm_num : 2 < 5)).mono_left AY) (layer_disj (by norm_num : 3 < 4))
    (layer_disj (by norm_num : 3 < 5)) (layer_disj (by norm_num : 4 < 5))
    (ball_mono_set AV) (base.trans (ball_mono_radius (by norm_num)))
    (hW.trans (ball_mono_radius (by norm_num))) hJ
  omega

end seven

/-! ### Lemma 8 at `q = 6`: `|W| + |J| ≥ 16` -/

/-- **Lemma 8 (instance `q = 6`, `r = 9`).** The pair budget on `Z ∪ W` with the growth table
(`Profile54`); the budget numbers are specific to `q = 6`. -/
theorem wj_sixteen (free : QFree D V 6) (hu : u ∈ V) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hY : (layer D V 2 u).card = 9) (hZ : (layer D V 3 u).card = 8)
    (ne : (aSet D V u).Nonempty) : 16 ≤ (layer D V 4 u).card + (layer D V 5 u).card := by
  have reg' : ∀ v ∈ V, (outN D V v).card = 6 + 3 := reg
  have wb := w_big free hu le_rfl reg' hY hZ ne
  by_contra small
  push Not at small
  have FV : layer D V 3 u ∪ layer D V 4 u ⊆ V := union_subset layer_subset layer_subset
  have fr : QFree D (layer D V 3 u ∪ layer D V 4 u) 6 := free.mono_set FV
  have dis : Disjoint (layer D V 3 u) (layer D V 4 u) := layer_disj (by norm_num)
  have nineZ : ∀ z ∈ layer D V 3 u, (outN D (layer D V 3 u ∪ layer D V 4 u) z).card = 9 := by
    intro z hz
    rw [Profile54.out_restrict FV (z_cover free hu le_rfl reg' hY hZ ne hz), reg z (layer_subset hz)]
  have degW : ∀ v ∈ layer D V 4 u,
      (layer D V 4 u).card - 6 ≤ (outN D (layer D V 3 u ∪ layer D V 4 u) v).card := by
    intro v hv
    have c := keep_count (w_cover free hu le_rfl reg' hY hZ ne hv)
    rw [reg v (layer_subset hv)] at c
    omega
  have degF : ∀ v ∈ layer D V 3 u ∪ layer D V 4 u,
      (layer D V 4 u).card - 6 ≤ (outN D (layer D V 3 u ∪ layer D V 4 u) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [nineZ v h]; omega
    · exact degW v h
  have deg2 : ∀ v ∈ layer D V 3 u ∪ layer D V 4 u,
      2 ≤ (outN D (layer D V 3 u ∪ layer D V 4 u) v).card := fun v hv => by
    have := degF v hv; omega
  have XF : layer D V 3 u ⊆ layer D V 3 u ∪ layer D V 4 u := subset_union_left
  have dif : (layer D V 3 u ∪ layer D V 4 u) \ layer D V 3 u = layer D V 4 u := by
    ext v
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, n⟩
      · exact absurd h n
      · exact h
    · intro h
      exact ⟨Or.inr h, fun hx => disjoint_left.mp dis hx h⟩
  have cF : (layer D V 3 u ∪ layer D V 4 u).card = (layer D V 3 u).card + (layer D V 4 u).card :=
    card_union_of_disjoint dis
  have bud : ∀ a b : ℕ,
      (∀ x ∈ layer D V 3 u, a ≤ Profile54.reach D (layer D V 3 u ∪ layer D V 4 u) 3 x) →
      (∀ v ∈ layer D V 4 u, b ≤ Profile54.reach D (layer D V 3 u ∪ layer D V 4 u) 3 v) →
      2 * (8 * a + (layer D V 4 u).card * b) ≤
        (8 + (layer D V 4 u).card) * (8 + (layer D V 4 u).card - 1) := by
    intro a b hX hW
    have := Profile54.budget_floor fr le_rfl XF hX (by rw [dif]; exact hW)
    rw [dif, cF, hZ] at this
    exact this
  have onZ : ∀ x ∈ layer D V 3 u, 12 ≤ Profile54.reach D (layer D V 3 u ∪ layer D V 4 u) 3 x :=
    fun x hx => Profile54.nine_row fr (XF hx) (nineZ x hx) deg2
  obtain ⟨w, hw⟩ : ∃ w, (layer D V 4 u).card = w := ⟨_, rfl⟩
  rw [hw] at bud degF small wb
  have hi : w ≤ 15 := by omega
  have lo : 8 ≤ w := by omega
  interval_cases w
  · have := bud 12 6 onZ (fun v hv => Profile54.reach_three_two fr (mem_union_right _ hv) le_rfl deg2)
    norm_num at this
  · have := bud 12 9 onZ (fun v hv => Profile54.reach_three_three fr (mem_union_right _ hv) (d := 3)
      le_rfl (fun t ht => by have := degF t ht; omega))
    norm_num at this
  · have d4 : ∀ t ∈ layer D V 3 u ∪ layer D V 4 u,
        4 ≤ (outN D (layer D V 3 u ∪ layer D V 4 u) t).card :=
      fun t ht => by have := degF t ht; omega
    have := bud 11 11 (fun x hx => Profile54.reach_three_four fr (XF hx) le_rfl d4)
      (fun v hv => Profile54.reach_three_four fr (mem_union_right _ hv) le_rfl d4)
    norm_num at this
  all_goals
    have d5 : ∀ t ∈ layer D V 3 u ∪ layer D V 4 u,
        5 ≤ (outN D (layer D V 3 u ∪ layer D V 4 u) t).card :=
      fun t ht => by have := degF t ht; omega
    have := bud 13 13 (fun x hx => Profile54.reach_three_five fr (XF hx) le_rfl d5)
      (fun v hv => Profile54.reach_three_five fr (mem_union_right _ hv) le_rfl d5)
    norm_num at this

/-! ### S2: packaging by the third layer -/

/-- Rows with `|B_3| ≥ b` pointing to all of `Z`, with exactly one other head, which also points
to all of `Z`. Depends only on `D`, `V`, the set `Z` and `b`. -/
noncomputable def zSetB (D : CH.Digraph) (V Z : Finset ℕ) (b : ℕ) : Finset ℕ :=
  V.filter (fun s => b ≤ (ball D V s 3).card ∧ Z ⊆ outN D V s ∧ (outN D V s \ Z).card = 1 ∧
    ∀ e ∈ outN D V s \ Z, Z ⊆ outN D V e)

/-- At `b = 28` this is `Supplier54.zSet`. -/
theorem zSetB_28 (D : CH.Digraph) (V Z : Finset ℕ) : zSetB D V Z 28 = Supplier54.zSet D V Z := rfl

/-- **S2 (generic, `6 ≤ q`).** Under `A ≠ ∅`, at least two suppliers, each with `|B_3| ≥ b`
whenever `b ≤ 4 + |Z| + |W| + |J|`. -/
theorem two_suppliers (free : QFree D V q) (hu : u ∈ V) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
    (hY : (layer D V 2 u).card = q + 3) (hZ : (layer D V 3 u).card = q + 2)
    (ne : (aSet D V u).Nonempty) {b : ℕ}
    (hb : b ≤ 4 + (layer D V 3 u).card + (layer D V 4 u).card + (layer D V 5 u).card) :
    2 ≤ (zSetB D V (layer D V 3 u) b).card := by
  refine (good_two free hu hq reg hY hZ ne).trans (card_le_card fun s hs => ?_)
  obtain ⟨full, rest, full'⟩ := good_supplier free hu (by omega) reg hZ hs
  have sA := lone_subset (mem_good.mp hs).1
  refine mem_filter.mpr ⟨aSet_V sA, hb.trans (complete_ball_A free hu (by omega) reg hZ sA full),
    full, ?_, ?_⟩
  · rw [rest, card_singleton]
  · intro e he
    rw [rest, mem_singleton] at he
    rw [he]
    exact full'

/-- **S2 (instance `q = 6`, `r = 9`), with Lemma 5 as `hO`.** -/
theorem two_suppliers_54 (free : QFree D V 6) (hu : u ∈ V) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hY : (layer D V 2 u).card = 9) (hZ : (layer D V 3 u).card = 8)
    (hO : oSet D V u ≠ layer D V 2 u) : 2 ≤ (Supplier54.zSet D V (layer D V 3 u)).card := by
  have ne := a_nonempty hO
  have := wj_sixteen free hu reg hY hZ ne
  rw [← zSetB_28]
  exact two_suppliers free hu le_rfl reg hY hZ ne (by omega)

/-- **S2 in the shape of `Laws54.s2`, with Lemma 5 as the hypothesis `hO`.** -/
theorem s2_of_hO (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (hO : ∀ u ∈ V, (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
      oSet D V u ≠ layer D V 2 u) :
    ∀ u ∈ V, ¬ Thin D V 9 u → (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
      2 ≤ (Supplier54.zSet D V (layer D V 3 u)).card :=
  fun u hu _ hY hZ => two_suppliers_54 free hu reg hY hZ (hO u hu hY hZ)

/-! ### Lemma 5: `O ≠ Y`

Facts B and C are generic in `q`. The case analysis is the instance `q = 6`, `r = 9`.
It differs from the paper's split into "X acyclic" and "X has a shortest cycle"; it splits
on whether some target reaches a sink of `X`:
* `case_reach` (some target reaches a sink): the rows that reach a sink within `k` steps
  (`near k`) grow strictly up to `k = 4`, because a target is not in `near 4`. So every target
  has at most four `X`-heads, all in the at most five rows `M = X \ near 3`. Fact C puts
  `Y = O` inside the union of the omission sets of the targets, and a count of arcs inside
  the targets (`arc_count`, overlaps `bu_one`, `bu_two`) bounds that union by `8`.
* `case_far` (no target reaches a sink): the rows that reach no sink form a closed set of
  minimum out-degree one. A2 (`OneHead.lone_two_six`) gives every target a one-head row within two
  steps, which omits a single label. Fact C then gives every label of `Y` its own one-head
  row, and a target and its head would share one.
-/

/-- **Facts A/B (generic).** A return `y → x`, a walk `x ⇝ c` of length `k`, an arc `c → a` and
a walk `a ⇝ y` of length `s` close a walk of length `k + s + 2`. -/
theorem fact_B {q : ℕ} (free : QFree D V q) {y x c a k s : ℕ} (xV : x ∈ V) (aV : a ∈ V)
    (yx : D y x = true) (wxc : Walk D V x c k) (ca : D c a = true) (way : Walk D V a y s)
    (h : k + s + 2 ≤ q) : False :=
  free x (k + 1 + s + 1) (by omega) (by omega) (((wxc.snoc aV ca).append way).snoc xV yx)

theorem walk_of_fun {W : Finset ℕ} (f : ℕ → ℕ) (i : ℕ) :
    ∀ n, (∀ m < n, f (i + m + 1) ∈ W ∧ D (f (i + m)) (f (i + m + 1)) = true) →
      Walk D W (f i) (f (i + n)) n := by
  intro n
  induction n with
  | zero => intro _; rw [Nat.add_zero]; exact .refl _
  | succ n ih =>
    intro h
    have w := ih (fun m hm => h m (by omega))
    obtain ⟨mem, arc⟩ := h n (by omega)
    rw [show i + (n + 1) = i + n + 1 by omega]
    exact w.snoc mem arc

/-- Labels of `Y` that `c` does not point to. -/
def om (D : CH.Digraph) (Y : Finset ℕ) (c : ℕ) : Finset ℕ := Y.filter (fun a => ¬ D c a = true)

theorem mem_om {Y : Finset ℕ} {c a : ℕ} : a ∈ om D Y c ↔ a ∈ Y ∧ ¬ D c a = true := mem_filter

theorem om_card (Y : Finset ℕ) (c : ℕ) : (outN D Y c).card + (om D Y c).card = Y.card := by
  unfold outN om
  exact card_filter_add_card_filter_not _

/-- **Fact C (generic).** A return `t → x`, a walk `x ⇝ e` of length `j` and
`|omit(e)| ≤ q - 2 - j`: every row of `Y` reaching `t` inside `Y` is omitted by `e`. -/
theorem fact_C {q : ℕ} (free : QFree D V q) {Y : Finset ℕ} (YV : Y ⊆ V) {t x e j : ℕ}
    (xV : x ∈ V) (tx : D t x = true) (wxe : Walk D V x e j)
    (small : (om D Y e).card + j + 2 ≤ q) {a s : ℕ} (aY : a ∈ Y) (way : Walk D Y a t s) :
    a ∈ om D Y e := by
  obtain ⟨f, f0, fs, hf⟩ := way.toFun
  have fY : ∀ i ≤ s, f i ∈ Y := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hp
    · rw [f0]; exact aY
    · have := (hf (i - 1) (by omega)).1
      rwa [show i - 1 + 1 = i by omega] at this
  have near : ∀ i ≤ s, s ≤ i + (q - 2 - j) → f i ∈ om D Y e := by
    intro i hi hd
    have w : Walk D Y (f i) (f (i + (s - i))) (s - i) :=
      walk_of_fun f i (s - i) (fun m hm => hf (i + m) (by omega))
    rw [show i + (s - i) = s by omega, fs] at w
    refine mem_om.mpr ⟨fY i hi, fun arc => ?_⟩
    exact fact_B free xV (YV (fY i hi)) tx wxe arc (w.mono YV) (by omega)
  by_cases hs : s ≤ q - 2 - j
  · have := near 0 (by omega) (by omega)
    rwa [f0] at this
  · exfalso
    have inj : Set.InjOn f (Finset.Icc (s - (q - 2 - j)) s : Set ℕ) := by
      intro i hi i' hi' eq
      simp only [coe_Icc, Set.mem_Icc] at hi hi'
      by_contra ne
      rcases lt_or_gt_of_ne ne with lt | lt
      · have w := walk_of_fun (W := Y) (D := D) f i (i' - i) (fun m hm => hf (i + m) (by omega))
        rw [show i + (i' - i) = i' by omega, ← eq] at w
        exact free _ (i' - i) (by omega) (by omega) (w.mono YV)
      · have w := walk_of_fun (W := Y) (D := D) f i' (i - i') (fun m hm => hf (i' + m) (by omega))
        rw [show i' + (i - i') = i by omega, eq] at w
        exact free _ (i - i') (by omega) (by omega) (w.mono YV)
    have sub : (Finset.Icc (s - (q - 2 - j)) s).image f ⊆ om D Y e := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      rw [mem_Icc] at hi
      exact near i hi.2 (by omega)
    have := card_le_card sub
    rw [card_image_of_injOn inj, Nat.card_Icc] at this
    omega

/-- Arcs inside a `q`-free set (`2 ≤ q`): `2 e + n ≤ n²`. -/
theorem arc_count {q : ℕ} {Q : Finset ℕ} (free : QFree D Q q) (hq : 2 ≤ q) :
    2 * ∑ x ∈ Q, (outN D Q x).card + Q.card ≤ Q.card * Q.card := by
  have led := ReachLedger.ledger (D := D) (V := Q) (q := q) (i := 1) (j := 1) free (by omega)
  have e : ∑ x ∈ Q, (ball D Q x 1).card = ∑ x ∈ Q, (outN D Q x).card + Q.card := by
    rw [sum_congr rfl (fun x hx => ReachLedger.ball_one free (by omega) hx), sum_add_distrib,
      sum_const, smul_eq_mul, mul_one]
  rw [e] at led
  have : Q.card * (Q.card + 1) = Q.card * Q.card + Q.card := by ring
  omega

/-- A label in two of the sets: the union loses one. -/
theorem bu_one {Q : Finset ℕ} {S : ℕ → Finset ℕ} {x1 x2 a : ℕ} (h1 : x1 ∈ Q) (h2 : x2 ∈ Q)
    (ne : x1 ≠ x2) (a1 : a ∈ S x1) (a2 : a ∈ S x2) :
    (Q.biUnion S).card + 1 ≤ ∑ x ∈ Q, (S x).card := by
  have sub : Q.biUnion S ⊆ (Q.erase x2).biUnion S ∪ (S x2).erase a := by
    intro z hz
    obtain ⟨x, hx, zx⟩ := mem_biUnion.mp hz
    by_cases e : x = x2
    · rw [e] at zx
      by_cases za : z = a
      · rw [za]; exact mem_union_left _ (mem_biUnion.mpr ⟨x1, mem_erase.mpr ⟨ne, h1⟩, a1⟩)
      · exact mem_union_right _ (mem_erase.mpr ⟨za, zx⟩)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨x, mem_erase.mpr ⟨e, hx⟩, zx⟩)
  have c1 := card_le_card sub
  have c2 := card_union_le ((Q.erase x2).biUnion S) ((S x2).erase a)
  have c3 := card_biUnion_le (s := Q.erase x2) (t := S)
  have c4 := card_erase_of_mem a2
  have c5 := add_sum_erase Q (fun x => (S x).card) h2
  have pos : 1 ≤ (S x2).card := card_pos.mpr ⟨a, a2⟩
  omega

/-- A label in three of the sets: the union loses two. -/
theorem bu_two {Q : Finset ℕ} {S : ℕ → Finset ℕ} {x0 b1 b2 a : ℕ} (h0 : x0 ∈ Q) (h1 : b1 ∈ Q)
    (h2 : b2 ∈ Q) (n01 : x0 ≠ b1) (n02 : x0 ≠ b2) (n12 : b1 ≠ b2) (a0 : a ∈ S x0)
    (a1 : a ∈ S b1) (a2 : a ∈ S b2) :
    (Q.biUnion S).card + 2 ≤ ∑ x ∈ Q, (S x).card := by
  have sub : Q.biUnion S ⊆ ((Q.erase b1).erase b2).biUnion S ∪ (S b1).erase a ∪ (S b2).erase a := by
    intro z hz
    obtain ⟨x, hx, zx⟩ := mem_biUnion.mp hz
    have za0 : z = a → z ∈ ((Q.erase b1).erase b2).biUnion S := fun e =>
      mem_biUnion.mpr ⟨x0, mem_erase.mpr ⟨n02, mem_erase.mpr ⟨n01, h0⟩⟩, e ▸ a0⟩
    by_cases e1 : x = b1
    · rw [e1] at zx
      by_cases za : z = a
      · exact mem_union_left _ (mem_union_left _ (za0 za))
      · exact mem_union_left _ (mem_union_right _ (mem_erase.mpr ⟨za, zx⟩))
    by_cases e2 : x = b2
    · rw [e2] at zx
      by_cases za : z = a
      · exact mem_union_left _ (mem_union_left _ (za0 za))
      · exact mem_union_right _ (mem_erase.mpr ⟨za, zx⟩)
    exact mem_union_left _ (mem_union_left _
      (mem_biUnion.mpr ⟨x, mem_erase.mpr ⟨e2, mem_erase.mpr ⟨e1, hx⟩⟩, zx⟩))
  have c1 := card_le_card sub
  have c2 := card_union_le (((Q.erase b1).erase b2).biUnion S ∪ (S b1).erase a) ((S b2).erase a)
  have c2' := card_union_le (((Q.erase b1).erase b2).biUnion S) ((S b1).erase a)
  have c3 := card_biUnion_le (s := (Q.erase b1).erase b2) (t := S)
  have c4 := card_erase_of_mem a1
  have c4' := card_erase_of_mem a2
  have c5 := add_sum_erase Q (fun x => (S x).card) h1
  have c6 := add_sum_erase (Q.erase b1) (fun x => (S x).card) (mem_erase.mpr ⟨Ne.symm n12, h2⟩)
  have p1 : 1 ≤ (S b1).card := card_pos.mpr ⟨a, a1⟩
  have p2 : 1 ≤ (S b2).card := card_pos.mpr ⟨a, a2⟩
  omega

/-- Sinks of `X`. -/
def snk (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (outN D V u).filter (fun c => outN D (outN D V u) c = ∅)

/-- Rows of `X` reaching a sink of `X` within `k` steps inside `X`. -/
noncomputable def near (D : CH.Digraph) (V : Finset ℕ) (u k : ℕ) : Finset ℕ := by
  classical
  exact (outN D V u).filter (fun c => ∃ s ∈ snk D V u, s ∈ ball D (outN D V u) c k)

theorem mem_near {k c : ℕ} : c ∈ near D V u k ↔
    c ∈ outN D V u ∧ ∃ s ∈ snk D V u, s ∈ ball D (outN D V u) c k := by
  classical
  unfold near
  exact mem_filter

theorem near_sub {k : ℕ} : near D V u k ⊆ outN D V u := fun _ h => (mem_near.mp h).1

theorem near_mono {k k' : ℕ} (h : k ≤ k') : near D V u k ⊆ near D V u k' := fun c hc => by
  obtain ⟨cX, s, hs, sb⟩ := mem_near.mp hc
  exact mem_near.mpr ⟨cX, s, hs, ball_mono_radius h sb⟩

theorem near_step {k c h : ℕ} (cX : c ∈ outN D V u) (hX : h ∈ outN D V u) (arc : D c h = true)
    (hn : h ∈ near D V u k) : c ∈ near D V u (k + 1) := by
  obtain ⟨-, s, hs, sb⟩ := mem_near.mp hn
  exact mem_near.mpr ⟨cX, s, hs, ReachLedger.ball_succ hX arc sb⟩

theorem near_stable {k : ℕ} (e : near D V u k = near D V u (k + 1)) :
    near D V u (k + 2) ⊆ near D V u (k + 1) := by
  intro c hc
  obtain ⟨cX, s, hs, sb⟩ := mem_near.mp hc
  obtain ⟨sX, j, hj, w⟩ := mem_ball.mp sb
  by_cases hj' : j ≤ k + 1
  · exact mem_near.mpr ⟨cX, s, hs, mem_ball.mpr ⟨sX, j, hj', w⟩⟩
  · obtain rfl : j = k + 2 := by omega
    cases w with
    | step hb hab w' =>
      have bn := mem_near.mpr ⟨hb, s, hs, mem_ball.mpr ⟨sX, k + 1, le_rfl, w'⟩⟩
      rw [← e] at bn
      exact near_step cX hb hab bn

theorem near_flat {k : ℕ} (e : near D V u k = near D V u (k + 1)) :
    ∀ i, near D V u (k + i) ⊆ near D V u k := by
  have step : ∀ i, near D V u (k + i) = near D V u (k + i + 1) := by
    intro i
    induction i with
    | zero => simpa using e
    | succ i ih =>
      apply Subset.antisymm (near_mono (by omega))
      have := near_stable (k := k + i) ih
      rw [show k + (i + 1) + 1 = k + i + 2 by omega, show k + (i + 1) = k + i + 1 by omega]
      exact this
  intro i
  induction i with
  | zero => rw [Nat.add_zero]
  | succ i ih =>
    rw [show k + (i + 1) = k + i + 1 by omega, ← step i]
    exact ih

/-- **The chain.** A row reaching a sink but not within four steps: `|near 3| ≥ 4` and
`near 4 ≠ near 3`. -/
theorem near_chain {x m s0 : ℕ} (s0s : s0 ∈ snk D V u) (sb : s0 ∈ ball D (outN D V u) x m)
    (xX : x ∈ outN D V u) (xn : x ∉ near D V u 4) :
    4 ≤ (near D V u 3).card ∧ (near D V u 4 \ near D V u 3).Nonempty := by
  have strict : ∀ k ≤ 3, near D V u k ⊂ near D V u (k + 1) := by
    intro k hk
    refine ssubset_of_subset_of_ne (near_mono (by omega)) (fun e => xn ?_)
    have xin : x ∈ near D V u (k + m) :=
      mem_near.mpr ⟨xX, s0, s0s, ball_mono_radius (by omega) sb⟩
    exact near_mono (by omega) (near_flat e m xin)
  have s0X := (mem_filter.mp s0s).1
  have n0 : 1 ≤ (near D V u 0).card :=
    card_pos.mpr ⟨s0, mem_near.mpr ⟨s0X, s0, s0s, self_mem_ball s0X⟩⟩
  have c0 : (near D V u 0).card < (near D V u 1).card := card_lt_card (strict 0 (by norm_num))
  have c1 : (near D V u 1).card < (near D V u 2).card := card_lt_card (strict 1 (by norm_num))
  have c2 : (near D V u 2).card < (near D V u 3).card := card_lt_card (strict 2 (by norm_num))
  refine ⟨by omega, ?_⟩
  obtain ⟨z, hz4, hz3⟩ := exists_of_ssubset (strict 3 le_rfl)
  exact ⟨z, mem_sdiff.mpr ⟨hz4, hz3⟩⟩

/-- Targets: rows of `X` with an in-neighbour in `Y`. -/
noncomputable def tgt (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (outN D V u).filter (fun x => ∃ t ∈ layer D V 2 u, D t x = true)

/-- Rows of `X` that reach no sink of `X`. -/
noncomputable def far (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ := by
  classical
  exact (outN D V u).filter (fun c => ¬ ∃ s ∈ snk D V u, ∃ k, s ∈ ball D (outN D V u) c k)

theorem mem_far {c : ℕ} : c ∈ far D V u ↔
    c ∈ outN D V u ∧ ¬ ∃ s ∈ snk D V u, ∃ k, s ∈ ball D (outN D V u) c k := by
  classical
  unfold far
  exact mem_filter

theorem far_sub : far D V u ⊆ outN D V u := fun _ h => (mem_far.mp h).1

theorem far_closed {c h : ℕ} (hc : c ∈ far D V u) (hh : h ∈ outN D (outN D V u) c) :
    h ∈ far D V u := by
  obtain ⟨hX, arc⟩ := mem_outN.mp hh
  refine mem_far.mpr ⟨hX, fun ⟨s, hs, k, sb⟩ => (mem_far.mp hc).2 ⟨s, hs, k + 1, ?_⟩⟩
  exact ReachLedger.ball_succ hX arc sb

theorem far_out {c : ℕ} (hc : c ∈ far D V u) :
    outN D (far D V u) c = outN D (outN D V u) c :=
  Profile54.out_restrict far_sub (fun _ hh => far_closed hc hh)

theorem far_deg {c : ℕ} (hc : c ∈ far D V u) : 1 ≤ (outN D (far D V u) c).card := by
  rw [far_out hc]
  by_contra h
  have e : outN D (outN D V u) c = ∅ := card_eq_zero.mp (by omega)
  have cX := (mem_far.mp hc).1
  exact (mem_far.mp hc).2 ⟨c, mem_filter.mpr ⟨cX, e⟩, 0, self_mem_ball cX⟩

section five
variable (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
  (hY : (layer D V 2 u).card = 9)

include free reg hu hY in
theorem om_le {c : ℕ} (hc : c ∈ outN D V u) :
    (om D (layer D V 2 u) c).card ≤ (outN D (outN D V u) c).card := by
  have := x_split free hu (q := 6) (by norm_num) reg hc
  have := om_card (D := D) (layer D V 2 u) c
  rw [hY] at this
  omega

include free reg hu hY in
/-- A sink of `X` points to all of `Y`. -/
theorem sink_full {s : ℕ} (hs : s ∈ snk D V u) {a : ℕ} (ha : a ∈ layer D V 2 u) :
    D s a = true := by
  obtain ⟨sX, e⟩ := mem_filter.mp hs
  have h1 := om_le free reg hu hY sX
  rw [e, card_empty] at h1
  by_contra h
  have : a ∈ om D (layer D V 2 u) s := mem_om.mpr ⟨ha, h⟩
  have := card_pos.mpr ⟨a, this⟩
  omega

include free reg hu hY in
/-- **Fact A at a sink.** A target is not within four steps of a sink. -/
theorem tgt_not_near {x : ℕ} (hx : x ∈ tgt D V u) : x ∉ near D V u 4 := by
  intro hn
  obtain ⟨xX, t, tY, tx⟩ := mem_filter.mp hx
  obtain ⟨-, s, hs, sb⟩ := mem_near.mp hn
  obtain ⟨-, j, hj, w⟩ := mem_ball.mp sb
  exact fact_B free (outN_subset xX) (layer_subset tY) tx (w.mono outN_subset)
    (sink_full free reg hu hY hs tY) (.refl t) (by omega)

include free reg hu hY in
theorem tgt_heads {x : ℕ} (hx : x ∈ tgt D V u) :
    outN D (outN D V u) x ⊆ (outN D V u \ near D V u 3).erase x := by
  intro h hh
  obtain ⟨hX, xh⟩ := mem_outN.mp hh
  have xX := (mem_filter.mp hx).1
  refine mem_erase.mpr ⟨fun e => ?_, mem_sdiff.mpr ⟨hX, fun hn => tgt_not_near free reg hu hY hx ?_⟩⟩
  · rw [e] at xh
    exact loopfree free (by norm_num) (outN_subset xX) xh
  · exact near_step xX hX xh hn

/-- `O = Y` puts every label of `Y` above a tail with a target. -/
theorem o_cover (hO : oSet D V u = layer D V 2 u) {a : ℕ} (ha : a ∈ layer D V 2 u) :
    ∃ t x j, x ∈ tgt D V u ∧ t ∈ layer D V 2 u ∧ D t x = true ∧ Walk D (layer D V 2 u) a t j := by
  rw [← hO] at ha
  obtain ⟨aY, t, ⟨x, hx, tx⟩, j, w⟩ := mem_oSet.mp ha
  have tY : t ∈ layer D V 2 u := by
    rcases w.end_mem_or with e | h
    · rw [e]; exact aY
    · exact h
  exact ⟨t, x, j, mem_filter.mpr ⟨hx, t, tY, tx⟩, tY, tx, w⟩

include free in
/-- A tail omitted by its target and by every head of its target. -/
theorem tail_om {t x : ℕ} (tY : t ∈ layer D V 2 u) (xV : x ∈ V) (tx : D t x = true) :
    t ∈ om D (layer D V 2 u) x ∧ ∀ h, h ∈ V → D x h = true → t ∈ om D (layer D V 2 u) h := by
  have tV := layer_subset tY
  refine ⟨mem_om.mpr ⟨tY, fun xt => digonfree free (by norm_num) tV xV tx xt⟩,
    fun h hV xh => mem_om.mpr ⟨tY, fun ht => ?_⟩⟩
  exact free t 3 (by norm_num) (by norm_num) (.step xV tx (.step hV xh (.step tV ht (.refl t))))

include free reg hu hY in
/-- **Lemma 5, a target reaches a sink.** -/
theorem case_reach (hO : oSet D V u = layer D V 2 u) {x0 s0 m : ℕ} (hx0 : x0 ∈ tgt D V u)
    (s0s : s0 ∈ snk D V u) (sb : s0 ∈ ball D (outN D V u) x0 m) : False := by
  have XV : outN D V u ⊆ V := outN_subset
  have hXc : (outN D V u).card = 9 := reg u hu
  have QX : tgt D V u ⊆ outN D V u := filter_subset _ _
  obtain ⟨n3, z, hz⟩ := near_chain s0s sb (QX hx0) (tgt_not_near free reg hu hY hx0)
  obtain ⟨hz4, hz3⟩ := mem_sdiff.mp hz
  have QM : tgt D V u ⊆ outN D V u \ near D V u 3 := fun x hx =>
    mem_sdiff.mpr ⟨QX hx, fun h => tgt_not_near free reg hu hY hx (near_mono (by norm_num) h)⟩
  have zMQ : z ∈ (outN D V u \ near D V u 3) \ tgt D V u :=
    mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨near_sub hz4, hz3⟩, fun h => tgt_not_near free reg hu hY h hz4⟩
  have cM : (outN D V u \ near D V u 3).card = (outN D V u).card - (near D V u 3).card :=
    card_sdiff_of_subset near_sub
  have n3X := card_le_card (near_sub (D := D) (V := V) (u := u) (k := 3))
  have cMQ : ((outN D V u \ near D V u 3) \ tgt D V u).card =
      (outN D V u \ near D V u 3).card - (tgt D V u).card := card_sdiff_of_subset QM
  have pos : 1 ≤ ((outN D V u \ near D V u 3) \ tgt D V u).card := card_pos.mpr ⟨z, zMQ⟩
  have qM := card_le_card QM
  -- every target omits at most four labels
  have heads4 : ∀ x ∈ tgt D V u, (outN D (outN D V u) x).card ≤ 4 := by
    intro x hx
    have := card_le_card (tgt_heads free reg hu hY hx)
    rw [card_erase_of_mem (QM hx)] at this
    omega
  have cover : layer D V 2 u ⊆ (tgt D V u).biUnion (om D (layer D V 2 u)) := by
    intro a ha
    obtain ⟨t, x, j, hx, -, tx, w⟩ := o_cover hO ha
    have xX := QX hx
    have small : (om D (layer D V 2 u) x).card + 0 + 2 ≤ 6 := by
      have := om_le free reg hu hY xX
      have := heads4 x hx
      omega
    exact mem_biUnion.mpr ⟨x, hx, fact_C free layer_subset (XV xX) tx (.refl x) small ha w⟩
  have rowb : ∀ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ≤
      (outN D (tgt D V u) x).card + ((outN D V u \ near D V u 3) \ tgt D V u).card := by
    intro x hx
    have h1 := om_le free reg hu hY (QX hx)
    have sub : outN D (outN D V u) x ⊆
        outN D (tgt D V u) x ∪ ((outN D V u \ near D V u 3) \ tgt D V u) := by
      intro h hh
      have hM := mem_of_mem_erase (tgt_heads free reg hu hY hx hh)
      by_cases hq : h ∈ tgt D V u
      · exact mem_union_left _ (mem_outN.mpr ⟨hq, (mem_outN.mp hh).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hM, hq⟩)
    have := (card_le_card sub).trans (card_union_le _ _)
    omega
  have sumb : ∑ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ≤
      ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card +
        (tgt D V u).card * ((outN D V u \ near D V u 3) \ tgt D V u).card := by
    calc _ ≤ ∑ x ∈ tgt D V u, ((outN D (tgt D V u) x).card +
          ((outN D V u \ near D V u 3) \ tgt D V u).card) := sum_le_sum rowb
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have cu := card_le_card cover
  have cb := card_biUnion_le (s := tgt D V u) (t := om D (layer D V 2 u))
  have arc := arc_count (free.mono_set (QX.trans XV)) (by norm_num : 2 ≤ 6)
  -- overlaps
  have excess : ((tgt D V u).biUnion (om D (layer D V 2 u))).card + 2 ≤
        ∑ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ∨
      (((tgt D V u).biUnion (om D (layer D V 2 u))).card + 1 ≤
        ∑ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ∧
        ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card ≤ (tgt D V u).card) ∨
      ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card = 0 := by
    by_cases two : ∃ x ∈ tgt D V u, 2 ≤ (outN D (tgt D V u) x).card
    · obtain ⟨x, hx, h2⟩ := two
      obtain ⟨b1, hb1, b2, hb2, n12⟩ := one_lt_card.mp (show 1 < (outN D (tgt D V u) x).card by omega)
      obtain ⟨b1Q, xb1⟩ := mem_outN.mp hb1
      obtain ⟨b2Q, xb2⟩ := mem_outN.mp hb2
      obtain ⟨xX, t, tY, tx⟩ := mem_filter.mp hx
      have om3 := tail_om free tY (XV xX) tx
      have nb : ∀ b, D x b = true → x ≠ b := fun b xb e => by
        rw [← e] at xb; exact loopfree free (by norm_num) (XV xX) xb
      exact Or.inl (bu_two hx b1Q b2Q (nb b1 xb1) (nb b2 xb2) n12 om3.1
        (om3.2 _ (XV (QX b1Q)) xb1) (om3.2 _ (XV (QX b2Q)) xb2))
    · push Not at two
      have le1 : ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card ≤ (tgt D V u).card := by
        calc _ ≤ ∑ _x ∈ tgt D V u, 1 := sum_le_sum (fun x hx => by have := two x hx; omega)
          _ = _ := by rw [sum_const, smul_eq_mul, mul_one]
      by_cases one : ∃ x ∈ tgt D V u, 1 ≤ (outN D (tgt D V u) x).card
      · obtain ⟨x, hx, h1⟩ := one
        obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (outN D (tgt D V u) x).card by omega)
        obtain ⟨bQ, xb⟩ := mem_outN.mp hb
        obtain ⟨xX, t, tY, tx⟩ := mem_filter.mp hx
        have om3 := tail_om free tY (XV xX) tx
        have nb : x ≠ b := fun e => by
          rw [← e] at xb; exact loopfree free (by norm_num) (XV xX) xb
        exact Or.inr (Or.inl ⟨bu_one hx bQ nb om3.1 (om3.2 _ (XV (QX bQ)) xb), le1⟩)
      · push Not at one
        refine Or.inr (Or.inr (sum_eq_zero (fun x hx => by have := one x hx; omega)))
  rw [hY] at cu
  obtain ⟨k, hk⟩ : ∃ k, (tgt D V u).card = k := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card = E := ⟨_, rfl⟩
  obtain ⟨mq, hmq⟩ : ∃ mq, ((outN D V u \ near D V u 3) \ tgt D V u).card = mq := ⟨_, rfl⟩
  rw [hk, hE, hmq] at sumb
  rw [hk, hE] at arc
  rw [hE, hk] at excess
  rw [hmq] at pos cMQ
  rw [hk] at cMQ qM
  have hk4 : k ≤ 4 := by omega
  interval_cases k <;> omega

include free reg hu hY in
/-- **Lemma 5, no target reaches a sink.** -/
theorem case_far (hO : oSet D V u = layer D V 2 u)
    (hnone : ¬ ∃ x ∈ tgt D V u, ∃ s ∈ snk D V u, ∃ k, s ∈ ball D (outN D V u) x k) : False := by
  have XV : outN D V u ⊆ V := outN_subset
  have hXc : (outN D V u).card = 9 := reg u hu
  have RX : far D V u ⊆ outN D V u := far_sub
  have frR : QFree D (far D V u) 6 := free.mono_set (RX.trans XV)
  have degR : ∀ c ∈ far D V u, 1 ≤ (outN D (far D V u) c).card := fun c hc => far_deg hc
  have RC := card_le_card RX
  have QX : tgt D V u ⊆ outN D V u := filter_subset _ _
  have tgtR : ∀ x ∈ tgt D V u, x ∈ far D V u := fun x hx =>
    mem_far.mpr ⟨QX hx, fun ⟨s, hs, k, sb⟩ => hnone ⟨x, hx, s, hs, k, sb⟩⟩
  have om1 : ∀ e ∈ lone D (far D V u), (om D (layer D V 2 u) e).card ≤ 1 := by
    intro e he
    have eR := lone_subset he
    have := om_le free reg hu hY (RX eR)
    rw [← far_out eR] at this
    have := (mem_lone.mp he).2
    omega
  have cover : layer D V 2 u ⊆ (lone D (far D V u)).biUnion (om D (layer D V 2 u)) := by
    intro a ha
    obtain ⟨t, x, j, hx, -, tx, w⟩ := o_cover hO ha
    obtain ⟨e, eb, el⟩ := lone_two_six frR degR (by omega) (tgtR x hx)
    obtain ⟨-, i, hi, we⟩ := mem_ball.mp eb
    have small : (om D (layer D V 2 u) e).card + i + 2 ≤ 6 := by
      have := om1 e el
      omega
    exact mem_biUnion.mpr ⟨e, el, fact_C free layer_subset (XV (QX hx)) tx
      (we.mono (RX.trans XV)) small ha w⟩
  have sumle : ∑ e ∈ lone D (far D V u), (om D (layer D V 2 u) e).card ≤
      (lone D (far D V u)).card := by
    calc _ ≤ ∑ _e ∈ lone D (far D V u), 1 := sum_le_sum om1
      _ = _ := by rw [sum_const, smul_eq_mul, mul_one]
  have cu := card_le_card cover
  have cb := card_biUnion_le (s := lone D (far D V u)) (t := om D (layer D V 2 u))
  have LR := card_le_card (lone_subset (D := D) (S := far D V u))
  rw [hY] at cu
  by_cases full : (lone D (far D V u)).card = 9
  · have LX : lone D (far D V u) = outN D V u :=
      eq_of_subset_of_card_le (lone_subset.trans RX) (by omega)
    obtain ⟨a, ha⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
    obtain ⟨t, x, j, hx, tY, tx, -⟩ := o_cover hO ha
    have xL : x ∈ lone D (far D V u) := by rw [LX]; exact QX hx
    obtain ⟨hR, xh⟩ := hd_mem degR xL
    have hL : hd D (far D V u) x ∈ lone D (far D V u) := by rw [LX]; exact RX hR
    have om3 := tail_om free tY (XV (QX hx)) tx
    have nb : x ≠ hd D (far D V u) x := fun e => by
      rw [← e] at xh; exact loopfree free (by norm_num) (XV (QX hx)) xh
    have := bu_one xL hL nb om3.1 (om3.2 _ (XV (RX hR)) xh)
    omega
  · omega

include free reg hu hY in
/-- **Lemma 5 (instance `q = 6`, `r = 9`, `|Y| = 9`).** Some row of `Y` reaches no tail
inside `Y`. -/
theorem lemma5 : oSet D V u ≠ layer D V 2 u := by
  intro hO
  by_cases h : ∃ x ∈ tgt D V u, ∃ s ∈ snk D V u, ∃ k, s ∈ ball D (outN D V u) x k
  · obtain ⟨x, hx, s, hs, k, sb⟩ := h
    exact case_reach free reg hu hY hO hx hs sb
  · exact case_far free reg hu hY hO h

end five

/-- **S2, unconditional (instance `q = 6`, `r = 9`), in the shape of `Laws54.s2`.** -/
theorem s2 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    ∀ u ∈ V, ¬ Thin D V 9 u → (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
      2 ≤ (Supplier54.zSet D V (layer D V 3 u)).card :=
  s2_of_hO free reg (fun _ hu hY _ => lemma5 free reg hu hY)

#print axioms a_counts
#print axioms good_two
#print axioms good_supplier
#print axioms low_near
#print axioms x_meet
#print axioms no_return
#print axioms w_big
#print axioms complete_ball_A
#print axioms wj_sixteen
#print axioms two_suppliers
#print axioms two_suppliers_54
#print axioms s2_of_hO
#print axioms fact_B
#print axioms fact_C
#print axioms case_reach
#print axioms case_far
#print axioms lemma5
#print axioms s2

end LeanCH.BR.SupplierFat54
