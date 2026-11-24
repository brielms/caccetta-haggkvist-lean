import checkpoints.shen_extension.SinkDepthReturn

/-!
# A layer of width `r + 1` between a layer of width `r` and a short layer

Three consecutive layers `X`, `Y`, `Z` of a `q`-free graph with
`|X| = r`, `|Y| = r + 1`, `|Z| + 1 ≤ r`, `3 ≤ r` and `r + 1 ≤ q`: the rows of
`X` and `Y` have out-degree at least `r`, the heads of an `X` row lie in
`X ∪ Y` and the heads of a `Y` row lie in `X ∪ Y ∪ Z`. This is impossible
(`wide_layer_false`).

The proof is about sinks. Each `X`-sink omits at most one label of `Y`, and
every `Y`-sink must return into `X` because `Z` is too small.

* With two `X`-sinks, every row of `X` reaches a sink within `r - 2` steps,
  so the return tails have no `Y`-parent. Then `Y` has no internal arc, and
  its `r + 1` rows return injectively into the `r` rows of `X`.
* With one `X`-sink `a`, the tails all equal the label `y₀` that `a` omits.
  So `y₀` is the only `Y`-sink, and `a` heads a `Y`-parent of `y₀`. A return
  target is then `(r - 1)`-deep, so it has at least `r - 1 ≥ 2` heads in `Y`.
  One of them reaches `y₀` within `r - 1` steps, closing a walk of length at
  most `r + 1`.

Both bounds `3 ≤ r` and `r + 1 ≤ q` are needed: a SAT check finds a model at
`r = 2, q = 3, |Z| = 1`, and with `q = r` at `|Z| = r - 1` for `r = 3, 4, 5`.
-/

namespace LeanCH.BR.WideLayerReturn
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn

/-- (a) A sink of `X` whose heads lie in `X ∪ Y`, with at least `|Y| - 1` heads,
omits at most one label of `Y`. -/
theorem sink_omits {D : CH.Digraph} {V X Y : Finset ℕ} {s r : ℕ}
    (heads : outN D V s ⊆ X ∪ Y) (sink : Sink D X s) (deg : r ≤ (outN D V s).card)
    (cy : Y.card = r + 1) : (Y \ outN D V s).card ≤ 1 := by
  have sub : outN D V s ⊆ Y := by
    intro z hz
    rcases mem_union.mp (heads hz) with zx | zy
    · exact (sink z zx (mem_outN.mp hz).2).elim
    · exact zy
  rw [card_sdiff_of_subset sub]
  omega

/-- (b) A sink of `Y` whose heads lie in `X ∪ Y ∪ Z`, with `|Z| < r ≤` its degree,
has a head in `X`. -/
theorem sink_returns {D : CH.Digraph} {V X Y Z : Finset ℕ} {y r : ℕ}
    (heads : outN D V y ⊆ X ∪ Y ∪ Z) (sink : Sink D Y y) (deg : r ≤ (outN D V y).card)
    (cz : Z.card + 1 ≤ r) : ∃ x ∈ X, D y x = true := by
  by_contra! none
  have sub : outN D V y ⊆ Z := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (heads hz) with zxy | zz
    · rcases mem_union.mp zxy with zx | zy
      · exact (none z zx arc).elim
      · exact (sink z zy arc).elim
    · exact zz
  have := card_le_card sub
  omega

/-- A walk inside `Y` between distinct rows ends with an arc from a row of `Y`. -/
theorem last_parent {D : CH.Digraph} {Y : Finset ℕ} {b t k : ℕ} (bm : b ∈ Y)
    (walk : Walk D Y b t k) (ne : b ≠ t) : ∃ p ∈ Y, D p t = true := by
  cases k with
  | zero => cases walk; exact (ne rfl).elim
  | succ k =>
    obtain ⟨p, init, _, arc⟩ := walk.unsnoc
    exact ⟨p, init.end_mem_or.elim (fun e => e ▸ bm) id, arc⟩

/-- With two distinct sinks, every row of an acyclic `X` reaches a sink within
`|X| - 2` steps: a shortest sink path of length `|X| - 1` would cover `X`, and
only its last row is a sink. -/
theorem short_sink {D : CH.Digraph} {X : Finset ℕ} {q s₁ s₂ x : ℕ} (free : QFree D X q)
    (size : X.card ≤ q) (m₁ : s₁ ∈ X) (m₂ : s₂ ∈ X) (ne : s₁ ≠ s₂)
    (k₁ : Sink D X s₁) (k₂ : Sink D X s₂) (xm : x ∈ X) :
    ∃ s ∈ X, Sink D X s ∧ ∃ k, k + 2 ≤ X.card ∧ Walk D X x s k := by
  classical
  obtain ⟨p⟩ := exists_shortest_sink_path free size xm
  have walk := p.walk (Nat.zero_le _) le_rfl
  simp only [p.start, Nat.sub_zero] at walk
  by_cases short : p.len + 2 ≤ X.card
  · exact ⟨_, p.mem _ le_rfl, fun z zm => p.sink z zm, _, short, walk⟩
  exfalso
  have bound := p.bounded
  let S := (range (p.len + 1)).image p.vertex
  have sub : S ⊆ X := by
    intro a am
    obtain ⟨i, im, rfl⟩ := mem_image.mp am
    exact p.mem _ (by have := mem_range.mp im; omega)
  have card : S.card = X.card := by
    rw [card_image_of_injOn (p.injective free size), card_range]
    omega
  have eq := eq_of_subset_of_card_le sub card.ge
  have last (s) (sm : s ∈ X) (stop : Sink D X s) : s = p.vertex p.len := by
    rw [← eq] at sm
    obtain ⟨i, im, rfl⟩ := mem_image.mp sm
    have il := mem_range.mp im
    by_contra other
    have lt : i < p.len := by
      rcases Nat.lt_or_ge i p.len with h | h
      · exact h
      · exact (other (by rw [show i = p.len by omega])).elim
    exact stop _ (p.mem _ (by omega)) (p.edge i lt)
  exact ne ((last _ m₁ k₁).trans (last _ m₂ k₂).symm)

/-- Two consecutive layers of widths `r` and `r + 1`: the rows of `X` keep their
heads in `X ∪ Y`, and every sink of `Y` returns into `X`. -/
structure Wide (D : CH.Digraph) (V X Y : Finset ℕ) (q r : ℕ) : Prop where
  free : QFree D V q
  xv : X ⊆ V
  yv : Y ⊆ V
  cx : X.card = r
  cy : Y.card = r + 1
  time : r + 1 ≤ q
  degX : ∀ x ∈ X, r ≤ (outN D V x).card
  headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y
  returnsY : ∀ y ∈ Y, Sink D Y y → ∃ x ∈ X, D y x = true

/-- A return `y → x` forbids `s ↦ y` when `x` reaches `s` within `k` steps and `k + 2 ≤ q`. -/
theorem omitted_tail {D : CH.Digraph} {V X Y : Finset ℕ} {q r x y s k : ℕ}
    (w : Wide D V X Y q r) (xm : x ∈ X) (ym : y ∈ Y) (ret : D y x = true)
    (walk : Walk D X x s k) (time : k + 2 ≤ q) : y ∉ outN D V s := by
  intro hp
  exact w.free x _ (by omega) (by omega)
    (((walk.mono w.xv).snoc (w.yv ym) (mem_outN.mp hp).2).snoc (w.xv xm) ret)

/-- A return `y → x` forbids `s ↦ p` for a parent `p → y` when `x` reaches `s`
within `k` steps and `k + 3 ≤ q`. -/
theorem omitted_parent {D : CH.Digraph} {V X Y : Finset ℕ} {q r x y s k p : ℕ}
    (w : Wide D V X Y q r) (xm : x ∈ X) (ym : y ∈ Y) (ret : D y x = true)
    (walk : Walk D X x s k) (time : k + 3 ≤ q) (pm : p ∈ Y) (py : D p y = true) :
    p ∉ outN D V s := by
  intro hp
  exact w.free x _ (by omega) (by omega)
    ((((walk.mono w.xv).snoc (w.yv pm) (mem_outN.mp hp).2).snoc (w.yv ym) py).snoc (w.xv xm) ret)

/-- (c) Two distinct `X`-sinks are impossible. -/
theorem two_sinks_false {D : CH.Digraph} {V X Y : Finset ℕ} {q r s₁ s₂ : ℕ}
    (w : Wide D V X Y q r) (m₁ : s₁ ∈ X) (m₂ : s₂ ∈ X) (ne : s₁ ≠ s₂)
    (k₁ : Sink D X s₁) (k₂ : Sink D X s₂) : False := by
  classical
  have fx := w.free.mono_set w.xv
  have fy := w.free.mono_set w.yv
  have sx : X.card ≤ q := by have := w.cx; have := w.time; omega
  have sy : Y.card ≤ q := by have := w.cy; have := w.time; omega
  -- every return target has a short sink omitting the tail and all its parents
  have hit (x) (xm : x ∈ X) :
      ∃ s ∈ X, (Y \ outN D V s).card ≤ 1 ∧ ∀ y ∈ Y, D y x = true →
        y ∉ outN D V s ∧ ∀ p ∈ Y, D p y = true → p ∉ outN D V s := by
    obtain ⟨s, sm, stop, k, kl, walk⟩ := short_sink fx sx m₁ m₂ ne k₁ k₂ xm
    have time : k + 3 ≤ q := by have := w.cx; have := w.time; omega
    exact ⟨s, sm, sink_omits (w.headsX s sm) stop (w.degX s sm) w.cy, fun y ym ret =>
      ⟨omitted_tail w xm ym ret walk (by omega),
        fun p pm py => omitted_parent w xm ym ret walk time pm py⟩⟩
  have orphan (x) (xm : x ∈ X) (y) (ym : y ∈ Y) (ret : D y x = true) (p) (pm : p ∈ Y)
      (py : D p y = true) : False := by
    obtain ⟨s, _, one, miss⟩ := hit x xm
    have eq := card_le_one.mp one y (mem_sdiff.mpr ⟨ym, (miss y ym ret).1⟩) p
      (mem_sdiff.mpr ⟨pm, (miss y ym ret).2 p pm py⟩)
    subst eq
    exact loopfree w.free (by have := w.time; omega) (w.yv ym) py
  -- so `Y` has no internal arc
  have flat (a) (am : a ∈ Y) (b) (bm : b ∈ Y) : D a b ≠ true := by
    intro ab
    obtain ⟨t, tm, stop, m, _, walk⟩ := reach_sink_of_card fy sy bm
    obtain ⟨x, xm, ret⟩ := w.returnsY t tm (fun z zm => stop z zm)
    have long : Walk D Y a t (m + 1) := .step bm ab walk
    obtain ⟨p, init, _, pt⟩ := long.unsnoc
    exact orphan x xm t tm ret p (init.end_mem_or.elim (fun e => e ▸ am) id) pt
  -- every row of `Y` returns, and two of them share a target
  have back (y) (ym : y ∈ Y) : ∃ x ∈ X, D y x = true :=
    w.returnsY y ym (fun z zm => flat y ym z zm)
  let f := fun y => if h : ∃ x ∈ X, D y x = true then h.choose else 0
  have fm (y) (ym : y ∈ Y) : f y ∈ X ∧ D y (f y) = true := by
    have h := back y ym
    simp only [f, h, dite_true]
    exact h.choose_spec
  obtain ⟨y₁, h₁, y₂, h₂, ne', same⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (show X.card < Y.card by rw [w.cx, w.cy]; omega) (fun y ym => (fm y ym).1)
  obtain ⟨s, _, one, miss⟩ := hit (f y₁) (fm y₁ h₁).1
  exact ne' (card_le_one.mp one y₁ (mem_sdiff.mpr ⟨h₁, (miss y₁ h₁ (fm y₁ h₁).2).1⟩) y₂
    (mem_sdiff.mpr ⟨h₂, (miss y₂ h₂ (same ▸ (fm y₂ h₂).2)).1⟩))

/-- (d) A unique `X`-sink is impossible when `3 ≤ r`. -/
theorem one_sink_false {D : CH.Digraph} {V X Y : Finset ℕ} {q r a : ℕ}
    (w : Wide D V X Y q r) (three : 3 ≤ r) (am : a ∈ X) (ka : Sink D X a)
    (only : ∀ s ∈ X, Sink D X s → s = a) : False := by
  classical
  have fx := w.free.mono_set w.xv
  have fy := w.free.mono_set w.yv
  have sx : X.card ≤ q := by have := w.cx; have := w.time; omega
  have sy : Y.card ≤ q := by have := w.cy; have := w.time; omega
  have one := sink_omits (w.headsX a am) ka (w.degX a am) w.cy
  -- every return tail is the label that `a` omits
  have tail (x) (xm : x ∈ X) (y) (ym : y ∈ Y) (ret : D y x = true) : y ∉ outN D V a := by
    obtain ⟨t, tm, stop, k, kl, walk⟩ := reach_sink_of_card fx sx xm
    have ta := only t tm (fun z zm => stop z zm)
    subst ta
    exact omitted_tail w xm ym ret walk (by have := w.cx; have := w.time; omega)
  -- the unique `Y`-sink
  obtain ⟨y₀, y₀m, stop₀⟩ := exists_sink fy (card_pos.mp (by rw [w.cy]; omega)) sy
  have k₀ : Sink D Y y₀ := fun z zm => stop₀ z zm
  obtain ⟨x₀, x₀m, ret₀⟩ := w.returnsY y₀ y₀m k₀
  have miss₀ := tail x₀ x₀m y₀ y₀m ret₀
  have unique (t) (tm : t ∈ Y) (kt : Sink D Y t) : t = y₀ := by
    obtain ⟨x, xm, ret⟩ := w.returnsY t tm kt
    exact card_le_one.mp one t (mem_sdiff.mpr ⟨tm, tail x xm t tm ret⟩) y₀
      (mem_sdiff.mpr ⟨y₀m, miss₀⟩)
  -- `y₀` has a parent `p` in `Y`, and `a` heads `p`
  obtain ⟨b, bm, bne⟩ := exists_mem_ne (show 1 < Y.card by rw [w.cy]; omega) y₀
  obtain ⟨t, tm, stopt, m, _, walkb⟩ := reach_sink_of_card fy sy bm
  have tt := unique t tm (fun z zm => stopt z zm)
  subst tt
  obtain ⟨p, pm, py⟩ := last_parent bm walkb bne
  have pa : p ∈ outN D V a := by
    by_contra pn
    have eq := card_le_one.mp one p (mem_sdiff.mpr ⟨pm, pn⟩) t (mem_sdiff.mpr ⟨tm, miss₀⟩)
    subst eq
    exact loopfree w.free (by have := w.time; omega) (w.yv pm) py
  -- so the return target `x₀` is `(r-1)`-deep in `X`
  have deep : Deep D X (r - 1) x₀ := by
    intro s sm ks k walk
    have sa := only s sm ks
    subst sa
    by_contra! short
    have loop := (((walk.mono w.xv).snoc (w.yv pm) (mem_outN.mp pa).2).snoc (w.yv tm) py).snoc
      (w.xv x₀m) ret₀
    exact w.free x₀ _ (by omega) (by have := w.cx; have := w.time; omega) loop
  have inner := deep_heads fx sx x₀m deep
  -- hence `x₀` has at least two heads in `Y`
  have split : outN D V x₀ ⊆ outN D X x₀ ∪ outN D Y x₀ := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (w.headsX x₀ x₀m hz) with zx | zy
    · exact mem_union_left _ (mem_outN.mpr ⟨zx, arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨zy, arc⟩)
  have heads := (card_le_card split).trans (card_union_le _ _)
  have degx := w.degX x₀ x₀m
  have two : 1 < (outN D Y x₀).card := by rw [w.cx] at inner; omega
  obtain ⟨h₁, hm₁, h₂, hm₂, hne⟩ := one_lt_card.mp two
  -- at most one row of `Y` is `r`-deep, so one of the two heads reaches `y₀` in under `r`
  have close (h) (hm : h ∈ outN D Y x₀) (shallow : ¬Deep D Y r h) : False := by
    simp only [Deep, not_forall, not_le, exists_prop] at shallow
    obtain ⟨s, sm, ks, k, walk, lt⟩ := shallow
    have st := unique s sm ks
    subst st
    have hY := (mem_outN.mp hm).1
    have loop := (Walk.step (w.yv hY) (mem_outN.mp hm).2 (walk.mono w.yv)).snoc (w.xv x₀m) ret₀
    exact w.free x₀ _ (by omega) (by have := w.time; omega) loop
  rcases deep_card (t := r) fy sy with bound | empty
  · by_cases d₁ : Deep D Y r h₁
    · by_cases d₂ : Deep D Y r h₂
      · have both : ({h₁, h₂} : Finset ℕ) ⊆ Y.filter (Deep D Y r) := by
          intro z hz
          rcases mem_insert.mp hz with rfl | hz
          · exact mem_filter.mpr ⟨(mem_outN.mp hm₁).1, d₁⟩
          · rw [mem_singleton.mp hz]; exact mem_filter.mpr ⟨(mem_outN.mp hm₂).1, d₂⟩
        have := card_le_card both
        rw [card_pair hne] at this
        have := w.cy
        omega
      · exact close h₂ hm₂ d₂
    · exact close h₁ hm₁ d₁
  · by_cases d₁ : Deep D Y r h₁
    · have : h₁ ∈ Y.filter (Deep D Y r) := mem_filter.mpr ⟨(mem_outN.mp hm₁).1, d₁⟩
      rw [empty] at this
      exact (notMem_empty _ this)
    · exact close h₁ hm₁ d₁

/-- **Wide layer, core.** Layers of widths `r` and `r + 1` in which every `Y`-sink
returns into `X`, with `3 ≤ r` and `r + 1 ≤ q`, are impossible. -/
theorem wide_false {D : CH.Digraph} {V X Y : Finset ℕ} {q r : ℕ}
    (w : Wide D V X Y q r) (three : 3 ≤ r) : False := by
  have fx := w.free.mono_set w.xv
  have sx : X.card ≤ q := by have := w.cx; have := w.time; omega
  obtain ⟨a, am, stop⟩ := exists_sink fx (card_pos.mp (by rw [w.cx]; omega)) sx
  have ka : Sink D X a := fun z zm => stop z zm
  by_cases two : ∃ s ∈ X, Sink D X s ∧ s ≠ a
  · obtain ⟨s, sm, ks, ne⟩ := two
    exact two_sinks_false w sm am ne ks ka
  · push Not at two
    exact one_sink_false w three am ka two

#print axioms wide_false

/-- **Wide layer.** Layers of widths `r`, `r + 1` and at most `r - 1`, with `3 ≤ r`
and `r + 1 ≤ q`, cannot follow one another in a `q`-free graph when the rows of
`X` and `Y` have out-degree at least `r`, `X` rows head only `X ∪ Y` and `Y` rows
head only `X ∪ Y ∪ Z`. -/
theorem wide_layer_false {D : CH.Digraph} {V X Y Z : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V) (cx : X.card = r) (cy : Y.card = r + 1)
    (cz : Z.card + 1 ≤ r) (three : 3 ≤ r) (time : r + 1 ≤ q)
    (degX : ∀ x ∈ X, r ≤ (outN D V x).card) (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y) (headsY : ∀ y ∈ Y, outN D V y ⊆ X ∪ Y ∪ Z) :
    False :=
  wide_false ⟨free, xv, yv, cx, cy, time, degX, headsX,
    fun y ym stop => sink_returns (headsY y ym) stop (degY y ym) cz⟩ three

#print axioms wide_layer_false
#print axioms one_sink_false
#print axioms omitted_tail
#print axioms omitted_parent
#print axioms two_sinks_false
#print axioms sink_omits
#print axioms sink_returns
#print axioms last_parent
#print axioms short_sink
/-- **A full layer in front.** Layers `W`, `X`, `Y`, `Z` of widths `r`, `r`, `r + 1`
and at most `r - 2`, with `3 ≤ r` and `r + 1 ≤ q`. Rows of each layer head only
their own and earlier layers and the next one, and every row of `Y` has a parent in
`X`. Then `W`-sinks head all of `X`, so `X` cannot return into `W`, and returns from
`Y` into `W` all land on the single possible `(q-2)`-deep row of `W`. Hence every
`Y`-sink still has a head in `X`, and `wide_false` applies to `X`, `Y`. -/
theorem full_front_false {D : CH.Digraph} {V W X Y Z : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (wv : W ⊆ V) (xv : X ⊆ V) (yv : Y ⊆ V)
    (cw : W.card = r) (cx : X.card = r) (cy : Y.card = r + 1) (cz : Z.card + 2 ≤ r)
    (three : 3 ≤ r) (time : r + 1 ≤ q)
    (degW : ∀ a ∈ W, r ≤ (outN D V a).card) (degX : ∀ x ∈ X, r ≤ (outN D V x).card)
    (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (headsW : ∀ a ∈ W, outN D V a ⊆ W ∪ X) (headsX : ∀ x ∈ X, outN D V x ⊆ W ∪ X ∪ Y)
    (headsY : ∀ y ∈ Y, outN D V y ⊆ W ∪ X ∪ Y ∪ Z)
    (parentY : ∀ y ∈ Y, ∃ p ∈ X, D p y = true) : False := by
  classical
  have fw := free.mono_set wv
  have sw : W.card ≤ q := by omega
  -- (i) every `W`-sink heads all of `X`
  have full (a) (am : a ∈ W) (ka : Sink D W a) : X ⊆ outN D V a := by
    have sub : outN D V a ⊆ X := by
      intro z hz
      rcases mem_union.mp (headsW a am hz) with zw | zx
      · exact (ka z zw (mem_outN.mp hz).2).elim
      · exact zx
    exact (eq_of_subset_of_card_le sub (by rw [cx]; exact degW a am)).symm.subset
  -- every row of `W` has a sink walk shorter than `r`
  have shallow (a) (am : a ∈ W) (t) (deep : Deep D W t a) : t < r := by
    obtain ⟨s, sm, stop, m, ml, walk⟩ := reach_sink_of_card fw sw am
    have := deep s sm (fun z zm => stop z zm) m walk
    omega
  -- (ii) `X` does not return into `W`
  have headsX' (x) (xm : x ∈ X) : outN D V x ⊆ X ∪ Y := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsX x xm hz) with zwx | zy
    · rcases mem_union.mp zwx with zw | zx
      · have deep := return_deep_next (l := 0) free wv xv zw full xm (.refl x) arc
        have := shallow z zw _ deep
        omega
      · exact mem_union_left _ zx
    · exact mem_union_right _ zy
  -- (iii) a return from `Y` into `W` lands on a `(q-2)`-deep row; there is at most one
  have deepTarget (y) (ym : y ∈ Y) (a) (am : a ∈ W) (arc : D y a = true) :
      a ∈ W.filter (Deep D W (q - 2)) := by
    obtain ⟨p, pm, py⟩ := parentY y ym
    refine mem_filter.mpr ⟨am, return_deep free wv am (fun s sm ks => ?_) arc⟩
    exact Walk.step (xv pm) (mem_outN.mp (full s sm ks pm)).2 (Walk.step (yv ym) py (.refl y))
  have fewDeep : (W.filter (Deep D W (q - 2))).card ≤ 1 := by
    rcases deep_card (t := q - 2) fw sw with bound | empty
    · omega
    · rw [empty]; simp
  -- (iv) so every `Y`-sink still has a head in `X`
  have returnsY (y) (ym : y ∈ Y) (ky : Sink D Y y) : ∃ x ∈ X, D y x = true := by
    by_contra! none
    have sub : outN D V y ⊆ W.filter (Deep D W (q - 2)) ∪ Z := by
      intro z hz
      have arc := (mem_outN.mp hz).2
      rcases mem_union.mp (headsY y ym hz) with zwxy | zz
      · rcases mem_union.mp zwxy with zwx | zy
        · rcases mem_union.mp zwx with zw | zx
          · exact mem_union_left _ (deepTarget y ym z zw arc)
          · exact (none z zx arc).elim
        · exact (ky z zy arc).elim
      · exact mem_union_right _ zz
    have := (card_le_card sub).trans (card_union_le _ _)
    have := degY y ym
    omega
  exact wide_false ⟨free, xv, yv, cx, cy, time, degX, headsX', returnsY⟩ three

#print axioms full_front_false
/-- A row of an acyclic `W` at depth `|W| - 1` has a shortest sink path that covers `W`. -/
theorem path_cover {D : CH.Digraph} {W : Finset ℕ} {q w : ℕ} (free : QFree D W q)
    (size : W.card ≤ q) (p : ShortestSinkPath D W w) (long : W.card ≤ p.len + 1) :
    ∀ z ∈ W, ∃ i ≤ p.len, p.vertex i = z := by
  classical
  have sub : (range (p.len + 1)).image p.vertex ⊆ W := by
    intro a am
    obtain ⟨i, im, rfl⟩ := mem_image.mp am
    exact p.mem _ (by have := mem_range.mp im; omega)
  have card : ((range (p.len + 1)).image p.vertex).card = p.len + 1 := by
    rw [card_image_of_injOn (p.injective free size), card_range]
  have eq := eq_of_subset_of_card_le sub (by omega)
  intro z zm
  rw [← eq] at zm
  obtain ⟨i, im, rfl⟩ := mem_image.mp zm
  exact ⟨i, by have := mem_range.mp im; omega, rfl⟩

/-- **A full layer in front, tight.** As `full_front_false`, but with `|Z| ≤ r - 1`.
A `Y`-sink without a head in `X` returns to the deepest row of `W`; this forces
`W` to be an induced path, a unique `X`-parent `p₀` of that sink, and either a
four-cycle through `p₀` or a closed walk of length at most `r + 1` through the
unique sink of `Y \ {t}`. -/
theorem full_front_tight_false {D : CH.Digraph} {V W X Y Z : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (wv : W ⊆ V) (xv : X ⊆ V) (yv : Y ⊆ V)
    (cw : W.card = r) (cx : X.card = r) (cy : Y.card = r + 1) (cz : Z.card + 1 ≤ r)
    (three : 3 ≤ r) (time : r + 1 ≤ q)
    (degW : ∀ a ∈ W, r ≤ (outN D V a).card) (degX : ∀ x ∈ X, r ≤ (outN D V x).card)
    (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (headsW : ∀ a ∈ W, outN D V a ⊆ W ∪ X) (headsX : ∀ x ∈ X, outN D V x ⊆ W ∪ X ∪ Y)
    (headsY : ∀ y ∈ Y, outN D V y ⊆ W ∪ X ∪ Y ∪ Z)
    (parentY : ∀ y ∈ Y, ∃ p ∈ X, D p y = true) : False := by
  classical
  have fw := free.mono_set wv
  have fx := free.mono_set xv
  have fy := free.mono_set yv
  have sw : W.card ≤ q := by omega
  have sx : X.card ≤ q := by omega
  have q1 : 1 ≤ q := by omega
  -- every `W`-sink heads all of `X`
  have full (a) (am : a ∈ W) (ka : Sink D W a) : X ⊆ outN D V a := by
    have sub : outN D V a ⊆ X := by
      intro z hz
      rcases mem_union.mp (headsW a am hz) with zw | zx
      · exact (ka z zw (mem_outN.mp hz).2).elim
      · exact zx
    exact (eq_of_subset_of_card_le sub (by rw [cx]; exact degW a am)).symm.subset
  -- `X` does not return into `W`
  have headsX' (x) (xm : x ∈ X) : outN D V x ⊆ X ∪ Y := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsX x xm hz) with zwx | zy
    · rcases mem_union.mp zwx with zw | zx
      · have deep := return_deep_next (l := 0) free wv xv zw full xm (.refl x) arc
        obtain ⟨s, sm, stop, m, ml, walk⟩ := reach_sink_of_card fw sw zw
        have := deep s sm (fun z zm => stop z zm) m walk
        omega
      · exact mem_union_left _ zx
    · exact mem_union_right _ zy
  -- an `X`-sink heads only `Y`
  have sinkY (σ) (σm : σ ∈ X) (kσ : Sink D X σ) : outN D V σ ⊆ Y := by
    intro z hz
    rcases mem_union.mp (headsX' σ σm hz) with zx | zy
    · exact (kσ z zx (mem_outN.mp hz).2).elim
    · exact zy
  by_cases good : ∀ y ∈ Y, Sink D Y y → ∃ x ∈ X, D y x = true
  · exact wide_false ⟨free, xv, yv, cx, cy, time, degX, headsX', good⟩ three
  push Not at good
  obtain ⟨t, tm, kt, noX⟩ := good
  -- `t` returns into `W`
  obtain ⟨w₀, w₀m, tw⟩ : ∃ w ∈ W, D t w = true := by
    by_contra! none
    have sub : outN D V t ⊆ Z := by
      intro z hz
      have arc := (mem_outN.mp hz).2
      rcases mem_union.mp (headsY t tm hz) with zwxy | zz
      · rcases mem_union.mp zwxy with zwx | zy
        · rcases mem_union.mp zwx with zw | zx
          · exact (none z zw arc).elim
          · exact (noX z zx arc).elim
        · exact (kt z zy arc).elim
      · exact zz
    have := card_le_card sub
    have := degY t tm
    omega
  -- `w₀` is `(q-2)`-deep, so its shortest sink path covers `W`
  have deep : Deep D W (q - 2) w₀ := by
    obtain ⟨p, pm, pt⟩ := parentY t tm
    exact return_deep free wv w₀m (fun s sm ks =>
      Walk.step (xv pm) (mem_outN.mp (full s sm ks pm)).2 (Walk.step (yv tm) pt (.refl t))) tw
  obtain ⟨P⟩ := exists_shortest_sink_path fw sw w₀m
  have plen := (deep_iff_len P).mp deep
  have bound := P.bounded
  have cover := path_cover fw sw P (by omega)
  -- (a) rows `vᵢ` with `i < len` have one head in `W`, and avoid every `X`-parent of `t`
  have oneW (i) (il : i < P.len) : outN D W (P.vertex i) ⊆ {P.vertex (i+1)} := by
    intro z hz
    obtain ⟨j, jl, rfl⟩ := cover z (mem_outN.mp hz).1
    rw [P.no_chord fw sw (by omega) jl (mem_outN.mp hz).2]
    exact mem_singleton_self _
  have avoid (i) (il : i < P.len) (p) (pm : p ∈ X) (pt : D p t = true) : D (P.vertex i) p ≠ true := by
    intro arc
    have back : Walk D V w₀ (P.vertex i) i := by
      have := (P.walk (i := 0) (j := i) (Nat.zero_le _) il.le).mono wv
      simpa [P.start] using this
    have loop := Walk.step (xv pm) arc (Walk.step (yv tm) pt (Walk.step (wv w₀m) tw back))
    exact free _ (i + 1 + 1 + 1) (by omega) (by omega) loop
  have manyX (i) (il : i < P.len) : r - 1 ≤ (outN D X (P.vertex i)).card := by
    have vm : P.vertex i ∈ W := P.mem _ il.le
    have split : outN D V (P.vertex i) ⊆ outN D W (P.vertex i) ∪ outN D X (P.vertex i) := by
      intro z hz
      have arc := (mem_outN.mp hz).2
      rcases mem_union.mp (headsW _ vm hz) with zw | zx
      · exact mem_union_left _ (mem_outN.mpr ⟨zw, arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨zx, arc⟩)
    have h1 := (card_le_card split).trans (card_union_le _ _)
    have h2 := card_le_card (oneW i il)
    rw [card_singleton] at h2
    have := degW _ vm
    omega
  obtain ⟨p₀, p₀m, p₀t⟩ := parentY t tm
  -- the `X`-parent of `t` is unique, and every `vᵢ` heads every other row of `X`
  have allX (i) (il : i < P.len) (x) (xm : x ∈ X) (ne : x ≠ p₀) : D (P.vertex i) x = true := by
    have sub : outN D X (P.vertex i) ⊆ X.erase p₀ := fun z hz =>
      mem_erase.mpr ⟨fun e => avoid i il p₀ p₀m p₀t (e ▸ (mem_outN.mp hz).2), (mem_outN.mp hz).1⟩
    have eq := eq_of_subset_of_card_le sub (by rw [card_erase_of_mem p₀m, cx]; exact manyX i il)
    exact (mem_outN.mp (eq.symm ▸ mem_erase.mpr ⟨ne, xm⟩ : x ∈ outN D X (P.vertex i))).2
  have unique (p) (pm : p ∈ X) (pt : D p t = true) : p = p₀ := by
    by_contra ne
    exact avoid 0 (by omega) p pm pt (allX 0 (by omega) p pm ne)
  have w₀X (x) (xm : x ∈ X) (ne : x ≠ p₀) : D w₀ x = true := by
    have := allX 0 (by omega) x xm ne
    rwa [P.start] at this
  -- every row of `W` heads every row of `X` other than `p₀`
  have anyW (w) (wm : w ∈ W) (x) (xm : x ∈ X) (ne : x ≠ p₀) : D w x = true := by
    obtain ⟨i, il, rfl⟩ := cover w wm
    rcases Nat.lt_or_ge i P.len with lt | ge
    · exact allX i lt x xm ne
    · have e : i = P.len := by omega
      subst e
      exact (mem_outN.mp (full _ (P.mem _ le_rfl) (fun z zm => P.sink z zm) xm)).2
  have r2 : 2 ≤ X.card := by omega
  by_cases other : ∃ σ ∈ X, Sink D X σ ∧ σ ≠ p₀
  swap
  · -- Case B: `p₀` is the only `X`-sink, and one of its `X`-parents closes a four-cycle
    push Not at other
    obtain ⟨x, xm, xne⟩ := exists_mem_ne (show 1 < X.card by omega) p₀
    obtain ⟨s, sm, stop, m, _, walk⟩ := reach_sink_of_card fx sx xm
    have sp := other s sm (fun z zm => stop z zm)
    subst sp
    obtain ⟨x', x'm, arc⟩ := last_parent xm walk xne
    have ne : x' ≠ s := fun e => loopfree free q1 (xv x'm) (e ▸ arc)
    have loop := Walk.step (xv x'm) (w₀X x' x'm ne) (Walk.step (xv p₀m) arc
      (Walk.step (yv tm) p₀t (Walk.step (wv w₀m) tw (.refl w₀))))
    exact free w₀ _ (by omega) (by omega) loop
  -- Case A: a second `X`-sink `σ`
  obtain ⟨σ, σm, kσ, σne⟩ := other
  -- (b) an `X`-sink other than `p₀` heads all of `Y` except `t`
  have sigmaAll (σ') (σ'm : σ' ∈ X) (kσ' : Sink D X σ') (ne : σ' ≠ p₀) (y) (ym : y ∈ Y)
      (yne : y ≠ t) : D σ' y = true := by
    have sub : outN D V σ' ⊆ Y.erase t := fun z hz =>
      mem_erase.mpr ⟨fun e => ne (unique σ' σ'm (e ▸ (mem_outN.mp hz).2)), sinkY σ' σ'm kσ' hz⟩
    have eq := eq_of_subset_of_card_le sub (by rw [card_erase_of_mem tm, cy]; simpa using degX σ' σ'm)
    exact (mem_outN.mp (eq.symm ▸ mem_erase.mpr ⟨yne, ym⟩ : y ∈ outN D V σ')).2
  -- (c) no other row of `Y` heads `t`
  have noT (y) (ym : y ∈ Y) (yne : y ≠ t) : D y t ≠ true := by
    intro arc
    have loop := Walk.step (yv tm) arc (Walk.step (wv w₀m) tw (Walk.step (xv σm) (w₀X σ σm σne)
      (Walk.step (yv ym) (sigmaAll σ σm kσ σne y ym yne) (.refl y))))
    exact free y _ (by omega) (by omega) loop
  -- (d) no other row of `Y` heads `W`
  have noW (y) (ym : y ∈ Y) (yne : y ≠ t) (w) (wm : w ∈ W) : D y w ≠ true := by
    intro arc
    have loop := Walk.step (wv wm) arc (Walk.step (xv σm) (anyW w wm σ σm σne)
      (Walk.step (yv ym) (sigmaAll σ σm kσ σne y ym yne) (.refl y)))
    exact free y _ (by omega) (by omega) loop
  -- (e)–(f) a sink of `Y \ {t}` returns into `X`, from where `p₀` is the sink reached
  have key (y₁) (y₁m : y₁ ∈ Y.erase t) (k₁ : Sink D (Y.erase t) y₁) :
      ∃ x₁ ∈ X, D y₁ x₁ = true ∧ ∃ m, m + 2 ≤ r ∧ Walk D X x₁ p₀ m ∧ Sink D X p₀ ∧
        D p₀ y₁ ≠ true := by
    obtain ⟨y₁ne, y₁Y⟩ := mem_erase.mp y₁m
    obtain ⟨x₁, x₁m, y₁x₁⟩ : ∃ x ∈ X, D y₁ x = true := by
      by_contra! none
      have sub : outN D V y₁ ⊆ Z := by
        intro z hz
        have arc := (mem_outN.mp hz).2
        rcases mem_union.mp (headsY y₁ y₁Y hz) with zwxy | zz
        · rcases mem_union.mp zwxy with zwx | zy
          · rcases mem_union.mp zwx with zw | zx
            · exact (noW y₁ y₁Y y₁ne z zw arc).elim
            · exact (none z zx arc).elim
          · by_cases zt : z = t
            · exact (noT y₁ y₁Y y₁ne (zt ▸ arc)).elim
            · exact (k₁ z (mem_erase.mpr ⟨zt, zy⟩) arc).elim
        · exact zz
      have := card_le_card sub
      have := degY y₁ y₁Y
      omega
    obtain ⟨Q⟩ := exists_shortest_sink_path fx sx x₁m
    have qwalk := Q.walk (i := 0) (j := Q.len) (Nat.zero_le _) le_rfl
    simp only [Q.start, Nat.sub_zero] at qwalk
    have qend := Q.mem _ le_rfl
    have qsink : Sink D X (Q.vertex Q.len) := fun z zm => Q.sink z zm
    have qb := Q.bounded
    have close (h : D (Q.vertex Q.len) y₁ = true) : False := by
      have loop := Walk.step (xv x₁m) y₁x₁ ((qwalk.mono xv).snoc (yv y₁Y) h)
      exact free y₁ _ (by omega) (by omega) loop
    have isP : Q.vertex Q.len = p₀ := by
      by_contra ne
      exact close (sigmaAll _ qend qsink ne y₁ y₁Y y₁ne)
    -- (h) the path avoids `σ`, so it has at most `r - 2` arcs
    have avoid : (range (Q.len + 1)).image Q.vertex ⊆ X.erase σ := by
      intro a am
      obtain ⟨i, im, rfl⟩ := mem_image.mp am
      have il := mem_range.mp im
      refine mem_erase.mpr ⟨fun e => ?_, Q.mem _ (by omega)⟩
      rcases Nat.lt_or_ge i Q.len with lt | ge
      · exact kσ _ (Q.mem _ (by omega)) (e ▸ Q.edge i lt)
      · exact σne (e.symm.trans (by rw [show i = Q.len by omega]; exact isP))
    have count := card_le_card avoid
    rw [card_image_of_injOn (Q.injective fx sx), card_range, card_erase_of_mem σm, cx] at count
    exact ⟨x₁, x₁m, y₁x₁, Q.len, by omega, isP ▸ qwalk, isP ▸ qsink, isP ▸ close⟩
  -- (g) `Y \ {t}` has a unique sink `y₁`, and some `y₂` heads it
  have fyt := free.mono_set ((erase_subset t Y).trans yv)
  have syt : (Y.erase t).card ≤ q := by rw [card_erase_of_mem tm]; omega
  obtain ⟨y₁, y₁m, stop₁⟩ := exists_sink fyt (card_pos.mp (by rw [card_erase_of_mem tm]; omega)) syt
  have k₁ : Sink D (Y.erase t) y₁ := fun z zm => stop₁ z zm
  obtain ⟨x₁, x₁m, y₁x₁, m, ml, walk, kp, miss⟩ := key y₁ y₁m k₁
  have one := sink_omits (headsX' p₀ p₀m) kp (degX p₀ p₀m) cy
  have only (y) (ym : y ∈ Y.erase t) (ky : Sink D (Y.erase t) y) : y = y₁ := by
    obtain ⟨_, _, _, _, _, _, _, miss'⟩ := key y ym ky
    exact card_le_one.mp one y (mem_sdiff.mpr ⟨(mem_erase.mp ym).2, fun h => miss' (mem_outN.mp h).2⟩)
      y₁ (mem_sdiff.mpr ⟨(mem_erase.mp y₁m).2, fun h => miss (mem_outN.mp h).2⟩)
  obtain ⟨b, bm, bne⟩ := exists_mem_ne (show 1 < (Y.erase t).card by rw [card_erase_of_mem tm]; omega) y₁
  obtain ⟨s', s'm, stop', m', _, walk'⟩ := reach_sink_of_card fyt syt bm
  have e := only s' s'm (fun z zm => stop' z zm)
  subst e
  obtain ⟨y₂, y₂m, y₂y₁⟩ := last_parent bm walk' bne
  have y₂ne : y₂ ≠ s' := fun e => loopfree free q1 (yv (mem_erase.mp y₂m).2) (e ▸ y₂y₁)
  have py₂ : D p₀ y₂ = true := by
    by_contra no
    exact y₂ne (card_le_one.mp one y₂ (mem_sdiff.mpr ⟨(mem_erase.mp y₂m).2, fun h => no (mem_outN.mp h).2⟩)
      s' (mem_sdiff.mpr ⟨(mem_erase.mp s'm).2, fun h => miss (mem_outN.mp h).2⟩))
  -- (h) the closed walk `p₀ → y₂ → y₁ → x₁ ⇝ p₀`
  have loop := Walk.step (yv (mem_erase.mp y₂m).2) py₂ (Walk.step (yv (mem_erase.mp s'm).2) y₂y₁
    (Walk.step (xv x₁m) y₁x₁ (walk.mono xv)))
  exact free p₀ _ (by omega) (by omega) loop

#print axioms full_front_tight_false
end LeanCH.BR.WideLayerReturn
