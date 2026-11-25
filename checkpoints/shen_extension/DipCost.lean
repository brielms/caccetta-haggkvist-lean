import checkpoints.shen_extension.FlatPersist

/-!
# The cost of a dip after flat layers

Generic in `q`, `r`, the layer index and the deficit `c`.

* `flat_keep`: the inner statement of `FlatPersist.flat_persist`, exported. If the layers
  `L 0 … L (h-1)` all have exactly `r` rows (`r < q`, `h + 1 ≤ q`), no row of them has a head in an
  earlier layer.
* (P1) `layer_host`, `layer_host_order`: if no row of `X` has a head outside `X ∪ Y` and
  `|Y| + c ≤ r`, every row of `X` has `≥ c` heads inside `X`, so `X` is a `q`-free digraph of
  minimum out-degree `≥ c` and `N ≤ |X|` whenever `Order q c N`.
  Instances: `order_one` (`Order q 1 (q+1)`: a cycle), `order_two` (`Order q 2 (2q+1)`:
  `BRq2.ball_growth`), `order_of_noHost` (`NoHost q c ⇒ Order q c (q c + 1)`).
* (P2, corrected) `far_return_free`: true BFS layers, `L 0 … L (g-1)` of width `r`, `L g` arbitrary,
  `r + 2 ≤ q`, `g + 2 ≤ q`. A row of `L g` has no head in `L j` for `j + 2 ≤ g`. The returning row
  `x ∈ L g` is reached through its parent `p ∈ L (g-1)`; the funnel lives in `L j … L (g-2)` (a sink
  of `L (g-1)` need not reach `p`), which costs one unit: the end count is `q - 1 ≤ r` instead of
  `q ≤ r`. Returns of span one (`L g → L (g-1)`) are NOT excluded by this argument.
* `dip_cost`, `flat_root_dip`: (P1) + (P2) with span-one returns excluded by hypothesis.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.DipCost
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors SinkDepthReturn FlatPersist
open MixedRadiusCompletion (Order)

/-- **Flat layers keep their heads** (the inner claim of `flat_persist`). -/
theorem flat_keep {D V q r h} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r < q) (time : h + 1 ≤ q)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < h → (L i).card=r)
    (quota : ∀ (i : ℕ), i < h → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i < h → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j) :
    ∀ i, i < h → ∀v∈L i,outN D V v⊆L i∪L (i+1) := by
  classical
  have sinks {i} (hi : i < h) (hi' : i+1 < h)
      (keep : ∀v∈L i,outN D V v⊆L i∪L (i+1)) (s) (sm : s∈L i) (last : Sink D (L i) s) :
      L (i+1)⊆outN D V s := by
    apply (eq_of_subset_of_card_le (s:=outN D V s) (t:=L (i+1)) ?_ ?_).symm.subset
    · exact fun x xm=>(mem_union.mp (keep s sm xm)).resolve_left (fun a=>last x a (mem_outN.mp xm).2)
    · rw [size _ hi']; exact quota i hi s sm
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro x xm y ym
    obtain ⟨j,le,yj⟩ := step i hi x xm y ym
    by_cases eq : j=i+1
    · exact mem_union_right _ (eq ▸ yj)
    by_cases same : j=i
    · exact mem_union_left _ (same ▸ yj)
    exfalso
    have ji : j < i := by omega
    have arc := (mem_outN.mp ym).2
    have yV := sub j yj
    let G : ℕ → Finset ℕ := fun m => (L m).filter (fun z => Walk D V y z (m - j))
    have reach (m) (jm : j ≤ m) (mi : m < i) :
        ∀ s ∈ L m, Sink D (L m) s → Walk D V s y (i - m + 1) := by
      intro s sm stop
      have tail := EqualLayerTransit.from_sink L free sub i
        (fun k _ ki=>(size k (by omega)).le.trans hq.le)
        (fun k _ ki=>card_pos.mp (by rw [size k (by omega)]; exact hr))
        (fun k _ ki=>sinks (by omega) (by omega) (ih k ki (by omega))) mi sm stop xm
      exact tail.snoc yV arc
    have gdeep (m) (jm : j ≤ m) (mi : m < i) : ∀ z ∈ G m, Deep D (L m) (q - (i - j)) z := by
      intro z zm
      have w := (mem_filter.mp zm).2
      have d := squeeze free (sub m) (by omega) w (reach m jm mi)
      exact d.mono (by omega)
    have grow (m) (jm : j ≤ m) (mi : m + 1 < i) (ne : (G m).Nonempty) :
        (G m).card + (q - (i - j) - 1) ≤ (G (m+1)).card :=
      growth free (sub m) (size m (by omega)) hq.le (by omega) (filter_subset _ _) ne
        (gdeep m jm (by omega)) (fun z zm => quota m (by omega) z (mem_filter.mp zm).1)
        (fun z zm => ih m (by omega) (by omega) z (mem_filter.mp zm).1)
        (fun z zm w wm arc' => mem_filter.mpr ⟨wm, by
          have p := ((mem_filter.mp zm).2).snoc (sub _ wm) arc'
          rwa [show m - j + 1 = m + 1 - j by omega] at p⟩)
    have count : ∀ d, j + d < i → d + 1 ≤ (G (j+d)).card := by
      intro d
      induction d with
      | zero =>
        intro _
        refine card_pos.mpr ⟨y, mem_filter.mpr ⟨yj, ?_⟩⟩
        simpa using (Walk.refl y : Walk D V y y 0)
      | succ d ihd =>
        intro lt
        have prev := ihd (by omega)
        have g := grow (j+d) (by omega) (by omega) (card_pos.mp (by omega))
        rw [show j + (d+1) = j + d + 1 by omega]
        omega
    have last := count (i - 1 - j) (by omega)
    rw [show j + (i - 1 - j) = i - 1 by omega] at last
    have fx : QFree D (L (i-1)) q := free.mono_set (sub _)
    have sz := size (i-1) (by omega)
    have pos : 0 < (G (i-1)).card := by omega
    have bound := deep_card_of (G := G (i-1)) (t := q - (i - j)) fx (sz.le.trans hq.le)
      (filter_subset _ _) (gdeep (i-1) (by omega) (by omega)) (card_pos.mp pos)
    omega

/-- Sinks of a flat layer head all of the next flat layer. -/
theorem flat_sinks {D V q r h} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r < q) (time : h + 1 ≤ q)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < h → (L i).card=r)
    (quota : ∀ (i : ℕ), i < h → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i < h → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j)
    {i : ℕ} (hi' : i+1 < h) (s : ℕ) (sm : s∈L i) (last : Sink D (L i) s) :
    L (i+1)⊆outN D V s := by
  have keep := flat_keep L free hr hq time sub size quota step i (by omega)
  apply (eq_of_subset_of_card_le (s:=outN D V s) (t:=L (i+1)) ?_ ?_).symm.subset
  · exact fun x xm=>(mem_union.mp (keep s sm xm)).resolve_left (fun a=>last x a (mem_outN.mp xm).2)
  · rw [size _ hi']; exact quota i (by omega) s sm

/-! ### (P1) the layer host -/

/-- **(P1) Layer host.** Heads of `X` inside `X ∪ Y`, `|Y| + c ≤ r`: every row of `X` has at least
`c` heads inside `X`. -/
theorem layer_host {D : CH.Digraph} {V X Y : Finset ℕ} {r c : ℕ}
    (quota : ∀ v ∈ X, r ≤ (outN D V v).card) (keep : ∀ v ∈ X, outN D V v ⊆ X ∪ Y)
    (small : Y.card + c ≤ r) : ∀ v ∈ X, c ≤ (outN D X v).card := by
  classical
  intro v hv
  have cover : outN D V v ⊆ outN D X v ∪ Y := by
    intro w wm
    rcases mem_union.mp (keep v hv wm) with wx | wy
    · exact mem_union_left _ (mem_outN.mpr ⟨wx, (mem_outN.mp wm).2⟩)
    · exact mem_union_right _ wy
  have := (quota v hv).trans ((card_le_card cover).trans (card_union_le _ _))
  omega

/-- **(P1), order form.** -/
theorem layer_host_order {D : CH.Digraph} {V X Y : Finset ℕ} {q r c N : ℕ}
    (free : QFree D V q) (xv : X ⊆ V) (ne : X.Nonempty)
    (quota : ∀ v ∈ X, r ≤ (outN D V v).card) (keep : ∀ v ∈ X, outN D V v ⊆ X ∪ Y)
    (small : Y.card + c ≤ r) (order : Order q c N) : N ≤ X.card :=
  order D X (free.mono_set xv) (layer_host quota keep small) ne

/-- **Instance, `c = 1`.** A nonempty `q`-free digraph of minimum out-degree `≥ 1` contains a cycle,
so it has at least `q + 1` vertices. -/
theorem order_one (q : ℕ) : Order q 1 (q+1) := by
  intro F U free deg ne
  by_contra! small
  obtain ⟨s, sm, stop⟩ := exists_sink free ne (by omega)
  obtain ⟨w, wm⟩ := card_pos.mp (show 0 < (outN F U s).card by have := deg s sm; omega)
  exact stop w (mem_outN.mp wm).1 (mem_outN.mp wm).2

/-- **Instance, `c = 2`** (`BRq2.ball_growth`). -/
theorem order_two {q : ℕ} (hq : 1 ≤ q) : Order q 2 (2*q+1) := by
  intro F U free deg ne
  obtain ⟨u, hu⟩ := ne
  have := BRq2.ball_growth q hq F U free (fun v hv => deg v hv) u hu q le_rfl
  exact this.trans (card_le_card ball_subset)

/-- **Instance from `NoHost`.** -/
theorem order_of_noHost {q c : ℕ} (none : BypassRepair.NoHost q c) : Order q c (q*c+1) := by
  intro F U free deg ne
  by_contra! small
  exact none F U ne (by omega) free deg

/-! ### (P2) no far returns from the first wide layer -/

/-- **(P2), corrected.** True BFS layers (`par`): `L 0 … L (g-1)` of width `r`, `L g` arbitrary,
`r + 2 ≤ q`, `g + 2 ≤ q`. Every head of a row of `L g` lies in `L (g-1) ∪ L g ∪ L (g+1)`. -/
theorem far_return_free {D V q r g} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r + 2 ≤ q) (time : g + 2 ≤ q)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < g → (L i).card=r)
    (quota : ∀ (i : ℕ), i ≤ g → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i ≤ g → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j)
    (par : 1 ≤ g → ∀ x ∈ L g, ∃ p ∈ L (g-1), D p x = true) :
    ∀ x ∈ L g, ∀ y ∈ outN D V x, y ∈ L (g-1) ∨ y ∈ L g ∨ y ∈ L (g+1) := by
  classical
  intro x xm y ym
  obtain ⟨j, le, yj⟩ := step g le_rfl x xm y ym
  by_cases near : g ≤ j + 1
  · rcases (by omega : j = g - 1 ∨ j = g ∨ j = g + 1) with rfl | rfl | rfl
    · exact Or.inl yj
    · exact Or.inr (Or.inl yj)
    · exact Or.inr (Or.inr yj)
  exfalso
  have hq' : r < q := by omega
  have keep := flat_keep (h := g) L free hr hq' (by omega) sub size
    (fun i hi => quota i hi.le) (fun i hi => step i hi.le)
  have sinks {i} (hi' : i+1 < g) := flat_sinks (h := g) L free hr hq' (by omega) sub size
    (fun i hi => quota i hi.le) (fun i hi => step i hi.le) hi'
  obtain ⟨p, pm, px⟩ := par (by omega) x xm
  have arc := (mem_outN.mp ym).2
  have yV := sub j yj
  have xV := sub g xm
  let G : ℕ → Finset ℕ := fun m => (L m).filter (fun z => Walk D V y z (m - j))
  have reach (m) (jm : j ≤ m) (mi : m + 1 < g) :
      ∀ s ∈ L m, Sink D (L m) s → Walk D V s y (g - m + 1) := by
    intro s sm stop
    have tail := EqualLayerTransit.from_sink L free sub (g-1)
      (fun k _ ki=>(size k (by omega)).le.trans hq'.le)
      (fun k _ ki=>card_pos.mp (by rw [size k (by omega)]; exact hr))
      (fun k _ ki=>sinks (by omega)) (by omega) sm stop pm
    have w := (tail.snoc xV px).snoc yV arc
    rwa [show g - 1 - m + 1 + 1 = g - m + 1 by omega] at w
  have gdeep (m) (jm : j ≤ m) (mi : m + 1 < g) : ∀ z ∈ G m, Deep D (L m) (q - (g - j)) z := by
    intro z zm
    have w := (mem_filter.mp zm).2
    have d := squeeze free (sub m) (by omega) w (reach m jm mi)
    exact d.mono (by omega)
  have grow (m) (jm : j ≤ m) (mi : m + 2 < g) (ne : (G m).Nonempty) :
      (G m).card + (q - (g - j) - 1) ≤ (G (m+1)).card :=
    growth free (sub m) (size m (by omega)) hq'.le (by omega) (filter_subset _ _) ne
      (gdeep m jm (by omega)) (fun z zm => quota m (by omega) z (mem_filter.mp zm).1)
      (fun z zm => keep m (by omega) z (mem_filter.mp zm).1)
      (fun z zm w wm arc' => mem_filter.mpr ⟨wm, by
        have p := ((mem_filter.mp zm).2).snoc (sub _ wm) arc'
        rwa [show m - j + 1 = m + 1 - j by omega] at p⟩)
  have count : ∀ d, j + d + 1 < g → d + 1 ≤ (G (j+d)).card := by
    intro d
    induction d with
    | zero =>
      intro _
      refine card_pos.mpr ⟨y, mem_filter.mpr ⟨yj, ?_⟩⟩
      simpa using (Walk.refl y : Walk D V y y 0)
    | succ d ihd =>
      intro lt
      have prev := ihd (by omega)
      have g' := grow (j+d) (by omega) (by omega) (card_pos.mp (by omega))
      rw [show j + (d+1) = j + d + 1 by omega]
      omega
  have last := count (g - 2 - j) (by omega)
  rw [show j + (g - 2 - j) = g - 2 by omega] at last
  have fx : QFree D (L (g-2)) q := free.mono_set (sub _)
  have sz := size (g-2) (by omega)
  have pos : 0 < (G (g-2)).card := by omega
  have bound := deep_card_of (G := G (g-2)) (t := q - (g - j)) fx (sz.le.trans hq'.le)
    (filter_subset _ _) (gdeep (g-2) (by omega) (by omega)) (card_pos.mp pos)
  omega

/-- **Dip cost.** (P1) + (P2): flat `L 0 … L (g-1)`, no span-one return from `L g`, and
`|L (g+1)| + c ≤ r`: then `N ≤ |L g|` for every `Order q c N`. -/
theorem dip_cost {D V q r g c N} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r + 2 ≤ q) (time : g + 2 ≤ q)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < g → (L i).card=r)
    (quota : ∀ (i : ℕ), i ≤ g → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i ≤ g → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j)
    (par : 1 ≤ g → ∀ x ∈ L g, ∃ p ∈ L (g-1), D p x = true)
    (unit : 1 ≤ g → ∀ x ∈ L g, ∀ y ∈ outN D V x, y ∉ L (g-1))
    (ne : (L g).Nonempty) (dip : (L (g+1)).card + c ≤ r) (order : Order q c N) :
    N ≤ (L g).card := by
  have far := far_return_free L free hr hq time sub size quota step par
  refine layer_host_order free (sub g) ne (quota g le_rfl) (fun x xm y ym => ?_) dip order
  rcases far x xm y ym with h | h | h
  · rcases Nat.eq_zero_or_pos g with g0 | g1
    · subst g0; exact mem_union_left _ h
    · exact absurd h (unit g1 x xm y ym)
  · exact mem_union_left _ h
  · exact mem_union_right _ h

open DotTwoPassShellTransport (layer) in
/-- **Dip cost at a root** (the shape of `flat_root_persist`). Root `u`, layers `1 … h-1` of width `r`
(`2 ≤ h`, `h + 1 ≤ q`, `r + 2 ≤ q`), no arc from layer `h` to layer `h-1` (`unit`), and
`|layer (h+1)| + c ≤ r`: then `|layer h| ≥ N` for every `Order q c N`. -/
theorem flat_root_dip {D : CH.Digraph} {V : Finset ℕ} {q r h c N u : ℕ}
    (free : QFree D V q) (hr : 0 < r) (hq : r + 2 ≤ q) (depth : 2 ≤ h)
    (time : h + 1 ≤ q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (flat : ∀ k, 1 ≤ k → k < h → (layer D V k u).card = r)
    (unit : ∀ x ∈ layer D V h u, ∀ y ∈ outN D V x, y ∉ layer D V (h-1) u)
    (ne : (layer D V h u).Nonempty)
    (dip : (layer D V (h+1) u).card + c ≤ r) (order : Order q c N) :
    N ≤ (layer D V h u).card := by
  have e : h - 1 + 1 = h := by omega
  have key := dip_cost (D := D) (V := V) (q := q) (r := r) (g := h-1) (c := c) (N := N)
    (fun i => layer D V (i+1) u) free hr hq (by omega)
    (fun i => sdiff_subset.trans ball_subset)
    (fun i hi => flat (i+1) (by omega) (by omega))
    (fun i _ v hv => degree v (sdiff_subset.trans ball_subset hv))
    (fun i hi v hv x hx => by
      obtain ⟨j, j1, j2, hj⟩ := ShapeClimbRoot.head_mem free hu (i := i+1) (by omega) (by omega) hv hx
      exact ⟨j - 1, by omega, by rwa [Nat.sub_add_cancel j1]⟩)
    (fun g1 x xm => by
      simp only [e] at xm
      obtain ⟨p, pm, px⟩ := ShapeClimbRoot.parent_mem (i := h-1) hu (by omega) (by rwa [e])
      exact ⟨p, by rwa [show h - 1 - 1 + 1 = h - 1 by omega], px⟩)
    (fun g1 x xm y ym => by
      simp only [e] at xm
      rw [show h - 1 - 1 + 1 = h - 1 by omega]
      exact unit x xm y ym)
    (by simpa only [e] using ne) (by simpa only [e, show h - 1 + 1 + 1 = h + 1 by omega] using dip) order
  simpa only [e] using key

/-! ### Span-one returns land in the last flat layer: two-layer hosts -/

/-- **Two-layer host.** Flat `L 0 … L (g-1)` (`1 ≤ g`), `L g` arbitrary, `|L (g+1)| + c ≤ r`: the set
`L (g-1) ∪ L g` is a `q`-free digraph of minimum out-degree `≥ c` (span-one returns stay inside it),
so `N ≤ r + |L g|` for every `Order q c N`. -/
theorem wide_dip_order {D V q r g c N} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r + 2 ≤ q) (time : g + 2 ≤ q) (g1 : 1 ≤ g)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < g → (L i).card=r)
    (quota : ∀ (i : ℕ), i ≤ g → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i ≤ g → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j)
    (par : 1 ≤ g → ∀ x ∈ L g, ∃ p ∈ L (g-1), D p x = true)
    (dip : (L (g+1)).card + c ≤ r) (order : Order q c N) : N ≤ r + (L g).card := by
  classical
  have far := far_return_free L free hr hq time sub size quota step par
  have keepA := flat_keep (h := g) L free hr (by omega) (by omega) sub size
    (fun i hi => quota i hi.le) (fun i hi => step i hi.le) (g-1) (by omega)
  rw [Nat.sub_add_cancel g1] at keepA
  have ne : (L (g-1) ∪ L g).Nonempty := by
    rw [← card_pos]
    have := card_le_card (subset_union_left (s₁ := L (g-1)) (s₂ := L g))
    rw [size _ (by omega)] at this
    omega
  have bound := layer_host_order (X := L (g-1) ∪ L g) (Y := L (g+1)) free
    (union_subset (sub _) (sub _)) ne
    (fun v hv => by
      rcases mem_union.mp hv with h | h
      · exact quota _ (by omega) v h
      · exact quota _ le_rfl v h)
    (fun v hv w wm => by
      rcases mem_union.mp hv with h | h
      · exact mem_union_left _ (keepA v h wm)
      · rcases far v h w wm with h' | h' | h'
        · exact mem_union_left _ (mem_union_left _ h')
        · exact mem_union_left _ (mem_union_right _ h')
        · exact mem_union_right _ h')
    dip order
  have := card_union_le (L (g-1)) (L g)
  rw [size _ (by omega)] at this
  omega

/-- **One unit of excess cannot pay for a dip.** True BFS layers, `L 0 … L (g-1)` of width `r`
(`1 ≤ g`), `|L g| = r + 1`, `|L (g+1)| ≤ r - 1`, `r + 2 ≤ q`, `g + 2 ≤ q`: impossible.

Proof. `A = L (g-1)`, `B = L g`, `C = L (g+1)`. A sink `σ` of `A` heads `≥ r` of the `r+1` rows of
`B`, so it misses at most one. A row `z ∈ B` with a head `y ∈ A`: `y` reaches an `A`-sink `σ` in
`k < r` steps; `σ ↛ z` (cycle of `k + 2 ≤ q`), and no `z' ∈ B` heads `z` (else `σ → z'`, cycle of
`k + 3 ≤ q`). A row of `B` with no head in `A` has a head in `B` (`|C| < r`). So the rows of `B`
headed inside `B` would form a sinkless set: `B` has no inner arc, every row of `B` has a head in `A`,
and `z ↦ σ_z` is injective from `B` to `A`, `r + 1 ≤ r`. -/
theorem unit_dip_false {D V q r g} (L : ℕ→Finset ℕ) (free : QFree D V q)
    (hr : 0 < r) (hq : r + 2 ≤ q) (time : g + 2 ≤ q) (g1 : 1 ≤ g)
    (sub : ∀ (i : ℕ), L i⊆V) (size : ∀ (i : ℕ), i < g → (L i).card=r)
    (wide : (L g).card = r + 1) (dip : (L (g+1)).card + 1 ≤ r)
    (quota : ∀ (i : ℕ), i ≤ g → ∀v∈L i,r ≤ (outN D V v).card)
    (step : ∀ (i : ℕ), i ≤ g → ∀v∈L i, ∀x∈outN D V v, ∃ (j : ℕ), j ≤ i + 1 ∧ x∈L j)
    (par : 1 ≤ g → ∀ x ∈ L g, ∃ p ∈ L (g-1), D p x = true) : False := by
  classical
  have far := far_return_free L free hr hq time sub size quota step par
  have keepA := flat_keep (h := g) L free hr (by omega) (by omega) sub size
    (fun i hi => quota i hi.le) (fun i hi => step i hi.le) (g-1) (by omega)
  rw [Nat.sub_add_cancel g1] at keepA
  set A := L (g-1) with hA
  set B := L g with hB
  set C := L (g+1) with hC
  have cardA : A.card = r := size _ (by omega)
  have qA : ∀ v ∈ A, r ≤ (outN D V v).card := quota _ (by omega)
  have qB : ∀ v ∈ B, r ≤ (outN D V v).card := quota _ le_rfl
  have aV : A ⊆ V := sub _
  have bV : B ⊆ V := sub _
  -- sinks of `A` miss at most one row of `B`
  have sinkB : ∀ σ ∈ A, Sink D A σ → outN D V σ ⊆ B := fun σ sm stop w wm =>
    (mem_union.mp (keepA σ sm wm)).resolve_left (fun wa => stop w wa (mem_outN.mp wm).2)
  have miss : ∀ σ ∈ A, Sink D A σ → ∀ z ∈ B, ∀ z' ∈ B, z ≠ z' →
      D σ z ≠ true → D σ z' ≠ true → False := by
    intro σ sm stop z zb z' zb' ne h1 h2
    have sub2 : outN D V σ ⊆ (B.erase z).erase z' := by
      intro w wm
      have wb := sinkB σ sm stop wm
      have arc := (mem_outN.mp wm).2
      refine mem_erase.mpr ⟨fun e => h2 (e ▸ arc), mem_erase.mpr ⟨fun e => h1 (e ▸ arc), wb⟩⟩
    have c1 := card_le_card sub2
    rw [card_erase_of_mem (mem_erase.mpr ⟨ne.symm, zb'⟩), card_erase_of_mem zb, wide] at c1
    have := qA σ sm
    omega
  -- every row of `A` reaches an `A`-sink in fewer than `r` steps
  have toSink : ∀ y ∈ A, ∃ σ ∈ A, Sink D A σ ∧ ∃ k, k < r ∧ Walk D A y σ k := by
    intro y ym
    by_contra! none
    have deep : Deep D A r y := fun σ sm stop k w => by
      by_contra! lt
      exact none σ sm stop k lt w
    have := deep_card_of (G := {y}) (t := r) (free.mono_set aV) (by omega)
      (singleton_subset_iff.mpr ym) (fun z zm => by rw [mem_singleton.mp zm]; exact deep)
      (singleton_nonempty y)
    simp at this
    omega
  -- a row of `B` with a head in `A` is missed by an `A`-sink and has no in-arc from `B`
  have key : ∀ z ∈ B, ∀ y ∈ A, D z y = true →
      ∃ σ ∈ A, Sink D A σ ∧ D σ z ≠ true ∧ ∀ z' ∈ B, D z' z ≠ true := by
    intro z zb y ya zy
    obtain ⟨σ, sm, stop, k, kr, w⟩ := toSink y ya
    have notz : D σ z ≠ true := by
      intro sz
      have loop := ((w.mono aV).snoc (bV zb) sz).snoc (aV ya) zy
      exact free y (k+1+1) (by omega) (by omega) loop
    refine ⟨σ, sm, stop, notz, fun z' zb' arc => ?_⟩
    by_cases e : z' = z
    · subst e
      exact loopfree free (by omega) (bV zb) arc
    have sz' : D σ z' = true := by
      by_contra h
      exact miss σ sm stop z zb z' zb' (Ne.symm e) notz h
    have loop := (((w.mono aV).snoc (bV zb') sz').snoc (bV zb) arc).snoc (aV ya) zy
    exact free y (k+1+1+1) (by omega) (by omega) loop
  -- a row of `B` with no head in `B` has a head in `A`; with no head in `A` it has one in `B`
  have headIn : ∀ z ∈ B, ∀ T : Finset ℕ, (∀ w ∈ outN D V z, w ∈ T ∨ w ∈ C) →
      ∃ w ∈ T, D z w = true := by
    intro z zb T cover
    by_contra! none
    have s2 : outN D V z ⊆ C := fun w wm =>
      (cover w wm).resolve_left (fun wt => none w wt (mem_outN.mp wm).2)
    have := card_le_card s2
    have := qB z zb
    omega
  -- no inner arcs in `B`
  let S := B.filter (fun z => ∃ z' ∈ B, D z' z = true)
  have empty : S = ∅ := by
    by_contra ne
    obtain ⟨s0, hs0⟩ := nonempty_iff_ne_empty.mpr ne
    have sS : S ⊆ V := (filter_subset _ _).trans bV
    have cS : S.card ≤ q := (card_le_card (filter_subset _ _)).trans (by rw [wide]; omega)
    obtain ⟨t, tm, stop⟩ := exists_sink (free.mono_set sS) ⟨s0, hs0⟩ cS
    obtain ⟨tb, z', zb', arc⟩ := mem_filter.mp tm
    have noA : ∀ y ∈ A, D t y ≠ true := fun y ya ty => by
      obtain ⟨σ, -, -, -, none⟩ := key t tb y ya ty
      exact none z' zb' arc
    obtain ⟨w, wb, tw⟩ := headIn t tb B (fun w wm => by
      rcases far t tb w wm with h | h | h
      · exact absurd (mem_outN.mp wm).2 (noA w h)
      · exact Or.inl h
      · exact Or.inr h)
    exact stop w (mem_filter.mpr ⟨wb, t, tb, tw⟩) tw
  have noB : ∀ z ∈ B, ∀ w ∈ B, D z w ≠ true := fun z zb w wb arc => by
    have : w ∈ S := mem_filter.mpr ⟨wb, z, zb, arc⟩
    rw [empty] at this
    exact absurd this (notMem_empty w)
  have pick : ∀ z ∈ B, ∃ σ ∈ A, Sink D A σ ∧ D σ z ≠ true := by
    intro z zb
    obtain ⟨y, ya, zy⟩ := headIn z zb A (fun w wm => by
      rcases far z zb w wm with h | h | h
      · exact Or.inl h
      · exact absurd (mem_outN.mp wm).2 (noB z zb w h)
      · exact Or.inr h)
    obtain ⟨σ, sm, stop, notz, -⟩ := key z zb y ya zy
    exact ⟨σ, sm, stop, notz⟩
  let f : ℕ → ℕ := fun z => if h : z ∈ B then (pick z h).choose else 0
  have fspec : ∀ z ∈ B, f z ∈ A ∧ Sink D A (f z) ∧ D (f z) z ≠ true := by
    intro z zb
    simp only [f, zb, dite_true]
    exact (pick z zb).choose_spec
  obtain ⟨z, zb, z', zb', ne, eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := B) (t := A) (f := f) (by rw [cardA, wide]; omega) (fun z zb => (fspec z zb).1)
  obtain ⟨fa, fs, fz⟩ := fspec z zb
  obtain ⟨-, -, fz'⟩ := fspec z' zb'
  rw [← eq] at fz'
  exact miss (f z) fa fs z zb z' zb' ne fz fz'

#print axioms wide_dip_order
#print axioms unit_dip_false
#print axioms flat_keep
#print axioms flat_sinks
#print axioms layer_host
#print axioms layer_host_order
#print axioms order_one
#print axioms order_two
#print axioms order_of_noHost
#print axioms far_return_free
#print axioms dip_cost
#print axioms flat_root_dip
end LeanCH.BR.DipCost
