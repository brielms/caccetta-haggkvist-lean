import checkpoints.shen_extension.TightWideBanks

/-!
# Layers `r`, `r + 2`, `r - 1`, `≤ r - 1`: the case of a cycle in `Y`

Four consecutive layers `X`, `Y`, `Z`, `W` of a `q`-free graph with `q = r + 1`,
`|X| = r`, `|Y| = r + 2`, `|Z| = r - 1`, `|W| ≤ r - 1` (`Wide2`). Rows of `X`, `Y`, `Z`
have out-degree at least `r`; heads of `X` lie in `X ∪ Y`, of `Y` in `X ∪ Y ∪ Z`, of `Z`
in `X ∪ Y ∪ Z ∪ W`.

If `Y` carries a closed walk of length at most `|Y| = q + 1`, it carries one of length
exactly `q + 1` through every row (`cycle_at`). Reading it backwards from `y`
(`back_labels`) gives `q + 1` distinct rows whose walk to `y` has each length `0..q`.
A row that may not head any of the last `m` of them has at most `|Y| - m` heads in `Y`
(`avoid_card`).

* Every row of `Y` has one head in `Y`.
* A return `y → x` forces `x` to be `(r-2)`-deep in `X` (its sinks omit at most two
  labels), and then `x` has at most two heads in `Y`: impossible for `5 ≤ r`.
* So rows of `Y` head all of `Z`, `Z` cannot return into `Y` or `X`, and `exit_false`
  closes (`cycle_case_false`).
-/

namespace LeanCH.BR.Wide2Cycle
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn TightWideBanks

/-- Layers of widths `r`, `r + 2`, `r - 1`, at most `r - 1` at cutoff `q = r + 1`. -/
structure Wide2 (D : CH.Digraph) (V X Y Z W : Finset ℕ) (q r : ℕ) : Prop where
  free : QFree D V q
  xv : X ⊆ V
  yv : Y ⊆ V
  zv : Z ⊆ V
  cx : X.card = r
  cy : Y.card = r + 2
  cz : Z.card + 1 = r
  cw : W.card + 1 ≤ r
  hq : q = r + 1
  degX : ∀ x ∈ X, r ≤ (outN D V x).card
  degY : ∀ y ∈ Y, r ≤ (outN D V y).card
  degZ : ∀ z ∈ Z, r ≤ (outN D V z).card
  headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y
  headsY : ∀ y ∈ Y, outN D V y ⊆ X ∪ Y ∪ Z
  headsZ : ∀ z ∈ Z, outN D V z ⊆ X ∪ Y ∪ Z ∪ W

section cycle
variable {D : CH.Digraph} {Y : Finset ℕ} {q : ℕ}

/-- A closed walk of length `q + 1` in a `q`-free `Y` with `q + 1` rows passes through
every row, so every row carries one. -/
theorem cycle_at (free : QFree D Y q) (cY : Y.card = q + 1) {a y : ℕ}
    (cyc : Walk D Y a a (q + 1)) (ym : y ∈ Y) : Walk D Y y y (q + 1) := by
  classical
  obtain ⟨f, h0, hm, he⟩ := cyc.toFun
  have hmem : ∀ i, i ≤ q + 1 → f i ∈ Y := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [h0, ← hm]
      exact (he q (by omega)).1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i - 1) (by omega)).1
  have hinj : Set.InjOn f (range (q + 1)) := by
    intro i hi j hj heq
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hij | hji
    · have wc := walk_between he hij.le (by omega : j ≤ q + 1)
      rw [← heq] at wc
      exact free (f i) (j - i) (by omega) (by omega) wc
    · have wc := walk_between he hji.le (by omega : i ≤ q + 1)
      rw [heq] at wc
      exact free (f j) (i - j) (by omega) (by omega) wc
  have hsub : (range (q + 1)).image f ⊆ Y := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact hmem i (by have := mem_range.mp hi; omega)
  have hspan := eq_of_subset_of_card_le hsub (by rw [card_image_of_injOn hinj, card_range, cY])
  obtain ⟨t, tm, rfl⟩ := mem_image.mp (hspan.symm ▸ ym)
  have tl := mem_range.mp tm
  have w1 := walk_between he (by omega : t ≤ q + 1) le_rfl
  have w2 := walk_between he (Nat.zero_le t) (by omega : t ≤ q + 1)
  rw [hm, ← h0] at w1
  have w := w1.append w2
  rwa [show q + 1 - t + (t - 0) = q + 1 by omega] at w

/-- Reading a closed walk of length `q + 1` at `y` backwards: rows `f t` (`t ≤ q + 1`)
of `Y` with a walk of length `q + 1 - t` to `y`, distinct for `1 ≤ t`. -/
theorem back_labels (free : QFree D Y q) {y : ℕ} (cyc : Walk D Y y y (q + 1)) :
    ∃ f : ℕ → ℕ, (∀ t ≤ q + 1, f t ∈ Y) ∧ (∀ t ≤ q + 1, Walk D Y (f t) y (q + 1 - t)) ∧
      Set.InjOn f (Icc 1 (q + 1)) := by
  obtain ⟨f, h0, hm, he⟩ := cyc.toFun
  refine ⟨f, fun t tl => ?_, fun t tl => ?_, ?_⟩
  · by_cases t0 : t = 0
    · subst t0
      rw [h0, ← hm]
      exact (he q (by omega)).1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using (he (t - 1) (by omega)).1
  · have w := walk_between he tl le_rfl
    rwa [hm] at w
  · intro i hi j hj heq
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hij | hji
    · have wc := walk_between he hij.le hj.2
      rw [← heq] at wc
      exact free (f i) (j - i) (by omega) (by omega) wc
    · have wc := walk_between he hji.le hi.2
      rw [heq] at wc
      exact free (f j) (i - j) (by omega) (by omega) wc

/-- A row that heads none of `f t` for `s ≤ t ≤ n` has at most `|Y| - (n + 1 - s)` heads
in `Y`. -/
theorem avoid_card {f : ℕ → ℕ} {n s v : ℕ} (cY : Y.card = n) (mem : ∀ t ≤ n, f t ∈ Y)
    (inj : Set.InjOn f (Icc 1 n)) (lo : 1 ≤ s)
    (avoid : ∀ t, s ≤ t → t ≤ n → D v (f t) ≠ true) :
    (outN D Y v).card + (n + 1 - s) ≤ n := by
  classical
  let S := (Icc s n).image f
  have cardS : S.card = n + 1 - s := by
    rw [card_image_of_injOn (inj.mono (by
      intro t ht; simp only [coe_Icc, Set.mem_Icc] at ht ⊢; omega)), Nat.card_Icc]
  have disj : Disjoint (outN D Y v) S := by
    rw [disjoint_left]
    intro a ha aS
    obtain ⟨t, tm, rfl⟩ := mem_image.mp aS
    obtain ⟨t1, t2⟩ := mem_Icc.mp tm
    exact avoid t t1 t2 (mem_outN.mp ha).2
  have sub : outN D Y v ∪ S ⊆ Y := by
    refine union_subset outN_subset (fun a aS => ?_)
    obtain ⟨t, tm, rfl⟩ := mem_image.mp aS
    exact mem _ (mem_Icc.mp tm).2
  have := card_le_card sub
  rw [card_union_of_disjoint disj, cardS, cY] at this
  exact this

end cycle

/-- **Case 1: `Y` carries a cycle.** -/
theorem cycle_case_false {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}
    (w : Wide2 D V X Y Z W q r) (five : 5 ≤ r) (cyc : ¬ QFree D Y (r + 2)) : False := by
  classical
  have hq := w.hq
  have fY : QFree D Y q := w.free.mono_set w.yv
  have fx := w.free.mono_set w.xv
  have sx : X.card ≤ q := by have := w.cx; omega
  have cY : Y.card = q + 1 := by have := w.cy; omega
  simp only [QFree, not_forall, not_not] at cyc
  obtain ⟨a, ℓ, h1, hl, walk⟩ := cyc
  have ℓe : ℓ = q + 1 := by
    by_contra ne
    exact fY a ℓ h1 (by omega) walk
  subst ℓe
  -- every row of `Y` has at most one head in `Y`
  have oneY (y) (ym : y ∈ Y) : (outN D Y y).card ≤ 1 := by
    obtain ⟨f, fm, fw, finj⟩ := back_labels fY (cycle_at fY cY walk ym)
    have := avoid_card cY fm finj (s := 2) (by omega) (fun t t2 tn arc =>
      w.free y (q + 1 - t + 1) (by omega) (by omega)
        (Walk.step (w.yv (fm t tn)) arc ((fw t tn).mono w.yv)))
    omega
  -- `Y` does not return into `X`
  have noRet (y) (ym : y ∈ Y) (x) (xm : x ∈ X) (yx : D y x = true) : False := by
    obtain ⟨f, fm, fw, finj⟩ := back_labels fY (cycle_at fY cY walk ym)
    have deep : Deep D X (r - 2) x := by
      intro s sm ks k wk
      by_contra! short
      have sub : outN D V s ⊆ outN D Y s := by
        intro z hz
        rcases mem_union.mp (w.headsX s sm hz) with zx | zy
        · exact (ks z zx (mem_outN.mp hz).2).elim
        · exact mem_outN.mpr ⟨zy, (mem_outN.mp hz).2⟩
      have deg := (w.degX s sm).trans (card_le_card sub)
      have := avoid_card cY fm finj (s := k + 3) (by omega) (fun t t1 tn arc =>
        w.free x (k + (q + 1 - t + 1) + 1) (by omega) (by omega)
          (((wk.mono w.xv).append (Walk.step (w.yv (fm t tn)) arc ((fw t tn).mono w.yv))).snoc
            (w.xv xm) yx))
      omega
    have inner := deep_heads fx sx xm deep
    have av := avoid_card cY fm finj (s := 3) (v := x) (by omega) (fun t t1 tn arc =>
      w.free x (q + 1 - t + 1 + 1) (by omega) (by omega)
        ((Walk.step (w.yv (fm t tn)) arc ((fw t tn).mono w.yv)).snoc (w.xv xm) yx))
    have split : outN D V x ⊆ outN D X x ∪ outN D Y x := by
      intro z hz
      have arc := (mem_outN.mp hz).2
      rcases mem_union.mp (w.headsX x xm hz) with zx | zy
      · exact mem_union_left _ (mem_outN.mpr ⟨zx, arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨zy, arc⟩)
    have := (card_le_card split).trans (card_union_le _ _)
    have := w.degX x xm
    have := w.cx
    omega
  -- so every row of `Y` heads all of `Z`
  have fullY (y) (ym : y ∈ Y) : Z ⊆ outN D V y := by
    have split : outN D V y ⊆ outN D Y y ∪ outN D Z y := by
      intro z hz
      have arc := (mem_outN.mp hz).2
      rcases mem_union.mp (w.headsY y ym hz) with zxy | zz
      · rcases mem_union.mp zxy with zx | zy
        · exact (noRet y ym z zx arc).elim
        · exact mem_union_left _ (mem_outN.mpr ⟨zy, arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨zz, arc⟩)
    have := (card_le_card split).trans (card_union_le _ _)
    have := w.degY y ym
    have := oneY y ym
    have := w.cz
    have eq := eq_of_subset_of_card_le (outN_subset (D := D) (W := Z) (y := y)) (by omega)
    intro z zm
    have zo : z ∈ outN D Z y := by rw [eq]; exact zm
    exact mem_outN.mpr ⟨w.zv zm, (mem_outN.mp zo).2⟩
  -- rows of `Z` head only `Z ∪ W`
  have heads (z) (zm : z ∈ Z) : outN D V z ⊆ Z ∪ W ∪ ∅ := by
    intro h hh
    have arc := (mem_outN.mp hh).2
    rcases mem_union.mp (w.headsZ z zm hh) with hxyz | hw
    · rcases mem_union.mp hxyz with hxy | hz
      · rcases mem_union.mp hxy with hx | hy
        · exfalso
          have deep : Deep D X (r - 1) h := by
            intro s sm ks k wk
            by_contra! short
            obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (outN D V s).card by have := w.degX s sm; omega)
            have ym : y ∈ Y := by
              rcases mem_union.mp (w.headsX s sm hy) with yx | yy
              · exact (ks y yx (mem_outN.mp hy).2).elim
              · exact yy
            exact w.free h (k + 1 + 1 + 1) (by omega) (by omega)
              ((((wk.mono w.xv).snoc (w.yv ym) (mem_outN.mp hy).2).snoc (w.zv zm)
                (mem_outN.mp (fullY y ym zm)).2).snoc (w.xv hx) arc)
          have inner := deep_heads fx sx hx deep
          obtain ⟨y, hy, ym⟩ : ∃ y ∈ outN D V h, y ∈ Y := by
            by_contra! none
            have sub : outN D V h ⊆ outN D X h := by
              intro u hu
              rcases mem_union.mp (w.headsX h hx hu) with ux | uy
              · exact mem_outN.mpr ⟨ux, (mem_outN.mp hu).2⟩
              · exact (none u hu uy).elim
            have := card_le_card sub
            have := w.degX h hx
            have := w.cx
            omega
          exact w.free h 3 (by omega) (by omega) (.step (w.yv ym) (mem_outN.mp hy).2
            (.step (w.zv zm) (mem_outN.mp (fullY y ym zm)).2 (.step (w.xv hx) arc (.refl h))))
        · exact (w.free z 2 (by omega) (by omega) (.step (w.yv hy) arc
            (.step (w.zv zm) (mem_outN.mp (fullY h hy zm)).2 (.refl z)))).elim
      · exact mem_union_left _ (mem_union_left _ hz)
    · exact mem_union_left _ (mem_union_right _ hw)
  have := w.cz
  exact exit_false w.free w.zv (empty_subset _) (by omega) (by omega) (by omega) w.cw w.degZ
    (by simp) (by simp) heads

#print axioms cycle_at
#print axioms back_labels
#print axioms avoid_card
#print axioms cycle_case_false

end LeanCH.BR.Wide2Cycle
