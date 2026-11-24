import checkpoints.shen_extension.TightLayerShapes

/-!
# Three full layers in front: no return from the fourth layer

Layers `U`, `W`, `X` of width `r` in front of a row `y` with a parent chain
`p' → p → y`, `p' ∈ W`, `p ∈ X`, at cutoff `q ≥ r + 1`. Rows of `U` head only `U ∪ W`,
rows of `W` only `U ∪ W ∪ X`.

* `front3_no_return`: `y` has no head in `U` once `5 ≤ r`. A return target `u` is
  `(q - 3)`-deep in `U` (route through a `U`-sink, which heads all of `W`), so it has at
  least `r - 2 ≥ 3` heads in `W`. At most two rows of `W` are `(q - 3)`-deep, so `u`
  heads a row `w` of `W` within `q - 4` steps of a `W`-sink, and that sink heads `p`
  (a `W`-sink heads all of `X`). The closed walk `u → w ⇝ sink → p → y → u` has length
  at most `q`.
* `front3_tight_false`: layers of widths `r`, `r`, `r`, `r + 1`, `≤ r - 1` are impossible
  for `5 ≤ r`, `r + 1 ≤ q`. This sharpens `TightLayerShapes.full_front3_false`
  (which needs `≤ r - 3`) by two.

Generic in `r` and `q`.
-/

namespace LeanCH.BR.ExcessStepFront
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn TightLayerShapes

/-- Rows of `W` never return into `U`, and every `W`-sink heads all of `X`, when `U`, `W`,
`X` are full layers of width `r`. -/
theorem front_full {D : CH.Digraph} {V U W X : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (wv : W ⊆ V)
    (cu : U.card = r) (cw : W.card = r) (cx : X.card = r) (time : r + 1 ≤ q)
    (degU : ∀ a ∈ U, r ≤ (outN D V a).card) (degW : ∀ a ∈ W, r ≤ (outN D V a).card)
    (headsU : ∀ a ∈ U, outN D V a ⊆ U ∪ W) (headsW : ∀ a ∈ W, outN D V a ⊆ U ∪ W ∪ X) :
    (∀ a ∈ W, outN D V a ⊆ W ∪ X) ∧ (∀ s ∈ W, Sink D W s → X ⊆ outN D V s) := by
  have fullU (s) (sm : s ∈ U) (ks : Sink D U s) : W ⊆ outN D V s :=
    sink_full (headsU s sm) ks (degU s sm) cw
  have headsW' (a) (am : a ∈ W) : outN D V a ⊆ W ∪ X := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsW a am hz) with zuw | zx
    · rcases mem_union.mp zuw with zu | zw
      · exact (next_return_false free uv wv cu.le time fullU am zu arc).elim
      · exact mem_union_left _ zw
    · exact mem_union_right _ zx
  exact ⟨headsW', fun s sm ks => sink_full (headsW' s sm) ks (degW s sm) cx⟩

/-- **No return from the fourth layer.** -/
theorem front3_no_return {D : CH.Digraph} {V U W X : Finset ℕ} {q r y u p p' : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (wv : W ⊆ V) (xv : X ⊆ V) (yv : y ∈ V)
    (cu : U.card = r) (cw : W.card = r) (cx : X.card = r) (five : 5 ≤ r) (time : r + 1 ≤ q)
    (degU : ∀ a ∈ U, r ≤ (outN D V a).card) (degW : ∀ a ∈ W, r ≤ (outN D V a).card)
    (headsU : ∀ a ∈ U, outN D V a ⊆ U ∪ W) (headsW : ∀ a ∈ W, outN D V a ⊆ U ∪ W ∪ X)
    (pm : p ∈ X) (py : D p y = true) (p'm : p' ∈ W) (p'p : D p' p = true)
    (um : u ∈ U) (ret : D y u = true) : False := by
  classical
  have fu := free.mono_set uv
  have fw := free.mono_set wv
  have su : U.card ≤ q := by omega
  have sw : W.card ≤ q := by omega
  have fullU (s) (sm : s ∈ U) (ks : Sink D U s) : W ⊆ outN D V s :=
    sink_full (headsU s sm) ks (degU s sm) cw
  obtain ⟨-, fullW⟩ := front_full free uv wv cu cw cx time degU degW headsU headsW
  -- `u` is `(q - 3)`-deep in `U`
  have deep : Deep D U (q - 3) u := return_deep free uv um (fun s sm ks => Walk.step (wv p'm)
    (mem_outN.mp (fullU s sm ks p'm)).2 (Walk.step (xv pm) p'p (Walk.step yv py (.refl y)))) ret
  have inner := deep_heads fu su um deep
  have split : outN D V u ⊆ outN D U u ∪ outN D W u := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsU u um hz) with zu | zw
    · exact mem_union_left _ (mem_outN.mpr ⟨zu, arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨zw, arc⟩)
  have heads := (card_le_card split).trans (card_union_le _ _)
  have degu := degU u um
  -- few deep rows in `W`
  have few : (W.filter (Deep D W (q - 3))).card ≤ 2 := by
    rcases deep_card (t := q - 3) fw sw with bound | empty
    · omega
    · rw [empty]; simp
  obtain ⟨w, wm, shallow⟩ : ∃ w ∈ outN D W u, w ∉ W.filter (Deep D W (q - 3)) := by
    by_contra! all
    have := card_le_card (show outN D W u ⊆ W.filter (Deep D W (q - 3)) from all)
    omega
  obtain ⟨wW, uw⟩ := mem_outN.mp wm
  have nd : ¬ Deep D W (q - 3) w := fun d => shallow (mem_filter.mpr ⟨wW, d⟩)
  simp only [Deep, not_forall, not_le, exists_prop] at nd
  obtain ⟨s, sm, ks, k, walk, lt⟩ := nd
  exact free u _ (by omega) (by omega)
    (Walk.step (wv wW) uw ((walk.mono wv).append
      (Walk.step (xv pm) (mem_outN.mp (fullW s sm ks pm)).2
        (Walk.step yv py (Walk.step (uv um) ret (.refl u))))))

/-- **Widths `r`, `r`, `r`, `r + 1`, `≤ r - 1`.** -/
theorem front3_tight_false {D : CH.Digraph} {V U W X Y Z : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (wv : W ⊆ V) (xv : X ⊆ V) (yv : Y ⊆ V)
    (cu : U.card = r) (cw : W.card = r) (cx : X.card = r) (cy : Y.card = r + 1)
    (cz : Z.card + 1 ≤ r) (five : 5 ≤ r) (time : r + 1 ≤ q)
    (degU : ∀ a ∈ U, r ≤ (outN D V a).card) (degW : ∀ a ∈ W, r ≤ (outN D V a).card)
    (degX : ∀ x ∈ X, r ≤ (outN D V x).card) (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (headsU : ∀ a ∈ U, outN D V a ⊆ U ∪ W) (headsW : ∀ a ∈ W, outN D V a ⊆ U ∪ W ∪ X)
    (headsX : ∀ x ∈ X, outN D V x ⊆ U ∪ W ∪ X ∪ Y)
    (headsY : ∀ y ∈ Y, outN D V y ⊆ U ∪ W ∪ X ∪ Y ∪ Z)
    (parentX : ∀ x ∈ X, ∃ p ∈ W, D p x = true)
    (parentY : ∀ y ∈ Y, ∃ p ∈ X, D p y = true) : False := by
  classical
  obtain ⟨headsW', fullW⟩ := front_full free uv wv cu cw cx time degU degW headsU headsW
  have headsX' (x) (xm : x ∈ X) : outN D V x ⊆ W ∪ X ∪ Y := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsX x xm hz) with zuwx | zy
    · rcases mem_union.mp zuwx with zuw | zx
      · rcases mem_union.mp zuw with zu | zw
        · exact (skip_return_false free uv wv (xv xm) cu cw (by omega) time degU headsU
            (fun s sm ks => (mem_outN.mp (fullW s sm ks xm)).2) (parentX x xm) zu arc).elim
        · exact mem_union_left _ (mem_union_left _ zw)
      · exact mem_union_left _ (mem_union_right _ zx)
    · exact mem_union_right _ zy
  have headsY' (y) (ym : y ∈ Y) : outN D V y ⊆ W ∪ X ∪ Y ∪ Z := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsY y ym hz) with zuwxy | zz
    · rcases mem_union.mp zuwxy with zuwx | zy
      · rcases mem_union.mp zuwx with zuw | zx
        · rcases mem_union.mp zuw with zu | zw
          · obtain ⟨p, pm, py⟩ := parentY y ym
            obtain ⟨p', p'm, p'p⟩ := parentX p pm
            exact (front3_no_return free uv wv xv (yv ym) cu cw cx five time degU degW
              headsU headsW pm py p'm p'p zu arc).elim
          · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zw))
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zx))
      · exact mem_union_left _ (mem_union_right _ zy)
    · exact mem_union_right _ zz
  exact full_front_tight_false free wv xv yv cw cx cy cz (by omega) time
    degW degX degY headsW' headsX' headsY' parentY

#print axioms front_full
#print axioms front3_no_return
#print axioms front3_tight_false

end LeanCH.BR.ExcessStepFront
