import checkpoints.shen_extension.WideLayerReturn

/-!
# More layer shapes around a wide layer

Generic in `r` and `q`.

* `parent_nonempty`: a layer whose rows all have parents in an earlier layer forces
  that earlier layer to be nonempty.
* `sink_full`: a sink of a full layer of width-`r` successors heads the whole next layer.
* `skip_return_false`: with two full layers `A`, `B` in front, no row with a `B`-parent
  that every `B`-sink heads can return into `A`.
* `full_front3_false`: three full layers of width `r`, then `r + 1`, then at most
  `r - 3`, cannot follow one another (`3 ≤ r`, `r + 1 ≤ q`).
-/

namespace LeanCH.BR.TightLayerShapes
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn

/-- **Parents.** If every row of `Y` has a parent in `X` and `Y` is nonempty, so is `X`. -/
theorem parent_nonempty {D : CH.Digraph} {X Y : Finset ℕ}
    (parent : ∀ y ∈ Y, ∃ p ∈ X, D p y = true) (ne : Y.Nonempty) : X.Nonempty := by
  obtain ⟨y, ym⟩ := ne
  obtain ⟨p, pm, _⟩ := parent y ym
  exact ⟨p, pm⟩

/-- A sink of `A` whose heads lie in `A ∪ B`, with at least `|B|` heads, heads all of `B`. -/
theorem sink_full {D : CH.Digraph} {V A B : Finset ℕ} {a r : ℕ}
    (heads : outN D V a ⊆ A ∪ B) (ka : Sink D A a) (deg : r ≤ (outN D V a).card)
    (cb : B.card = r) : B ⊆ outN D V a := by
  have sub : outN D V a ⊆ B := by
    intro z hz
    rcases mem_union.mp (heads hz) with za | zb
    · exact (ka z za (mem_outN.mp hz).2).elim
    · exact zb
  exact (eq_of_subset_of_card_le sub (by rw [cb]; exact deg)).symm.subset

/-- A row `w` of a layer `B` whose `A`-sinks head all of `B` cannot return into `A` when
`A` has at most `r` rows, `r < q`, and every row of `A` reaches an `A`-sink inside `A`. -/
theorem next_return_false {D : CH.Digraph} {V A B : Finset ℕ} {q r w u : ℕ}
    (free : QFree D V q) (av : A ⊆ V) (bv : B ⊆ V) (ca : A.card ≤ r) (time : r + 1 ≤ q)
    (fullA : ∀ s ∈ A, Sink D A s → B ⊆ outN D V s) (wm : w ∈ B) (um : u ∈ A)
    (ret : D w u = true) : False := by
  have fa := free.mono_set av
  have deep := return_deep_next (l := 0) free av bv um fullA wm (.refl w) ret
  obtain ⟨s, sm, stop, m, ml, walk⟩ := reach_sink_of_card fa (by omega) um
  have := deep s sm (fun z zm => stop z zm) m walk
  omega

/-- **No skipped return.** Two layers `A`, `B` of width `r` in front of a row `x`: the
`A`-sinks head all of `B`, every `B`-sink heads `x`, and `x` has a parent in `B`.
Then `x` has no head in `A`. A return target `u` would be `(q-2)`-deep, so it heads all
of `B` but the single `B`-parent `p₀` of `x`; then `p₀` is the only `B`-sink, and a
`B`-parent of `p₀` closes the four-cycle `u → w' → p₀ → x → u`. -/
theorem skip_return_false {D : CH.Digraph} {V A B : Finset ℕ} {q r x u : ℕ}
    (free : QFree D V q) (av : A ⊆ V) (bv : B ⊆ V) (xv : x ∈ V)
    (ca : A.card = r) (cb : B.card = r) (three : 3 ≤ r) (time : r + 1 ≤ q)
    (degA : ∀ a ∈ A, r ≤ (outN D V a).card) (headsA : ∀ a ∈ A, outN D V a ⊆ A ∪ B)
    (fullB : ∀ s ∈ B, Sink D B s → D s x = true)
    (parent : ∃ p ∈ B, D p x = true) (um : u ∈ A) (ret : D x u = true) : False := by
  classical
  have fa := free.mono_set av
  have fb := free.mono_set bv
  have sa : A.card ≤ q := by omega
  have sb : B.card ≤ q := by omega
  have q1 : 1 ≤ q := by omega
  have fullA (s) (sm : s ∈ A) (ks : Sink D A s) : B ⊆ outN D V s :=
    sink_full (headsA s sm) ks (degA s sm) cb
  obtain ⟨p₀, p₀m, p₀x⟩ := parent
  have deep : Deep D A (q - 2) u := return_deep free av um (fun s sm ks =>
    Walk.step (bv p₀m) (mem_outN.mp (fullA s sm ks p₀m)).2 (Walk.step xv p₀x (.refl x))) ret
  have inner := deep_heads fa sa um deep
  have split : outN D V u ⊆ outN D A u ∪ outN D B u := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsA u um hz) with za | zb
    · exact mem_union_left _ (mem_outN.mpr ⟨za, arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨zb, arc⟩)
  have heads := (card_le_card split).trans (card_union_le _ _)
  have degu := degA u um
  -- `u` heads no `B`-parent of `x`
  have avoid (b) (bm : b ∈ B) (bx : D b x = true) (ub : D u b = true) : False :=
    free u 3 (by omega) (by omega)
      (Walk.step (bv bm) ub (Walk.step xv bx (Walk.step (av um) ret (.refl u))))
  have sub : outN D B u ⊆ B.erase p₀ := fun z hz =>
    mem_erase.mpr ⟨fun e => avoid p₀ p₀m p₀x (e ▸ (mem_outN.mp hz).2), (mem_outN.mp hz).1⟩
  have eq := eq_of_subset_of_card_le sub (by rw [card_erase_of_mem p₀m, cb]; omega)
  have allB (b) (bm : b ∈ B) (ne : b ≠ p₀) : D u b = true :=
    (mem_outN.mp (eq.symm ▸ mem_erase.mpr ⟨ne, bm⟩ : b ∈ outN D B u)).2
  -- so `p₀` is the only `B`-sink
  have only (s) (sm : s ∈ B) (ks : Sink D B s) : s = p₀ := by
    by_contra ne
    exact avoid s sm (fullB s sm ks) (allB s sm ne)
  obtain ⟨b, bm, bne⟩ := exists_mem_ne (show 1 < B.card by omega) p₀
  obtain ⟨s, sm, stop, m, _, walk⟩ := reach_sink_of_card fb sb bm
  have sp := only s sm (fun z zm => stop z zm)
  subst sp
  obtain ⟨w', w'm, arc⟩ := last_parent bm walk bne
  have ne : w' ≠ s := fun e => loopfree free q1 (bv w'm) (e ▸ arc)
  exact free u 4 (by omega) (by omega) (Walk.step (bv w'm) (allB w' w'm ne)
    (Walk.step (bv sm) arc (Walk.step xv p₀x (Walk.step (av um) ret (.refl u)))))

/-- **Three full layers in front.** Layers `U`, `W`, `X`, `Y`, `Z` of widths `r`, `r`, `r`,
`r + 1` and at most `r - 3`, with `3 ≤ r` and `r + 1 ≤ q`. Rows of each layer head only
their own and earlier layers and the next one, every row of `X` has a parent in `W` and
every row of `Y` has a parent in `X`. Then `W` and `X` do not return into `U`, returns
from `Y` into `U` land on the at most two `(q-3)`-deep rows of `U`, and
`full_front_tight_false` applies to `W`, `X`, `Y` with those rows added to `Z`. -/
theorem full_front3_false {D : CH.Digraph} {V U W X Y Z : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (wv : W ⊆ V) (xv : X ⊆ V) (yv : Y ⊆ V)
    (cu : U.card = r) (cw : W.card = r) (cx : X.card = r) (cy : Y.card = r + 1)
    (cz : Z.card + 3 ≤ r) (three : 3 ≤ r) (time : r + 1 ≤ q)
    (degU : ∀ a ∈ U, r ≤ (outN D V a).card) (degW : ∀ a ∈ W, r ≤ (outN D V a).card)
    (degX : ∀ x ∈ X, r ≤ (outN D V x).card) (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (headsU : ∀ a ∈ U, outN D V a ⊆ U ∪ W) (headsW : ∀ a ∈ W, outN D V a ⊆ U ∪ W ∪ X)
    (headsX : ∀ x ∈ X, outN D V x ⊆ U ∪ W ∪ X ∪ Y)
    (headsY : ∀ y ∈ Y, outN D V y ⊆ U ∪ W ∪ X ∪ Y ∪ Z)
    (parentX : ∀ x ∈ X, ∃ p ∈ W, D p x = true)
    (parentY : ∀ y ∈ Y, ∃ p ∈ X, D p y = true) : False := by
  classical
  have fu := free.mono_set uv
  have su : U.card ≤ q := by omega
  have fullU (s) (sm : s ∈ U) (ks : Sink D U s) : W ⊆ outN D V s :=
    sink_full (headsU s sm) ks (degU s sm) cw
  -- `W` does not return into `U`
  have headsW' (a) (am : a ∈ W) : outN D V a ⊆ W ∪ X := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsW a am hz) with zuw | zx
    · rcases mem_union.mp zuw with zu | zw
      · exact (next_return_false free uv wv cu.le time fullU am zu arc).elim
      · exact mem_union_left _ zw
    · exact mem_union_right _ zx
  have fullW (s) (sm : s ∈ W) (ks : Sink D W s) : X ⊆ outN D V s :=
    sink_full (headsW' s sm) ks (degW s sm) cx
  -- `X` does not return into `U`
  have headsX' (x) (xm : x ∈ X) : outN D V x ⊆ W ∪ X ∪ Y := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsX x xm hz) with zuwx | zy
    · rcases mem_union.mp zuwx with zuw | zx
      · rcases mem_union.mp zuw with zu | zw
        · exact (skip_return_false free uv wv (xv xm) cu cw three time degU headsU
            (fun s sm ks => (mem_outN.mp (fullW s sm ks xm)).2) (parentX x xm) zu arc).elim
        · exact mem_union_left _ (mem_union_left _ zw)
      · exact mem_union_left _ (mem_union_right _ zx)
    · exact mem_union_right _ zy
  -- returns from `Y` into `U` are `(q-3)`-deep
  have headsY' (y) (ym : y ∈ Y) : outN D V y ⊆ W ∪ X ∪ Y ∪ (Z ∪ U.filter (Deep D U (q - 3))) := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (headsY y ym hz) with zuwxy | zz
    · rcases mem_union.mp zuwxy with zuwx | zy
      · rcases mem_union.mp zuwx with zuw | zx
        · rcases mem_union.mp zuw with zu | zw
          · obtain ⟨p, pm, py⟩ := parentY y ym
            obtain ⟨p', p'm, p'p⟩ := parentX p pm
            refine mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨zu, ?_⟩))
            exact return_deep free uv zu (fun s sm ks => Walk.step (wv p'm)
              (mem_outN.mp (fullU s sm ks p'm)).2 (Walk.step (xv pm) p'p
                (Walk.step (yv ym) py (.refl y)))) arc
          · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zw))
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zx))
      · exact mem_union_left _ (mem_union_right _ zy)
    · exact mem_union_right _ (mem_union_left _ zz)
  have few : (U.filter (Deep D U (q - 3))).card ≤ 2 := by
    rcases deep_card (t := q - 3) fu su with bound | empty
    · omega
    · rw [empty]; simp
  have cz' : (Z ∪ U.filter (Deep D U (q - 3))).card + 1 ≤ r := by
    have := card_union_le Z (U.filter (Deep D U (q - 3)))
    omega
  exact WideLayerReturn.full_front_tight_false free wv xv yv cw cx cy cz' three time
    degW degX degY headsW' headsX' headsY' parentY

#print axioms full_front3_false
#print axioms parent_nonempty
#print axioms sink_full
#print axioms next_return_false
#print axioms skip_return_false

end LeanCH.BR.TightLayerShapes
