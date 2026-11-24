import checkpoints.shen_extension.ExcessStepFront
import checkpoints.shen_extension.LayerExcess

/-!
# Shifted peel behind three full layers

Layers `U`, `W`, `X` of width `r`, then `Y` (any width `a`) and `Z`, at cutoff `q ≥ r + 1`,
`5 ≤ r`. By `next_return_false`, `skip_return_false` and `front3_no_return`, none of
`W`, `X`, `Y` returns into `U`. So the union `S = W ∪ X ∪ Y` keeps at least
`t = r - |Z|` heads per row, and `NoHost q t` forces `|S| = 2r + a > q · t`.

* `peel_core`: a nonempty set whose rows all keep `t` heads inside it, outside a set `Z`
  with `|Z| + t ≤ r`, has more than `q · t` labels under `NoHost q t`.
* `front3_peel_false`: widths `r`, `r`, `r`, `a`, `≤ r - t` are impossible when
  `2r + a ≤ q · t`. At `q = r + 1`, `t = 3`, `a = r + 2` this is the profile
  `(r, r, r, r + 2, ≤ r - 3)`.

Generic in `r`, `q`, `a` and `t`.
-/

namespace LeanCH.BR.ExcessStepPeel
open Finset BRq2 BRq3 BypassRepair SinkReturnAncestors SinkDepthReturn WideLayerReturn
open TightLayerShapes ExcessStepFront

/-- **Peel core.** -/
theorem peel_core {D : CH.Digraph} {V S Z : Finset ℕ} {q r t : ℕ}
    (free : QFree D V q) (sv : S ⊆ V) (ne : S.Nonempty) (lower : NoHost q t)
    (cz : Z.card + t ≤ r) (deg : ∀ v ∈ S, r ≤ (outN D V v).card)
    (heads : ∀ v ∈ S, outN D V v ⊆ S ∪ Z) : q * t < S.card := by
  by_contra! small
  refine lower D S ne small (free.mono_set sv) (fun v vm => ?_)
  have sub : outN D V v ⊆ outN D S v ∪ Z := by
    intro w hw
    rcases mem_union.mp (heads v vm hw) with ws | wz
    · exact mem_union_left _ (mem_outN.mpr ⟨ws, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ wz
  have := (card_le_card sub).trans (card_union_le _ _)
  have := deg v vm
  omega

/-- **Three full layers, then a peel.** -/
theorem front3_peel_false {D : CH.Digraph} {V U W X Y Z : Finset ℕ} {q r a t : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (wv : W ⊆ V) (xv : X ⊆ V) (yv : Y ⊆ V)
    (cu : U.card = r) (cw : W.card = r) (cx : X.card = r) (cy : Y.card = a)
    (cz : Z.card + t ≤ r) (five : 5 ≤ r) (time : r + 1 ≤ q)
    (lower : NoHost q t) (size : 2 * r + a ≤ q * t)
    (degU : ∀ v ∈ U, r ≤ (outN D V v).card) (degW : ∀ v ∈ W, r ≤ (outN D V v).card)
    (degX : ∀ v ∈ X, r ≤ (outN D V v).card) (degY : ∀ v ∈ Y, r ≤ (outN D V v).card)
    (headsU : ∀ v ∈ U, outN D V v ⊆ U ∪ W) (headsW : ∀ v ∈ W, outN D V v ⊆ U ∪ W ∪ X)
    (headsX : ∀ v ∈ X, outN D V v ⊆ U ∪ W ∪ X ∪ Y)
    (headsY : ∀ v ∈ Y, outN D V v ⊆ U ∪ W ∪ X ∪ Y ∪ Z)
    (parentX : ∀ x ∈ X, ∃ p ∈ W, D p x = true)
    (parentY : ∀ y ∈ Y, ∃ p ∈ X, D p y = true) : False := by
  classical
  obtain ⟨headsW', fullW⟩ := front_full free uv wv cu cw cx time degU degW headsU headsW
  have noX (x) (xm : x ∈ X) (z) (zu : z ∈ U) (arc : D x z = true) : False :=
    skip_return_false free uv wv (xv xm) cu cw (by omega) time degU headsU
      (fun s sm ks => (mem_outN.mp (fullW s sm ks xm)).2) (parentX x xm) zu arc
  have noY (y) (ym : y ∈ Y) (z) (zu : z ∈ U) (arc : D y z = true) : False := by
    obtain ⟨p, pm, py⟩ := parentY y ym
    obtain ⟨p', p'm, p'p⟩ := parentX p pm
    exact front3_no_return free uv wv xv (yv ym) cu cw cx five time degU degW
      headsU headsW pm py p'm p'p zu arc
  have big := peel_core (S := W ∪ X ∪ Y) (Z := Z) free
    (union_subset (union_subset wv xv) yv)
    (by
      obtain ⟨w, wm⟩ := card_pos.mp (show 0 < W.card by omega)
      exact ⟨w, mem_union_left _ (mem_union_left _ wm)⟩)
    lower cz
    (fun v vm => by
      rcases mem_union.mp vm with vwx | vy
      · rcases mem_union.mp vwx with vw | vx
        · exact degW v vw
        · exact degX v vx
      · exact degY v vy)
    (fun v vm => by
      intro z hz
      have arc := (mem_outN.mp hz).2
      rcases mem_union.mp vm with vwx | vy
      · rcases mem_union.mp vwx with vw | vx
        · rcases mem_union.mp (headsW' v vw hz) with zw | zx
          · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zw))
          · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zx))
        · rcases mem_union.mp (headsX v vx hz) with h | zy
          · rcases mem_union.mp h with h | zx
            · rcases mem_union.mp h with zu | zw
              · exact (noX v vx z zu arc).elim
              · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zw))
            · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zx))
          · exact mem_union_left _ (mem_union_right _ zy)
      · rcases mem_union.mp (headsY v vy hz) with h | zz
        · rcases mem_union.mp h with h | zy
          · rcases mem_union.mp h with h | zx
            · rcases mem_union.mp h with zu | zw
              · exact (noY v vy z zu arc).elim
              · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zw))
            · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zx))
          · exact mem_union_left _ (mem_union_right _ zy)
        · exact mem_union_right _ zz)
  have c1 := card_union_le (W ∪ X) Y
  have c2 := card_union_le W X
  omega

#print axioms peel_core
#print axioms front3_peel_false

end LeanCH.BR.ExcessStepPeel
