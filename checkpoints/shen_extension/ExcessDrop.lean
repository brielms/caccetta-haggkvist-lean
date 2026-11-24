import checkpoints.shen_extension.FrontLayers

/-!
# An excess `e` that is cancelled at once

Layers `X = L h` (width `r`), `Y = L (h+1)` (width `r + e`), `Z = L (h+2)` (width at most
`r - e`) in a `q`-free graph, with the layer facts of `FrontLayers.Layers`. For
`1 ≤ e`, `r + h ≤ q` and `r + e + 1 ≤ q` this is impossible (`excess_drop_false`).
For `e = 1` this is `FrontLayers.front_false` (there with `3 ≤ r`, `r + 1 ≤ q`).

The core (`drop_false`) only uses: `|X| = r`, `|Y| = r + e`, rows of `X` have out-degree
`≥ r` and head only `X ∪ Y`, rows of `Y` have `≥ e` heads in `X ∪ Y`.

* (1) `sink_omits_e`: an `X`-sink heads only `Y` and omits at most `e` rows of `Y`.
* (2) `omitted_ancestor`: if `b ∈ Y` reaches a returning row `y → x` and `x` reaches the
  `X`-sink `σ`, with total closed length at most `q`, then `σ` does not head `b`.
* (3) `chain_false`: a `Y`-walk with `e` arcs ending at a returning row is impossible
  (its `e + 1` distinct rows would all be omitted by one sink); `walks_short`: every walk
  inside `Y` has fewer than `e` arcs.
* `reach_count`: hence every row of `Y` reaches at least `e` rows of `X` by walks of at
  most `e` arcs (induction on the height in `Y`).
* `target_count`: every row of `X` is reached that way from at most `e` rows of `Y`
  (they are all omitted by a sink below it).
* Double counting: `(r + e) · e ≤ r · e`, impossible for `e ≥ 1`. No case split on the
  number of sinks of `X` is needed.

Generic in `r`, `q`, `h`, `e`.
-/

namespace LeanCH.BR.ExcessDrop
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn FrontLayers

/-- A vertex sequence with arcs and membership gives walks between any two of its points. -/
theorem seq_walk {D : CH.Digraph} {W : Finset ℕ} (f : ℕ → ℕ) (n : ℕ)
    (hf : ∀ i, i < n → f (i + 1) ∈ W ∧ D (f i) (f (i + 1)) = true) :
    ∀ i j, i ≤ j → j ≤ n → Walk D W (f i) (f j) (j - i) := by
  intro i j ij jn
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact .refl _
  | succ j ih =>
    by_cases e : i = j + 1
    · subst e
      simpa using (Walk.refl (D := D) (W := W) (f (j + 1)))
    · have w := ih (by omega) (by omega)
      have := w.snoc (hf j (by omega)).1 (hf j (by omega)).2
      rwa [show j - i + 1 = j + 1 - i by omega] at this

/-- The abstract shape: `|X| = r`, `|Y| = r + e`, rows of `X` have out-degree `≥ r` and
head only `X ∪ Y`, rows of `Y` have at least `e` heads in `X ∪ Y`. -/
structure Drop (D : CH.Digraph) (V X Y : Finset ℕ) (q r e : ℕ) : Prop where
  free : QFree D V q
  xv : X ⊆ V
  yv : Y ⊆ V
  cx : X.card = r
  cy : Y.card = r + e
  one : 1 ≤ e
  time : r + e + 1 ≤ q
  degX : ∀ x ∈ X, r ≤ (outN D V x).card
  headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y
  degY : ∀ y ∈ Y, e ≤ (outN D (X ∪ Y) y).card

variable {D : CH.Digraph} {V X Y : Finset ℕ} {q r e : ℕ}

/-- (1) **Omission.** An `X`-sink heads only rows of `Y`, and omits at most `e` of them. -/
theorem sink_omits_e (P : Drop D V X Y q r e) {σ : ℕ} (σm : σ ∈ X) (kσ : Sink D X σ) :
    outN D V σ ⊆ Y ∧ (Y \ outN D V σ).card ≤ e := by
  have sub : outN D V σ ⊆ Y := by
    intro z hz
    rcases mem_union.mp (P.headsX σ σm hz) with zx | zy
    · exact (kσ z zx (mem_outN.mp hz).2).elim
    · exact zy
  refine ⟨sub, ?_⟩
  rw [card_sdiff_of_subset sub]
  have := P.degX σ σm
  have := P.cy
  omega

/-- (2) **Returning rows and their ancestors are omitted.** If `b ∈ Y` reaches `y` in `t`
steps, `y → x`, and `x` reaches `σ` in `d` steps, then `σ` does not head `b` as soon as
`t + d + 2 ≤ q`. -/
theorem omitted_ancestor (P : Drop D V X Y q r e) {σ x y b t d : ℕ} (xm : x ∈ X)
    (bm : b ∈ Y) (up : Walk D V b y t) (ret : D y x = true) (down : Walk D V x σ d)
    (len : t + d + 2 ≤ q) : b ∉ outN D V σ := by
  intro hb
  have loop := Walk.step (P.yv bm) (mem_outN.mp hb).2 ((up.snoc (P.xv xm) ret).append down)
  exact P.free σ _ (by omega) (by omega) loop

/-- (3) **Chains are short.** A walk inside `Y` with `e` arcs, given as a sequence
`f 0 → … → f e`, cannot end at a row returning into `X`: its `e + 1` rows are distinct
(Y is acyclic) and all omitted by a sink reached from the return target. -/
theorem chain_false (P : Drop D V X Y q r e) (f : ℕ → ℕ) (f0 : f 0 ∈ Y)
    (hf : ∀ i, i < e → f (i + 1) ∈ Y ∧ D (f i) (f (i + 1)) = true) {x : ℕ} (xm : x ∈ X)
    (ret : D (f e) x = true) : False := by
  classical
  have fx := P.free.mono_set P.xv
  have sx : X.card ≤ q := by have := P.cx; have := P.time; omega
  obtain ⟨σ, σm, stop, d, dl, down⟩ := reach_sink_of_card fx sx xm
  have kσ : Sink D X σ := fun z zm => stop z zm
  obtain ⟨_, few⟩ := sink_omits_e P σm kσ
  have fm (i) (il : i ≤ e) : f i ∈ Y := by
    rcases i with _ | i
    · exact f0
    · exact (hf i (by omega)).1
  have sub : (range (e + 1)).image f ⊆ Y \ outN D V σ := by
    intro z hz
    obtain ⟨i, im, rfl⟩ := mem_image.mp hz
    have il := mem_range.mp im
    refine mem_sdiff.mpr ⟨fm i (by omega), ?_⟩
    have up := (seq_walk f e hf i e (by omega) le_rfl).mono P.yv
    exact omitted_ancestor P xm (fm i (by omega)) up ret (down.mono P.xv)
      (by have := P.cx; have := P.time; omega)
  have inj : Set.InjOn f (range (e + 1)) := by
    intro i hi j hj eq
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with lt | lt
    · have w := seq_walk f e hf i j lt.le (by omega)
      rw [← eq] at w
      exact P.free _ _ (by omega) (by have := P.time; omega) (w.mono P.yv)
    · have w := seq_walk f e hf j i lt.le (by omega)
      rw [eq] at w
      exact P.free _ _ (by omega) (by have := P.time; omega) (w.mono P.yv)
  have := card_le_card sub
  rw [card_image_of_injOn inj, card_range] at this
  omega

/-- A sink of `Y` has a head in `X`. -/
theorem sink_returns_e (P : Drop D V X Y q r e) {s : ℕ} (sm : s ∈ Y)
    (ks : ∀ z ∈ Y, ¬ D s z = true) : ∃ x ∈ X, D s x = true := by
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (outN D (X ∪ Y) s).card by
    have := P.degY s sm; have := P.one; omega)
  obtain ⟨zm, arc⟩ := mem_outN.mp hz
  rcases mem_union.mp zm with zx | zy
  · exact ⟨z, zx, arc⟩
  · exact (ks z zy arc).elim

/-- (3') **Every walk inside `Y` has fewer than `e` arcs.** Extend it to a sink of `Y`
(which returns into `X`) and apply `chain_false` to the last `e` arcs. -/
theorem walks_short (P : Drop D V X Y q r e) {y z k : ℕ} (ym : y ∈ Y)
    (walk : Walk D Y y z k) : k < e := by
  by_contra! long
  have fy := P.free.mono_set P.yv
  have sy : Y.card ≤ q := by have := P.cy; have := P.time; omega
  have zm : z ∈ Y := walk.end_mem_or.elim (fun e => e ▸ ym) id
  obtain ⟨s, sm, ks, m, _, tail⟩ := reach_sink_of_card fy sy zm
  obtain ⟨x, xm, ret⟩ := sink_returns_e P sm ks
  obtain ⟨g, g0, gl, hg⟩ := (walk.append tail).toFun
  let f := fun i => g (k + m - e + i)
  have f0 : f 0 ∈ Y := by
    simp only [f, Nat.add_zero]
    rcases Nat.eq_zero_or_pos (k + m - e) with h0 | hpos
    · rw [h0, g0]; exact ym
    · have := (hg (k + m - e - 1) (by omega)).1
      rwa [show k + m - e - 1 + 1 = k + m - e by omega] at this
  have hf (i) (il : i < e) : f (i + 1) ∈ Y ∧ D (f i) (f (i + 1)) = true := by
    have := hg (k + m - e + i) (by omega)
    simp only [f, ← Nat.add_assoc]
    exact this
  have fe : f e = s := by
    simp only [f, show k + m - e + e = k + m by omega]
    exact gl
  exact chain_false P f f0 hf xm (fe ▸ ret)

open scoped Classical in
/-- Rows of `X` reached from `y` by a walk of `1 … n` arcs. -/
noncomputable def reachX (D : CH.Digraph) (V X : Finset ℕ) (n y : ℕ) : Finset ℕ :=
  X.filter (fun x => ∃ k, 1 ≤ k ∧ k ≤ n ∧ Walk D V y x k)

/-- **Reach count.** A row of `Y` all of whose walks inside `Y` have fewer than `n` arcs
reaches at least `e` rows of `X` within `n` arcs. -/
theorem reach_count (P : Drop D V X Y q r e) :
    ∀ n, ∀ y ∈ Y, (∀ z k, Walk D Y y z k → k < n) → e ≤ (reachX D V X n y).card := by
  classical
  intro n
  induction n with
  | zero =>
    intro y _ short
    exact absurd (short y 0 (.refl y)) (by omega)
  | succ n ih =>
    intro y ym short
    by_cases hc : ∃ c ∈ Y, D y c = true
    · obtain ⟨c, cm, arc⟩ := hc
      have shortc (z k) (w : Walk D Y c z k) : k < n := by
        have := short z (k + 1) (.step cm arc w)
        omega
      have sub : reachX D V X n c ⊆ reachX D V X (n + 1) y := by
        intro x hx
        simp only [reachX, mem_filter] at hx ⊢
        obtain ⟨xm, k, k1, kn, w⟩ := hx
        exact ⟨xm, k + 1, by omega, by omega, .step (P.yv cm) arc w⟩
      exact (ih c cm shortc).trans (card_le_card sub)
    · push Not at hc
      have sub : outN D (X ∪ Y) y ⊆ reachX D V X (n + 1) y := by
        intro z hz
        obtain ⟨zm, arc⟩ := mem_outN.mp hz
        have zx : z ∈ X := by
          rcases mem_union.mp zm with zx | zy
          · exact zx
          · exact absurd arc (by simp [hc z zy])
        simp only [reachX, mem_filter]
        exact ⟨zx, 1, le_rfl, by omega, .step (P.xv zx) arc (.refl z)⟩
      exact (P.degY y ym).trans (card_le_card sub)

open scoped Classical in
/-- **Target count.** At most `e` rows of `Y` reach a given row `x` of `X` within `e` arcs:
all of them are omitted by an `X`-sink below `x`. -/
theorem target_count (P : Drop D V X Y q r e) {x : ℕ} (xm : x ∈ X) :
    (Y.filter (fun y => ∃ k, 1 ≤ k ∧ k ≤ e ∧ Walk D V y x k)).card ≤ e := by
  classical
  have fx := P.free.mono_set P.xv
  have sx : X.card ≤ q := by have := P.cx; have := P.time; omega
  obtain ⟨σ, σm, stop, d, dl, down⟩ := reach_sink_of_card fx sx xm
  obtain ⟨_, few⟩ := sink_omits_e P σm (fun z zm => stop z zm)
  refine le_trans (card_le_card ?_) few
  intro y hy
  obtain ⟨ym, k, k1, ke, w⟩ := mem_filter.mp hy
  refine mem_sdiff.mpr ⟨ym, fun hb => ?_⟩
  have loop := Walk.step (P.yv ym) (mem_outN.mp hb).2 (w.append (down.mono P.xv))
  exact P.free σ _ (by omega) (by have := P.cx; have := P.time; omega) loop

/-- **Excess drop, core.** The shape `Drop` is impossible, whatever the number of sinks
of `X`. -/
theorem drop_false (P : Drop D V X Y q r e) : False := by
  classical
  let rel := fun y x => ∃ k, 1 ≤ k ∧ k ≤ e ∧ Walk D V y x k
  have upper : ∑ x ∈ X, (Y.filter (fun y => rel y x)).card ≤ X.card • e :=
    sum_le_card_nsmul _ _ _ (fun x xm => target_count P xm)
  have lower : Y.card • e ≤ ∑ y ∈ Y, (reachX D V X e y).card :=
    card_nsmul_le_sum _ _ _ (fun y ym => reach_count P e y ym (fun z k w => walks_short P ym w))
  have swap : ∑ x ∈ X, (Y.filter (fun y => rel y x)).card =
      ∑ y ∈ Y, (reachX D V X e y).card := by
    simp only [reachX, card_filter]
    exact sum_comm
  rw [swap, smul_eq_mul, P.cx] at upper
  rw [smul_eq_mul, P.cy] at lower
  have := P.one
  nlinarith

/-- **Excess drop.** Layers of widths `r` (`L 1 … L h`), `r + e`, then at most `r - e`, with
`1 ≤ h`, `1 ≤ e`, `r + h ≤ q` and `r + e + 1 ≤ q`: impossible. -/
theorem excess_drop_false {L : ℕ → Finset ℕ} {h : ℕ} (P : Layers D V L q r h) (hh : 1 ≤ h)
    (he : 1 ≤ e) (time : r + h ≤ q) (time' : r + e + 1 ≤ q)
    (cy : (L (h + 1)).card = r + e) (cz : (L (h + 2)).card + e ≤ r) : False := by
  classical
  refine drop_false (X := L h) (Y := L (h + 1)) ⟨P.free, P.sub h, P.sub (h + 1),
    P.size h hh le_rfl, cy, he, time', P.quota h hh (by omega),
    full_prefix P (by omega) h hh le_rfl, ?_⟩
  intro t tm
  have sub : outN D V t ⊆ outN D (L h ∪ L (h + 1)) t ∪ L (h + 2) := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    obtain ⟨j, hj, jle, zj⟩ := P.step (h + 1) (by omega) le_rfl t tm z hz
    by_cases e1 : j = h + 2
    · exact mem_union_right _ (e1 ▸ zj)
    by_cases e2 : j = h + 1
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (e2 ▸ zj), arc⟩)
    by_cases e3 : j = h
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ (e3 ▸ zj), arc⟩)
    exact (no_far_return P (by omega) hj (by omega : j < h + 1) (by omega) le_rfl (by omega)
      zj tm arc).elim
  have := (card_le_card sub).trans (card_union_le _ _)
  have := P.quota (h + 1) (by omega) le_rfl t tm
  omega

/-- **Excess drop, one sink.** The unique-sink case (item (4) of the plan); a special case
of `excess_drop_false`. -/
theorem excess_drop_one_sink {L : ℕ → Finset ℕ} {h a : ℕ} (P : Layers D V L q r h) (hh : 1 ≤ h)
    (he : 1 ≤ e) (time : r + h ≤ q) (time' : r + e + 1 ≤ q)
    (cy : (L (h + 1)).card = r + e) (cz : (L (h + 2)).card + e ≤ r)
    (_am : a ∈ L h) (_ka : Sink D (L h) a) (_only : ∀ s ∈ L h, Sink D (L h) s → s = a) : False :=
  excess_drop_false P hh he time time' cy cz

#print axioms seq_walk
#print axioms sink_omits_e
#print axioms omitted_ancestor
#print axioms chain_false
#print axioms walks_short
#print axioms reach_count
#print axioms target_count
#print axioms drop_false
#print axioms excess_drop_false
#print axioms excess_drop_one_sink

end LeanCH.BR.ExcessDrop
