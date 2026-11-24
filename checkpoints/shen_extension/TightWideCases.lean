import checkpoints.shen_extension.TightWideBanks

/-!
# Layers `r`, `r + 1`, `r`, `≤ r - 1` are impossible (`5 ≤ r`, `q = r + 1`)

We check the four bank conditions of `TightWideBanks.banks_false` by the number of
sinks of `X`.

* Two or more `X`-sinks (`many_sinks_false`): every row of `X` reaches a sink within
  `r - 2` steps, so return tails have no `Y`-parent and `B` is the set of tails. Each tail
  is the single omission of some `X`-sink, so `|B|` is at most the number of `X`-sinks,
  which is at most `2` beside an `(r-2)`-deep row (`sinks_of_deep`).
* One `X`-sink `a` (`one_sink_false`): every tail is the label `y₀` that `a` omits. If
  `y₀` has a `Y`-parent `p`, a return target of `y₀` is `(r-1)`-deep, so `p` is the only
  parent of `y₀`, `p` has none, and `B ⊆ {y₀, p}`; `p` reaches all of `Z` through
  `y₀`, the target and an `A`-sink.

`tight_wide_false` combines both.
-/

namespace LeanCH.BR.TightWideCases
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn TightWideBanks

open scoped Classical in
/-- A `t`-deep row of an acyclic `X` leaves room for at most `|X| - t` sinks: the first
`t` rows of its shortest sink path are not sinks. -/
theorem sinks_of_deep {D : CH.Digraph} {X : Finset ℕ} {q t x : ℕ} (free : QFree D X q)
    (size : X.card ≤ q) (xm : x ∈ X) (deep : Deep D X t x) :
    t + (X.filter (Sink D X)).card ≤ X.card := by
  classical
  obtain ⟨P⟩ := exists_shortest_sink_path free size xm
  have len := (deep_iff_len P).mp deep
  let S := (range P.len).image P.vertex
  have cardS : S.card = P.len := by
    rw [card_image_of_injOn (fun i hi j hj e => P.injective free size
      (by simp only [coe_range, Set.mem_Iio] at hi ⊢; omega)
      (by simp only [coe_range, Set.mem_Iio] at hj ⊢; omega) e), card_range]
  have disj : Disjoint S (X.filter (Sink D X)) := by
    rw [disjoint_left]
    intro a aS aK
    obtain ⟨i, im, rfl⟩ := mem_image.mp aS
    have il := mem_range.mp im
    exact (mem_filter.mp aK).2 _ (P.mem _ (by omega)) (P.edge i il)
  have sub : S ∪ X.filter (Sink D X) ⊆ X := by
    refine union_subset (fun a aS => ?_) (filter_subset _ _)
    obtain ⟨i, im, rfl⟩ := mem_image.mp aS
    exact P.mem _ (by have := mem_range.mp im; omega)
  have := card_le_card sub
  rw [card_union_of_disjoint disj, cardS] at this
  omega

section cases
variable {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}

/-- A return tail is omitted by every `X`-sink reached from its target. -/
theorem tail_omitted (t : Tight D V X Y Z W q r) {y x s k : ℕ} (ym : y ∈ Y) (xm : x ∈ X)
    (yx : D y x = true) (walk : Walk D X x s k) (kl : k < X.card) : D s y ≠ true := fun h =>
  t.free x (k + 1 + 1) (by omega) (by have := t.cx; have := t.hq; omega)
    (((walk.mono t.xv).snoc (t.yv ym) h).snoc (t.xv xm) yx)

open scoped Classical in
/-- **Two or more `X`-sinks.** -/
theorem many_sinks_false (t : Tight D V X Y Z W q r) {s₁ s₂ : ℕ} (m₁ : s₁ ∈ X) (m₂ : s₂ ∈ X)
    (ne : s₁ ≠ s₂) (k₁ : Sink D X s₁) (k₂ : Sink D X s₂) : False := by
  classical
  have fx := t.free.mono_set t.xv
  have sx : X.card ≤ q := by have := t.cx; have := t.hq; omega
  have q1 : 1 ≤ q := by have := t.hq; omega
  -- return tails have no `Y`-parent
  have orphan (y) (ym : y ∈ Y) (x) (xm : x ∈ X) (yx : D y x = true) (p) (pm : p ∈ Y)
      (py : D p y = true) : False := by
    obtain ⟨s, sm, ks, k, kl, walk⟩ := short_sink fx sx m₁ m₂ ne k₁ k₂ xm
    have one := sink_omits (t.headsX s sm) ks (t.degX s sm) t.cy
    have sp : D s p ≠ true := fun h => t.free x (k + 1 + 1 + 1) (by omega)
      (by have := t.cx; have := t.hq; omega)
      ((((walk.mono t.xv).snoc (t.yv pm) h).snoc (t.yv ym) py).snoc (t.xv xm) yx)
    have e := card_le_one.mp one p (mem_sdiff.mpr ⟨pm, fun h => sp (mem_outN.mp h).2⟩)
      y (mem_sdiff.mpr ⟨ym, fun h => tail_omitted t ym xm yx walk (by omega) (mem_outN.mp h).2⟩)
    subst e
    exact loopfree t.free q1 (t.yv pm) py
  -- so every row of `B` is a tail
  have tail (b) (bB : b ∈ bankB D X Y) : ∃ x ∈ X, D b x = true := by
    obtain ⟨bm, y', k, walk, x, xm, yx⟩ := mem_bankB.mp bB
    by_cases e : b = y'
    · exact ⟨x, xm, e ▸ yx⟩
    · obtain ⟨p, pm, py⟩ := last_parent bm walk e
      exact (orphan y' (walk.end_mem_or.elim (fun h => h ▸ bm) id) x xm yx p pm py).elim
  -- each tail is the single omission of a sink
  have omitter (b) (bB : b ∈ bankB D X Y) : ∃ s ∈ X, Sink D X s ∧ D s b ≠ true := by
    obtain ⟨x, xm, bx⟩ := tail b bB
    obtain ⟨s, sm, stop, m, ml, walk⟩ := reach_sink_of_card fx sx xm
    exact ⟨s, sm, fun z zm => stop z zm, tail_omitted t (bankB_sub bB) xm bx walk ml⟩
  let f := fun b => if h : ∃ s ∈ X, Sink D X s ∧ D s b ≠ true then h.choose else 0
  have fm (b) (bB : b ∈ bankB D X Y) : f b ∈ X ∧ Sink D X (f b) ∧ D (f b) b ≠ true := by
    have h := omitter b bB
    simp only [f, h, dite_true]
    exact h.choose_spec
  have inj : Set.InjOn f (bankB D X Y) := by
    intro b hb b' hb' e
    have hb := Finset.mem_coe.mp hb
    have hb' := Finset.mem_coe.mp hb'
    obtain ⟨sm, ks, sb⟩ := fm b hb
    obtain ⟨_, _, sb'⟩ := fm b' hb'
    rw [← e] at sb'
    exact card_le_one.mp (sink_omits (t.headsX _ sm) ks (t.degX _ sm) t.cy) b
      (mem_sdiff.mpr ⟨bankB_sub hb, fun h => sb (mem_outN.mp h).2⟩) b'
      (mem_sdiff.mpr ⟨bankB_sub hb', fun h => sb' (mem_outN.mp h).2⟩)
  have imgSub : (bankB D X Y).image f ⊆ X.filter (Sink D X) := by
    intro s hs
    obtain ⟨b, bB, rfl⟩ := mem_image.mp hs
    exact mem_filter.mpr ⟨(fm b bB).1, (fm b bB).2.1⟩
  have imgCard : ((bankB D X Y).image f).card = (bankB D X Y).card := card_image_of_injOn inj
  have sinksX := card_le_card (filter_subset (Sink D X) X)
  have bSinks := card_le_card imgSub
  have cards := bank_card (D := D) (X := X) (Y := Y)
  have := t.cx; have := t.cy; have := t.five
  refine banks_false t ?P1 ?P2 ?P3 ?P4
  · exact card_pos.mp (by omega)
  · intro σ σm kσ
    by_cases two : 2 ≤ (bankA D X Y).card
    · exact Or.inl two
    right
    have eq := eq_of_subset_of_card_le imgSub (by omega)
    obtain ⟨b, bB, rfl⟩ := mem_image.mp (eq ▸ mem_filter.mpr ⟨σm, kσ⟩ :
      σ ∈ (bankB D X Y).image f)
    obtain ⟨sm, ks, sb⟩ := fm b bB
    intro a am
    refine mem_outN.mpr ⟨bankA_sub.trans t.yv am, ?_⟩
    by_contra no
    have e := card_le_one.mp (sink_omits (t.headsX _ sm) ks (t.degX _ sm) t.cy) a
      (mem_sdiff.mpr ⟨bankA_sub am, fun h => no (mem_outN.mp h).2⟩) b
      (mem_sdiff.mpr ⟨bankB_sub bB, fun h => sb (mem_outN.mp h).2⟩)
    subst e
    exact A_not_B am bB
  · intro x xm deep
    have := sinks_of_deep fx sx xm deep
    omega
  · exact fun b bB => Or.inl (tail b bB)

#print axioms many_sinks_false

/-- **One `X`-sink.** -/
theorem one_sink_false (t : Tight D V X Y Z W q r) {a : ℕ} (am : a ∈ X) (ka : Sink D X a)
    (only : ∀ s ∈ X, Sink D X s → s = a) : False := by
  classical
  have fx := t.free.mono_set t.xv
  have sx : X.card ≤ q := by have := t.cx; have := t.hq; omega
  have q1 : 1 ≤ q := by have := t.hq; omega
  have AV : bankA D X Y ⊆ V := bankA_sub.trans t.yv
  have one := sink_omits (t.headsX a am) ka (t.degX a am) t.cy
  have cards := bank_card (D := D) (X := X) (Y := Y)
  have := t.cx; have := t.cy; have := t.five; have := t.hq
  -- every return tail is omitted by `a`
  have miss (y) (ym : y ∈ Y) (x) (xm : x ∈ X) (yx : D y x = true) : D a y ≠ true := by
    obtain ⟨s, sm, stop, m, ml, walk⟩ := reach_sink_of_card fx sx xm
    have e := only s sm (fun z zm => stop z zm)
    subst e
    exact tail_omitted t ym xm yx walk ml
  -- the conditions follow from `|B| ≤ 2` and `P4`
  have finish (small : (bankB D X Y).card ≤ 2)
      (P4 : ∀ b ∈ bankB D X Y, (∃ x ∈ X, D b x = true) ∨ Near D V Z b r) : False :=
    banks_false t (card_pos.mp (by omega)) (fun _ _ _ => Or.inl (by omega))
      (fun _ _ _ => small) P4
  by_cases empty : bankB D X Y = ∅
  · exact finish (by rw [empty]; simp) (fun b bB => by rw [empty] at bB; simp at bB)
  obtain ⟨b₁, b₁B⟩ := nonempty_iff_ne_empty.mpr empty
  obtain ⟨b₁m, y₀, k₁, walk₁, x₀, x₀m, y₀x₀⟩ := mem_bankB.mp b₁B
  have y₀m : y₀ ∈ Y := walk₁.end_mem_or.elim (fun h => h ▸ b₁m) id
  -- all tails are `y₀`
  have same (y) (ym : y ∈ Y) (x) (xm : x ∈ X) (yx : D y x = true) : y = y₀ :=
    card_le_one.mp one y (mem_sdiff.mpr ⟨ym, fun h => miss y ym x xm yx (mem_outN.mp h).2⟩)
      y₀ (mem_sdiff.mpr ⟨y₀m, fun h => miss y₀ y₀m x₀ x₀m y₀x₀ (mem_outN.mp h).2⟩)
  -- every row of `B` reaches `y₀` inside `Y`
  have toY₀ (b) (bB : b ∈ bankB D X Y) : ∃ k, Walk D Y b y₀ k := by
    obtain ⟨bm, y', k, walk, x, xm, yx⟩ := mem_bankB.mp bB
    have e := same y' (walk.end_mem_or.elim (fun h => h ▸ bm) id) x xm yx
    subst e
    exact ⟨k, walk⟩
  by_cases orphan : ∀ p ∈ Y, D p y₀ ≠ true
  · -- `B = {y₀}`
    have sub : bankB D X Y ⊆ {y₀} := by
      intro b bB
      obtain ⟨k, walk⟩ := toY₀ b bB
      by_contra ne
      obtain ⟨p, pm, py⟩ := last_parent (bankB_sub bB) walk (fun e => ne (mem_singleton.mpr e))
      exact orphan p pm py
    refine finish ((card_le_card sub).trans (by simp)) (fun b bB => Or.inl ?_)
    rw [mem_singleton.mp (sub bB)]
    exact ⟨x₀, x₀m, y₀x₀⟩
  push Not at orphan
  obtain ⟨p, pm, py₀⟩ := orphan
  have pne : p ≠ y₀ := fun e => loopfree t.free q1 (t.yv pm) (e ▸ py₀)
  have ap : D a p = true := by
    by_contra no
    exact pne (card_le_one.mp one p (mem_sdiff.mpr ⟨pm, fun h => no (mem_outN.mp h).2⟩)
      y₀ (mem_sdiff.mpr ⟨y₀m, fun h => miss y₀ y₀m x₀ x₀m y₀x₀ (mem_outN.mp h).2⟩))
  -- the target `x₀` is `(r-1)`-deep, so it omits at most two labels of `Y`
  have deep : Deep D X (r - 1) x₀ := by
    intro s sm ks k walk
    have e := only s sm ks
    subst e
    by_contra! short
    exact t.free x₀ (k + 1 + 1 + 1) (by omega) (by omega)
      ((((walk.mono t.xv).snoc (t.yv pm) ap).snoc (t.yv y₀m) py₀).snoc (t.xv x₀m) y₀x₀)
  have inner := deep_heads fx sx x₀m deep
  have split : outN D V x₀ ⊆ outN D X x₀ ∪ outN D Y x₀ := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (t.headsX x₀ x₀m hz) with zx | zy
    · exact mem_union_left _ (mem_outN.mpr ⟨zx, arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨zy, arc⟩)
  have heads := (card_le_card split).trans (card_union_le _ _)
  have deg := t.degX x₀ x₀m
  have M2 : (Y \ outN D V x₀).card ≤ 2 := by
    have sub : Y \ outN D V x₀ ⊆ Y \ outN D Y x₀ := by
      intro z hz
      obtain ⟨zm, zn⟩ := mem_sdiff.mp hz
      exact mem_sdiff.mpr ⟨zm, fun h => zn (mem_outN.mpr ⟨t.yv zm, (mem_outN.mp h).2⟩)⟩
    have := card_le_card sub
    rw [card_sdiff_of_subset outN_subset] at this
    omega
  have y₀M : y₀ ∈ Y \ outN D V x₀ := mem_sdiff.mpr ⟨y₀m, fun h =>
    t.free x₀ 2 (by omega) (by omega) (.step (t.yv y₀m) (mem_outN.mp h).2 (.step (t.xv x₀m) y₀x₀ (.refl x₀)))⟩
  have parM (p') (p'm : p' ∈ Y) (p'y : D p' y₀ = true) : p' ∈ (Y \ outN D V x₀).erase y₀ := by
    refine mem_erase.mpr ⟨fun e => loopfree t.free q1 (t.yv p'm) (e ▸ p'y), mem_sdiff.mpr ⟨p'm, fun h => ?_⟩⟩
    exact t.free x₀ 3 (by omega) (by omega) (.step (t.yv p'm) (mem_outN.mp h).2
      (.step (t.yv y₀m) p'y (.step (t.xv x₀m) y₀x₀ (.refl x₀))))
  have M1 : ((Y \ outN D V x₀).erase y₀).card ≤ 1 := by
    rw [card_erase_of_mem y₀M]; omega
  -- `x₀` heads every row of `Y` other than `y₀` and `p`
  have x₀all (y) (ym : y ∈ Y) (ne₀ : y ≠ y₀) (nep : y ≠ p) : D x₀ y = true := by
    by_contra no
    exact nep (card_le_one.mp M1 y (mem_erase.mpr ⟨ne₀, mem_sdiff.mpr ⟨ym, fun h => no (mem_outN.mp h).2⟩⟩)
      p (parM p pm py₀))
  -- `p` is the only parent of `y₀` and has no parent itself
  have uniq (p') (p'm : p' ∈ Y) (p'y : D p' y₀ = true) : p' = p :=
    card_le_one.mp M1 p' (parM p' p'm p'y) p (parM p pm py₀)
  have noPar (p'') (p''m : p'' ∈ Y) (p''p : D p'' p = true) : False := by
    have ne₁ : p'' ≠ p := fun e => loopfree t.free q1 (t.yv pm) (e ▸ p''p)
    have ne₀ : p'' ≠ y₀ := fun e =>
      t.free p 2 (by omega) (by omega) (.step (t.yv y₀m) py₀ (.step (t.yv pm) (e ▸ p''p) (.refl p)))
    exact t.free x₀ 4 (by omega) (by omega) (.step (t.yv p''m) (x₀all p'' p''m ne₀ ne₁)
      (.step (t.yv pm) p''p (.step (t.yv y₀m) py₀ (.step (t.xv x₀m) y₀x₀ (.refl x₀)))))
  -- `B ⊆ {y₀, p}`
  have sub : bankB D X Y ⊆ {y₀, p} := by
    intro b bB
    obtain ⟨k, walk⟩ := toY₀ b bB
    cases k with
    | zero => cases walk; exact mem_insert_self _ _
    | succ k =>
      obtain ⟨u, init, _, uy⟩ := walk.unsnoc
      have um : u ∈ Y := init.end_mem_or.elim (fun h => h ▸ bankB_sub bB) id
      have e := uniq u um uy
      subst e
      by_cases bu : b = u
      · rw [bu]; exact mem_insert_of_mem (mem_singleton_self _)
      · obtain ⟨p'', p''m, p''u⟩ := last_parent (bankB_sub bB) init bu
        exact (noPar p'' p''m p''u).elim
  have small : (bankB D X Y).card ≤ 2 :=
    (card_le_card sub).trans ((card_insert_le _ _).trans (by simp))
  refine finish small (fun b bB => ?_)
  rcases mem_insert.mp (sub bB) with e | e
  · subst e; exact Or.inl ⟨x₀, x₀m, y₀x₀⟩
  · rw [mem_singleton.mp e]
    right
    obtain ⟨s, sm, stop⟩ := exists_sink (A_free t) (card_pos.mp (by omega)) (A_size t)
    have pB : p ∈ bankB D X Y := mem_bankB.mpr ⟨pm, y₀, 1, .step y₀m py₀ (.refl y₀), x₀, x₀m, y₀x₀⟩
    have y₀B : y₀ ∈ bankB D X Y := tail_mem_B y₀m x₀m y₀x₀
    have xs : D x₀ s = true := x₀all s (bankA_sub sm) (fun e => A_not_B sm (e ▸ y₀B))
      (fun e => A_not_B sm (e ▸ pB))
    exact (Near.step (t.yv y₀m) py₀ (Near.step (t.xv x₀m) y₀x₀ (Near.step (AV sm) xs
      (near_sink t sm (fun z zm => stop z zm))))).mono (by omega)

/-- **Tight wide layer.** Layers `X`, `Y`, `Z`, `W` of widths `r`, `r + 1`, `r` and at most
`r - 1` are impossible at cutoff `q = r + 1` when `5 ≤ r`. -/
theorem tight_wide_false (t : Tight D V X Y Z W q r) : False := by
  have fx := t.free.mono_set t.xv
  have sx : X.card ≤ q := by have := t.cx; have := t.hq; omega
  obtain ⟨a, am, stop⟩ := exists_sink fx (card_pos.mp (by have := t.cx; have := t.five; omega)) sx
  have ka : Sink D X a := fun z zm => stop z zm
  by_cases two : ∃ s ∈ X, Sink D X s ∧ s ≠ a
  · obtain ⟨s, sm, ks, ne⟩ := two
    exact many_sinks_false t sm am ne ks ka
  · push Not at two
    exact one_sink_false t am ka two

end cases

/-- **Tight wide layer, unbundled.** Four consecutive layers `X`, `Y`, `Z`, `W` of a
`q`-free graph with `|X| = r`, `|Y| = r + 1`, `|Z| = r`, `|W| ≤ r - 1`, `5 ≤ r` and
`q = r + 1`, where the rows of `X`, `Y`, `Z` have out-degree at least `r` and head only
their own and earlier layers and the next one, cannot exist. -/
theorem tight_wide_layers_false {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V) (zv : Z ⊆ V)
    (cx : X.card = r) (cy : Y.card = r + 1) (cz : Z.card = r) (cw : W.card + 1 ≤ r)
    (five : 5 ≤ r) (hq : q = r + 1)
    (degX : ∀ x ∈ X, r ≤ (outN D V x).card) (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (degZ : ∀ z ∈ Z, r ≤ (outN D V z).card)
    (headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y) (headsY : ∀ y ∈ Y, outN D V y ⊆ X ∪ Y ∪ Z)
    (headsZ : ∀ z ∈ Z, outN D V z ⊆ X ∪ Y ∪ Z ∪ W) : False :=
  tight_wide_false ⟨free, xv, yv, zv, cx, cy, cz, cw, five, hq, degX, degY, degZ,
    headsX, headsY, headsZ⟩

#print axioms one_sink_false
#print axioms sinks_of_deep
#print axioms tight_wide_false
#print axioms tight_wide_layers_false

end LeanCH.BR.TightWideCases
