import checkpoints.shen_extension.WideLayerReturn

/-!
# Layers `r`, `r + 1`, `r`, `≤ r - 1`: the ancestor bank of the returns

Four consecutive layers `X`, `Y`, `Z`, `W` of a `q`-free graph with `q = r + 1`,
`|X| = r`, `|Y| = r + 1`, `|Z| = r`, `|W| ≤ r - 1` (`Tight`). Rows of `X`, `Y`, `Z` have
out-degree at least `r`; heads of `X` lie in `X ∪ Y`, of `Y` in `X ∪ Y ∪ Z`, of `Z` in
`X ∪ Y ∪ Z ∪ W`.

Split `Y` into the bank `B` of rows that reach, inside `Y`, a row with a head in `X`
(`Ret`), and its complement `A`. Rows of `A` head only `A ∪ Z`, so every `A`-sink heads
all of `Z`. `Near v k` says that `v` reaches every row of `Z` within `k` steps; a row of
`Z` cannot head a row that is near within `r`.

* `exit_false`: rows of `Z` cannot keep all their heads in `Z ∪ W ∪ T` for a set `T` of
  at most one row that heads all of `Z` but one.
* `A_target`, `deep_A_omit`: a return from `Z` into `A` lands on an `r`-deep row of `A`,
  which heads all of `Z` but one.
* `reach_A_sink`, `deep_of_target`, `target_false`: a return from `Z` into `X` is
  impossible once `|B| ≤ 2` for `(r-2)`-deep rows of `X`.
* `tail_near`: a return tail of `Y` is near within `r`.
* `banks_false`: the four conditions `P1`–`P4` on the bank give a contradiction.
-/

namespace LeanCH.BR.TightWideBanks
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn

/-- Four layers of widths `r`, `r + 1`, `r`, at most `r - 1` at cutoff `q = r + 1`. -/
structure Tight (D : CH.Digraph) (V X Y Z W : Finset ℕ) (q r : ℕ) : Prop where
  free : QFree D V q
  xv : X ⊆ V
  yv : Y ⊆ V
  zv : Z ⊆ V
  cx : X.card = r
  cy : Y.card = r + 1
  cz : Z.card = r
  cw : W.card + 1 ≤ r
  five : 5 ≤ r
  hq : q = r + 1
  degX : ∀ x ∈ X, r ≤ (outN D V x).card
  degY : ∀ y ∈ Y, r ≤ (outN D V y).card
  degZ : ∀ z ∈ Z, r ≤ (outN D V z).card
  headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y
  headsY : ∀ y ∈ Y, outN D V y ⊆ X ∪ Y ∪ Z
  headsZ : ∀ z ∈ Z, outN D V z ⊆ X ∪ Y ∪ Z ∪ W

/-- `y` reaches, inside `Y`, a row with a head in `X`. -/
def Ret (D : CH.Digraph) (X Y : Finset ℕ) (y : ℕ) : Prop :=
  ∃ y' k, Walk D Y y y' k ∧ ∃ x ∈ X, D y' x = true

open scoped Classical in
/-- The ancestor bank of the returns into `X`. -/
noncomputable def bankB (D : CH.Digraph) (X Y : Finset ℕ) : Finset ℕ := Y.filter (Ret D X Y)

open scoped Classical in
/-- The rows of `Y` that never reach a return. -/
noncomputable def bankA (D : CH.Digraph) (X Y : Finset ℕ) : Finset ℕ :=
  Y.filter (fun y => ¬ Ret D X Y y)

/-- `v` reaches every row of `Z` within `k` steps. -/
def Near (D : CH.Digraph) (V Z : Finset ℕ) (v k : ℕ) : Prop :=
  ∀ z ∈ Z, ∃ j ≤ k, Walk D V v z j

section bank
variable {D : CH.Digraph} {X Y : Finset ℕ}

open scoped Classical in
theorem mem_bankA {y : ℕ} : y ∈ bankA D X Y ↔ y ∈ Y ∧ ¬ Ret D X Y y := by
  unfold bankA; exact mem_filter

open scoped Classical in
theorem mem_bankB {y : ℕ} : y ∈ bankB D X Y ↔ y ∈ Y ∧ Ret D X Y y := by
  unfold bankB; exact mem_filter

theorem bankA_sub : bankA D X Y ⊆ Y := fun _ h => (mem_bankA.mp h).1

theorem bankB_sub : bankB D X Y ⊆ Y := fun _ h => (mem_bankB.mp h).1

theorem bank_card : (bankA D X Y).card + (bankB D X Y).card = Y.card := by
  classical
  have disj : Disjoint (bankA D X Y) (bankB D X Y) := by
    rw [disjoint_left]
    intro y ha hb
    exact (mem_bankA.mp ha).2 (mem_bankB.mp hb).2
  have cover : bankA D X Y ∪ bankB D X Y = Y := by
    ext y
    constructor
    · intro h
      rcases mem_union.mp h with h | h
      · exact (mem_bankA.mp h).1
      · exact (mem_bankB.mp h).1
    · intro ym
      by_cases ret : Ret D X Y y
      · exact mem_union_right _ (mem_bankB.mpr ⟨ym, ret⟩)
      · exact mem_union_left _ (mem_bankA.mpr ⟨ym, ret⟩)
  rw [← card_union_of_disjoint disj, cover]

theorem A_noX {a x : ℕ} (am : a ∈ bankA D X Y) (xm : x ∈ X) : D a x ≠ true :=
  fun h => (mem_bankA.mp am).2 ⟨a, 0, .refl a, x, xm, h⟩

theorem A_closed {a b : ℕ} (am : a ∈ bankA D X Y) (bm : b ∈ Y) (ab : D a b = true) :
    b ∈ bankA D X Y :=
  mem_bankA.mpr ⟨bm, fun ⟨y', k, walk, rest⟩ => (mem_bankA.mp am).2 ⟨y', k + 1, .step bm ab walk, rest⟩⟩

theorem tail_mem_B {b x : ℕ} (bm : b ∈ Y) (xm : x ∈ X) (bx : D b x = true) :
    b ∈ bankB D X Y :=
  mem_bankB.mpr ⟨bm, b, 0, .refl b, x, xm, bx⟩

theorem A_not_B {y : ℕ} (ha : y ∈ bankA D X Y) (hb : y ∈ bankB D X Y) : False :=
  (mem_bankA.mp ha).2 (mem_bankB.mp hb).2

end bank

section near
variable {D : CH.Digraph} {V Z : Finset ℕ}

theorem Near.mono {v k k' : ℕ} (h : Near D V Z v k) (le : k ≤ k') : Near D V Z v k' :=
  fun z zm => let ⟨j, jl, w⟩ := h z zm; ⟨j, jl.trans le, w⟩

theorem Near.step {v w k : ℕ} (wv : w ∈ V) (arc : D v w = true) (h : Near D V Z w k) :
    Near D V Z v (k + 1) :=
  fun z zm => let ⟨j, jl, walk⟩ := h z zm; ⟨j + 1, by omega, .step wv arc walk⟩

theorem Near.walk {v w j k : ℕ} (walk : Walk D V v w j) (h : Near D V Z w k) :
    Near D V Z v (j + k) :=
  fun z zm => let ⟨i, il, w'⟩ := h z zm; ⟨j + i, by omega, walk.append w'⟩

end near

/-- **Exit.** Rows of `Z` keep their heads in `Z ∪ W ∪ T`, where `T` has at most one row,
which heads all of `Z` but one, and `|W| < r ≤` out-degree. Then the rows of `Z` that do
not head `T` have a sink, and its heads all lie in `W`. -/
theorem exit_false {D : CH.Digraph} {V Z W T : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (zv : Z ⊆ V) (tv : T ⊆ V) (sz : Z.card ≤ q) (two : 2 ≤ Z.card) (q3 : 3 ≤ q)
    (cw : W.card + 1 ≤ r) (degZ : ∀ z ∈ Z, r ≤ (outN D V z).card) (cT : T.card ≤ 1)
    (miss : ∀ t ∈ T, (Z \ outN D V t).card ≤ 1)
    (heads : ∀ z ∈ Z, outN D V z ⊆ Z ∪ W ∪ T) : False := by
  classical
  let Z' := Z.filter (fun z => ∀ t ∈ T, D z t ≠ true)
  have z'sub : Z' ⊆ Z := filter_subset _ _
  have ne : Z'.Nonempty := by
    rcases T.eq_empty_or_nonempty with e | ⟨t, tm⟩
    · obtain ⟨z, zm⟩ := card_pos.mp (by omega : 0 < Z.card)
      exact ⟨z, mem_filter.mpr ⟨zm, fun t' tm' => by rw [e] at tm'; exact absurd tm' (notMem_empty _)⟩⟩
    · obtain ⟨z, zm, tz⟩ : ∃ z ∈ Z, D t z = true := by
        by_contra! none
        have all : Z \ outN D V t = Z := by
          ext z
          simp only [mem_sdiff, mem_outN]
          exact ⟨fun h => h.1, fun zm => ⟨zm, fun h => none z zm h.2⟩⟩
        have := miss t tm
        rw [all] at this
        omega
      refine ⟨z, mem_filter.mpr ⟨zm, fun t' tm' zt => ?_⟩⟩
      have e := card_le_one.mp cT t' tm' t tm
      subst e
      exact free z 2 (by omega) (by omega) (.step (tv tm') zt (.step (zv zm) tz (.refl z)))
  obtain ⟨σ, σm, stop⟩ := exists_sink (free.mono_set (z'sub.trans zv)) ne
    ((card_le_card z'sub).trans sz)
  have σZ := z'sub σm
  have σT := (mem_filter.mp σm).2
  have sub : outN D V σ ⊆ W := by
    intro h hh
    have arc := (mem_outN.mp hh).2
    rcases mem_union.mp (heads σ σZ hh) with hzw | ht
    · rcases mem_union.mp hzw with hz | hw
      · by_cases hZ' : h ∈ Z'
        · exact (stop h hZ' arc).elim
        · have : ∃ t ∈ T, D h t = true := by
            by_contra! none
            exact hZ' (mem_filter.mpr ⟨hz, fun t tm => by simpa using none t tm⟩)
          obtain ⟨t, tm, ht⟩ := this
          have th : D t h ≠ true := fun th =>
            free h 2 (by omega) (by omega) (.step (tv tm) ht (.step (zv hz) th (.refl h)))
          by_cases tσ : D t σ = true
          · exact (free σ 3 (by omega) (by omega) (.step (zv hz) arc (.step (tv tm) ht
              (.step (zv σZ) tσ (.refl σ))))).elim
          · have e := card_le_one.mp (miss t tm) σ (mem_sdiff.mpr ⟨σZ, fun x => tσ (mem_outN.mp x).2⟩)
              h (mem_sdiff.mpr ⟨hz, fun x => th (mem_outN.mp x).2⟩)
            subst e
            exact (loopfree free (by omega) (zv σZ) arc).elim
      · exact hw
    · exact (σT h ht arc).elim
  have := card_le_card sub
  have := degZ σ σZ
  omega

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

section tight
variable {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}

theorem A_heads (t : Tight D V X Y Z W q r) {a : ℕ} (am : a ∈ bankA D X Y) :
    outN D V a ⊆ bankA D X Y ∪ Z := by
  intro z hz
  have arc := (mem_outN.mp hz).2
  rcases mem_union.mp (t.headsY a (bankA_sub am) hz) with zxy | zz
  · rcases mem_union.mp zxy with zx | zy
    · exact (A_noX am zx arc).elim
    · exact mem_union_left _ (A_closed am zy arc)
  · exact mem_union_right _ zz

/-- Every `A`-sink heads all of `Z`. -/
theorem A_sink_full (t : Tight D V X Y Z W q r) {s : ℕ} (sm : s ∈ bankA D X Y)
    (ks : Sink D (bankA D X Y) s) : Z ⊆ outN D V s :=
  sink_full (A_heads t sm) ks (t.degY s (bankA_sub sm)) t.cz

theorem near_sink (t : Tight D V X Y Z W q r) {s : ℕ} (sm : s ∈ bankA D X Y)
    (ks : Sink D (bankA D X Y) s) : Near D V Z s 1 :=
  fun z zm => ⟨1, le_rfl, .step (t.zv zm) (mem_outN.mp (A_sink_full t sm ks zm)).2 (.refl z)⟩

theorem near_A (t : Tight D V X Y Z W q r) {a s k : ℕ} (sm : s ∈ bankA D X Y)
    (ks : Sink D (bankA D X Y) s) (walk : Walk D (bankA D X Y) a s k) : Near D V Z a (k + 1) :=
  Near.walk (walk.mono (bankA_sub.trans t.yv)) (near_sink t sm ks)

/-- A row of `Z` cannot head a row that reaches all of `Z` within `r` steps. -/
theorem near_false (t : Tight D V X Y Z W q r) {z v : ℕ} (zm : z ∈ Z) (vv : v ∈ V)
    (arc : D z v = true) (near : Near D V Z v r) : False := by
  obtain ⟨j, jl, walk⟩ := near z zm
  exact t.free v (j + 1) (by omega) (by have := t.hq; omega) (walk.snoc vv arc)

theorem A_free (t : Tight D V X Y Z W q r) : QFree D (bankA D X Y) q :=
  t.free.mono_set (bankA_sub.trans t.yv)

theorem A_size (t : Tight D V X Y Z W q r) : (bankA D X Y).card ≤ q := by
  have := card_le_card (bankA_sub (D := D) (X := X) (Y := Y))
  have := t.cy; have := t.hq; omega

/-- A return from `Z` into `A` lands on an `r`-deep row of `A`. -/
theorem A_target (t : Tight D V X Y Z W q r) {z a : ℕ} (zm : z ∈ Z) (am : a ∈ bankA D X Y)
    (arc : D z a = true) : Deep D (bankA D X Y) r a := by
  have deep := return_deep (m := 1) t.free (bankA_sub.trans t.yv) am (fun s sm ks =>
    Walk.step (t.zv zm) (mem_outN.mp (A_sink_full t sm ks zm)).2 (.refl z)) arc
  have e : q - 1 = r := by have := t.hq; omega
  rwa [e] at deep

/-- An `r`-deep row of `A` heads all of `Z` but one. -/
theorem deep_A_omit (t : Tight D V X Y Z W q r) {a : ℕ} (am : a ∈ bankA D X Y)
    (deep : Deep D (bankA D X Y) r a) : (Z \ outN D V a).card ≤ 1 := by
  have inner := deep_heads (A_free t) (A_size t) am deep
  have cA := card_le_card (bankA_sub (D := D) (X := X) (Y := Y))
  have split : outN D V a ⊆ outN D (bankA D X Y) a ∪ outN D Z a := by
    intro z hz
    have arc := (mem_outN.mp hz).2
    rcases mem_union.mp (A_heads t am hz) with za | zz
    · exact mem_union_left _ (mem_outN.mpr ⟨za, arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨zz, arc⟩)
  have heads := (card_le_card split).trans (card_union_le _ _)
  have deg := t.degY a (bankA_sub am)
  have sub : Z \ outN D V a ⊆ Z \ outN D Z a := by
    intro z hz
    obtain ⟨zm, zn⟩ := mem_sdiff.mp hz
    exact mem_sdiff.mpr ⟨zm, fun h => zn (mem_outN.mpr ⟨t.zv zm, (mem_outN.mp h).2⟩)⟩
  have := card_le_card sub
  rw [card_sdiff_of_subset outN_subset] at this
  have := t.cy; have := t.cz
  omega

open scoped Classical in
theorem T_card (t : Tight D V X Y Z W q r) :
    ((bankA D X Y).filter (Deep D (bankA D X Y) r)).card ≤ 1 := by
  have cA := card_le_card (bankA_sub (D := D) (X := X) (Y := Y))
  have := t.cy
  rcases deep_card (t := r) (A_free t) (A_size t) with bound | empty
  · omega
  · rw [empty]; simp

/-- An `X`-sink reaches an `A`-sink within two steps when `A` has two rows or the sink
heads all of `A`; so it reaches all of `Z` within three steps. -/
theorem reach_A_sink (t : Tight D V X Y Z W q r) {σ : ℕ} (σm : σ ∈ X) (kσ : Sink D X σ)
    (Ane : (bankA D X Y).Nonempty) (wide : 2 ≤ (bankA D X Y).card ∨ bankA D X Y ⊆ outN D V σ) :
    Near D V Z σ 3 := by
  have one := sink_omits (t.headsX σ σm) kσ (t.degX σ σm) t.cy
  have AV : bankA D X Y ⊆ V := bankA_sub.trans t.yv
  by_cases hit : ∃ s ∈ bankA D X Y, Sink D (bankA D X Y) s ∧ D σ s = true
  · obtain ⟨s, sm, ks, arc⟩ := hit
    exact (Near.step (AV sm) arc (near_sink t sm ks)).mono (by omega)
  push Not at hit
  obtain ⟨s₀, s₀m, stop₀⟩ := exists_sink (A_free t) Ane (A_size t)
  have k₀ : Sink D (bankA D X Y) s₀ := fun z zm => stop₀ z zm
  have miss₀ : s₀ ∈ Y \ outN D V σ :=
    mem_sdiff.mpr ⟨bankA_sub s₀m, fun h => hit s₀ s₀m k₀ (mem_outN.mp h).2⟩
  rcases wide with two | all
  · obtain ⟨a, am, ane⟩ := exists_mem_ne (show 1 < (bankA D X Y).card by omega) s₀
    obtain ⟨s, sm, stop, m, _, walk⟩ := reach_sink_of_card (A_free t) (A_size t) am
    have ks : Sink D (bankA D X Y) s := fun z zm => stop z zm
    have e := card_le_one.mp one s (mem_sdiff.mpr ⟨bankA_sub sm, fun h => hit s sm ks (mem_outN.mp h).2⟩)
      s₀ miss₀
    subst e
    obtain ⟨p, pm, ps⟩ := last_parent am walk ane
    have q1 : 1 ≤ q := by have := t.hq; omega
    have pne : p ≠ s := fun e => loopfree t.free q1 (AV pm) (e ▸ ps)
    have σp : D σ p = true := by
      by_contra no
      exact pne (card_le_one.mp one p (mem_sdiff.mpr ⟨bankA_sub pm, fun h => no (mem_outN.mp h).2⟩)
        s miss₀)
    exact Near.step (AV pm) σp (Near.step (AV sm) ps (near_sink t sm ks))
  · exact (hit s₀ s₀m k₀ (mem_outN.mp (all s₀m)).2).elim

/-- A return `z → x` from `Z` into `X` forces `x` to be `(r-2)`-deep in `X`. -/
theorem deep_of_target (t : Tight D V X Y Z W q r) (Ane : (bankA D X Y).Nonempty)
    (P2 : ∀ σ ∈ X, Sink D X σ → 2 ≤ (bankA D X Y).card ∨ bankA D X Y ⊆ outN D V σ)
    {z x : ℕ} (zm : z ∈ Z) (xm : x ∈ X) (arc : D z x = true) : Deep D X (r - 2) x := by
  intro s sm ks k walk
  by_contra! short
  obtain ⟨j, jl, w2⟩ := reach_A_sink t sm ks Ane (P2 s sm ks) z zm
  exact t.free x (k + j + 1) (by omega) (by have := t.hq; omega)
    (((walk.mono t.xv).append w2).snoc (t.xv xm) arc)

/-- Split the `Y`-heads of a row into its `A`-heads and `B`-heads. -/
theorem split_heads (t : Tight D V X Y Z W q r) {x : ℕ} (xm : x ∈ X) :
    (outN D V x).card ≤ (outN D X x).card + (outN D (bankA D X Y) x).card +
      (outN D (bankB D X Y) x).card := by
  classical
  have split : outN D V x ⊆ outN D X x ∪ outN D (bankA D X Y) x ∪ outN D (bankB D X Y) x := by
    intro h hh
    have arc := (mem_outN.mp hh).2
    rcases mem_union.mp (t.headsX x xm hh) with hx | hy
    · exact mem_union_left _ (mem_union_left _ (mem_outN.mpr ⟨hx, arc⟩))
    · by_cases ret : Ret D X Y h
      · exact mem_union_right _ (mem_outN.mpr ⟨mem_bankB.mpr ⟨hy, ret⟩, arc⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_outN.mpr ⟨mem_bankA.mpr ⟨hy, ret⟩, arc⟩))
  have := card_le_card split
  have := card_union_le (outN D X x ∪ outN D (bankA D X Y) x) (outN D (bankB D X Y) x)
  have := card_union_le (outN D X x) (outN D (bankA D X Y) x)
  omega

open scoped Classical in
/-- **No return into `X`.** A return `z → x` to an `(r-2)`-deep row of `X` is impossible
when `|B| ≤ 2`: every `A`-head of `x` is `(r-1)`-deep in `A`, and there are at most
`2 - |B|` such rows. -/
theorem target_false (t : Tight D V X Y Z W q r) {z x : ℕ} (zm : z ∈ Z) (xm : x ∈ X)
    (arc : D z x = true) (deep : Deep D X (r - 2) x) (small : (bankB D X Y).card ≤ 2) : False := by
  have fx := t.free.mono_set t.xv
  have sx : X.card ≤ q := by have := t.cx; have := t.hq; omega
  have inner := deep_heads fx sx xm deep
  have AV : bankA D X Y ⊆ V := bankA_sub.trans t.yv
  have sub : outN D (bankA D X Y) x ⊆ (bankA D X Y).filter (Deep D (bankA D X Y) (r - 1)) := by
    intro a ha
    obtain ⟨am, xa⟩ := mem_outN.mp ha
    refine mem_filter.mpr ⟨am, fun s sm ks k walk => ?_⟩
    by_contra! short
    exact t.free x (k + 1 + 1 + 1) (by omega) (by have := t.hq; omega)
      ((Walk.step (AV am) xa ((walk.mono AV).snoc (t.zv zm)
        (mem_outN.mp (A_sink_full t sm ks zm)).2)).snoc (t.xv xm) arc)
  have hA := card_le_card sub
  have hB := card_le_card (outN_subset (D := D) (W := bankB D X Y) (y := x))
  have heads := split_heads t xm
  have deg := t.degX x xm
  have cards := bank_card (D := D) (X := X) (Y := Y)
  have := t.cx; have := t.cy; have := t.five
  rcases deep_card (t := r - 1) (A_free t) (A_size t) with bound | empty
  · omega
  · rw [empty, card_empty] at hA
    omega

open scoped Classical in
/-- **Near tails.** A return tail `b → x` of `Y` reaches all of `Z` within `r` steps. -/
theorem tail_near (t : Tight D V X Y Z W q r) (Ane : (bankA D X Y).Nonempty)
    (P3 : ∀ x ∈ X, Deep D X (r - 2) x → (bankB D X Y).card ≤ 2)
    {b x : ℕ} (bm : b ∈ Y) (xm : x ∈ X) (bx : D b x = true) : Near D V Z b r := by
  have fx := t.free.mono_set t.xv
  have sx : X.card ≤ q := by have := t.cx; have := t.hq; omega
  have AV : bankA D X Y ⊆ V := bankA_sub.trans t.yv
  have bB : b ∈ bankB D X Y := tail_mem_B bm xm bx
  obtain ⟨P⟩ := exists_shortest_sink_path fx sx xm
  have walkP := P.walk (Nat.zero_le _) le_rfl
  simp only [P.start, Nat.sub_zero] at walkP
  have σm := P.mem _ le_rfl
  have kσ : Sink D X (P.vertex P.len) := fun z zm => P.sink z zm
  have bound := P.bounded
  have σb : D (P.vertex P.len) b ≠ true := fun h =>
    t.free b (P.len + 1 + 1) (by omega) (by have := t.cx; have := t.hq; omega)
      ((Walk.step (t.xv xm) bx (walkP.mono t.xv)).snoc (t.yv bm) h)
  have one := sink_omits (t.headsX _ σm) kσ (t.degX _ σm) t.cy
  have allA (a) (am : a ∈ bankA D X Y) : D (P.vertex P.len) a = true := by
    by_contra no
    have e := card_le_one.mp one a (mem_sdiff.mpr ⟨bankA_sub am, fun h => no (mem_outN.mp h).2⟩)
      b (mem_sdiff.mpr ⟨bm, fun h => σb (mem_outN.mp h).2⟩)
    subst e
    exact A_not_B am bB
  obtain ⟨s₀, s₀m, stop₀⟩ := exists_sink (A_free t) Ane (A_size t)
  have nearσ := Near.step (AV s₀m) (allA s₀ s₀m) (near_sink t s₀m (fun z zm => stop₀ z zm))
  by_cases short : P.len + 3 ≤ r
  · exact (Near.step (t.xv xm) bx (Near.walk (walkP.mono t.xv) nearσ)).mono (by omega)
  have deep : Deep D X (r - 2) x := (deep_iff_len P).mpr (by omega)
  have small := P3 x xm deep
  -- some `A`-head of `x` is shallow in `A`
  obtain ⟨a, ha, shallow⟩ : ∃ a ∈ outN D (bankA D X Y) x, ¬ Deep D (bankA D X Y) (r - 2) a := by
    by_contra! all
    have sub : outN D (bankA D X Y) x ⊆ (bankA D X Y).filter (Deep D (bankA D X Y) (r - 2)) :=
      fun a ha => mem_filter.mpr ⟨(mem_outN.mp ha).1, all a ha⟩
    have subB : outN D (bankB D X Y) x ⊆ (bankB D X Y).erase b := by
      intro y hy
      obtain ⟨ym, xy⟩ := mem_outN.mp hy
      refine mem_erase.mpr ⟨fun e => ?_, ym⟩
      subst e
      exact t.free x 2 (by omega) (by have := t.hq; have := t.five; omega)
        (.step (t.yv bm) xy (.step (t.xv xm) bx (.refl x)))
    have hA := card_le_card sub
    have hB := card_le_card subB
    rw [card_erase_of_mem bB] at hB
    have inner := deep_heads fx sx xm deep
    have heads := split_heads t xm
    have deg := t.degX x xm
    have cards := bank_card (D := D) (X := X) (Y := Y)
    have := t.cx; have := t.cy; have := t.five
    have bpos := card_pos.mpr ⟨b, bB⟩
    rcases deep_card (t := r - 2) (A_free t) (A_size t) with bound | empty
    · omega
    · rw [empty, card_empty] at hA
      omega
  obtain ⟨am, xa⟩ := mem_outN.mp ha
  simp only [Deep, not_forall, not_le, exists_prop] at shallow
  obtain ⟨s, sm, ks, k, walk, lt⟩ := shallow
  exact (Near.step (t.xv xm) bx (Near.step (AV am) xa (near_A t sm ks walk))).mono (by omega)

open scoped Classical in
/-- **Bank closure.** If `A` is nonempty (`P1`), every `X`-sink reaches an `A`-sink
within two steps (`P2`), `|B| ≤ 2` as soon as `X` has an `(r-2)`-deep row (`P3`), and
every row of `B` is a return tail or is near within `r` (`P4`), the four layers are
impossible. -/
theorem banks_false (t : Tight D V X Y Z W q r) (P1 : (bankA D X Y).Nonempty)
    (P2 : ∀ σ ∈ X, Sink D X σ → 2 ≤ (bankA D X Y).card ∨ bankA D X Y ⊆ outN D V σ)
    (P3 : ∀ x ∈ X, Deep D X (r - 2) x → (bankB D X Y).card ≤ 2)
    (P4 : ∀ b ∈ bankB D X Y, (∃ x ∈ X, D b x = true) ∨ Near D V Z b r) : False := by
  have AV : bankA D X Y ⊆ V := bankA_sub.trans t.yv
  have heads (z) (zm : z ∈ Z) :
      outN D V z ⊆ Z ∪ W ∪ (bankA D X Y).filter (Deep D (bankA D X Y) r) := by
    intro h hh
    have arc := (mem_outN.mp hh).2
    rcases mem_union.mp (t.headsZ z zm hh) with hxyz | hw
    · rcases mem_union.mp hxyz with hxy | hz
      · rcases mem_union.mp hxy with hx | hy
        · have deep := deep_of_target t P1 P2 zm hx arc
          exact (target_false t zm hx arc deep (P3 h hx deep)).elim
        · by_cases ret : Ret D X Y h
          · have hB : h ∈ bankB D X Y := mem_bankB.mpr ⟨hy, ret⟩
            rcases P4 h hB with ⟨x, xm, hx⟩ | near
            · exact (near_false t zm (t.yv hy) arc (tail_near t P1 P3 hy xm hx)).elim
            · exact (near_false t zm (t.yv hy) arc near).elim
          · have hA : h ∈ bankA D X Y := mem_bankA.mpr ⟨hy, ret⟩
            exact mem_union_right _ (mem_filter.mpr ⟨hA, A_target t zm hA arc⟩)
      · exact mem_union_left _ (mem_union_left _ hz)
    · exact mem_union_left _ (mem_union_right _ hw)
  have := t.cz; have := t.hq; have := t.five
  exact exit_false t.free t.zv ((filter_subset _ _).trans AV) (by omega) (by omega) (by omega)
    t.cw t.degZ (T_card t) (fun a ha => deep_A_omit t (mem_filter.mp ha).1 (mem_filter.mp ha).2) heads

end tight

#print axioms exit_false
#print axioms reach_A_sink
#print axioms target_false
#print axioms tail_near
#print axioms banks_false

end LeanCH.BR.TightWideBanks
