import checkpoints.shen_extension.TubeAtCutoff

/-!
# Two width patterns on the row `r = q + 1`

A root `u` of out-degree exactly `q + 1` in a `q`-free digraph of minimum out-degree `q + 1`;
`X, Y, Z, W` are its first four layers.

* **B1** `row_dip_fourth` (generic, `4 ≤ q`): widths `(q + 1, q + 1, ≤ q)` force a fourth layer
  of at least `q + 1`. Pattern `dipB1`, `dipB1_sound`; with the collar dip, `collarRowX_sound`.
* **B2** (widths `(q + 1, q + 1, q + 1)` force a fourth layer of at least `q`) is **not** proved.
  Proved: `flat_run_fourth_of_return` (`6 ≤ q`), B2 when every sink of `D[Y]` has a head in `X`
  (in particular when `D[Y]` has no sink); and `flat_run_residual` (`6 ≤ q`): a counterexample
  to B2 has a sink `t` of `D[Y]` whose heads are exactly `Z` and whose own second layer has at
  least `q + 1` labels. `dipB2Unproved` is the width pattern, for evaluation only.

Tools, all generic. In a set `S` of at most `q + 1` labels with a sink of `D[S]`, closed balls
contain sinks and `D[S]` has no closed walk (`closed_sink1`, `no_cycle1`), so the deep-ball
lemmas of `TubeAtCutoff` hold (`deep_grow1`, `deep_heads1`, `three_deep1`). For two sets
`X, Y` of `q + 1` labels with rows of `X` inside `X ∪ Y`:
* `no_return` (`4 ≤ q`): if `D[Y]` has no sink, no row of `Y` points into `X`. `Y` is then a loop
  with a parent everywhere, so a return `y → x` makes `x` miss the `q - 1` labels reaching `y`
  within `q - 2`; `x` then has `q - 1` heads in `X`. A loop `X` has one; if `X` has a sink `s`,
  `x` heads all of `X` except `x, s`, and a sink of `D[X - s]` closes a triangle or a 4-cycle
  through `s → y → x`.
* `no_sink_of_return` (`4 ≤ q`): if every sink of `D[Y]` points into `X`, `D[Y]` has no sink.
  If `X` is a loop, a return target misses only its tail: a parent of the tail closes a
  triangle, and two parentless returning sinks close a 4-cycle. If `X` has a sink, return
  targets are deep to radius `q - 2` in `X`, miss at most two labels of `Y` each, at most two
  labels are deep, and the ancestor sets of the sinks of `D[Y]` cover `Y` (`4 < q + 1`).
* `ball_two_floor` (`2 ≤ q`): every label has at least `2q + 2` labels within two steps
  (`LoopCollar.collar`).

B1 then: every sink of `D[Y]` returns (`|Z| ≤ q`), so `D[Y]` is a loop without returns, complete
to `Z`; `Z → X` closes a triangle through a `Y`-head, `Z → Y` a digon; a sink of `D[Z]` has all
`q + 1` heads in `W`.

Departure from the paper (degree-nine dossier, Appendix 22, "All 34-label fourth balls come from
an actual nine-cycle", `q = 8`): the case "X cyclic" is replaced by the loop argument above (no
nine-omission count, no exceptional label `y0`), and "X a DAG" uses the deep balls of
`TubeAtCutoff` in a set of `q + 1` labels with a sink instead of nearest-sink depths. The paper's
B2 ("Higher three-step reach is now priced", first bullet) is a reach count at `r = 9`; the two
proved B2 cases are new and generic, the residual case is open.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarRowDips
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open FlatAtCutoff (walk_first grow)
open TubeAtCutoff (IsSink Deep closed_sink pclosed_sink too_few full_of_sub closed_or_grow
  reach_or_grow rev walk_rev row_ball classify x_ball layer_in layer_out)

variable {D : CH.Digraph}

/-! ### Balls in a set of at most `q + 1` labels with a sink -/

section sinkset
variable {S : Finset ℕ} {q s0 : ℕ}

/-- A closed ball contains a sink of `D[S]`. -/
theorem closed_sink1 (free : QFree D S q) (hS : S.card ≤ q + 1) (hs0 : s0 ∈ S)
    (sk0 : IsSink D S s0) {v j : ℕ} (hv : v ∈ S)
    (cl : ∀ a ∈ ball D S v j, ∀ w ∈ S, D a w = true → w ∈ ball D S v j) :
    ∃ s ∈ ball D S v j, IsSink D S s := by
  by_cases sm : (ball D S v j).card ≤ q
  · exact closed_sink free hv sm cl
  · have full : ball D S v j = S := eq_of_subset_of_card_le ball_subset (by omega)
    exact ⟨s0, by rw [full]; exact hs0, sk0⟩

/-- No closed walk at all: a closed walk avoids the sink, so it lies in at most `q` labels. -/
theorem no_cycle1 (free : QFree D S q) (hS : S.card ≤ q + 1) (hs0 : s0 ∈ S)
    (sk0 : IsSink D S s0) {a n : ℕ} (hn : 1 ≤ n) (w : Walk D S a a n) : False := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have aW : a ∈ S := (w.unsnoc).choose_spec.2.1
  let C := S.filter (fun v => ∃ m, 1 ≤ m ∧ Walk D S v v m)
  have aC : a ∈ C := mem_filter.mpr ⟨aW, n' + 1, by omega, w⟩
  have s0C : s0 ∉ C := by
    intro h
    obtain ⟨-, m, hm, ws⟩ := mem_filter.mp h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨c, cW, sc, -⟩ := walk_first ws
    exact sk0 c cW sc
  have small : C.card ≤ q := by
    have : C.card < S.card :=
      card_lt_card ((ssubset_iff_of_subset (filter_subset _ S)).mpr ⟨s0, hs0, s0C⟩)
    omega
  obtain ⟨s, sC, sink⟩ := exists_sink (free.mono_set (filter_subset _ _)) ⟨a, aC⟩ small
  obtain ⟨sW, m, hm, ws⟩ := mem_filter.mp sC
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨c, cW, sc, wc⟩ := walk_first ws
  exact sink c (mem_filter.mpr ⟨cW, m' + 1, by omega, wc.snoc cW sc⟩) sc

theorem deep_open1 (free : QFree D S q) (hS : S.card ≤ q + 1) (hs0 : s0 ∈ S)
    (sk0 : IsSink D S s0) {m v : ℕ} (hv : v ∈ S) (dp : Deep D S m v) {j : ℕ} (hj : j ≤ m) :
    ∃ a ∈ ball D S v j, ∃ w ∈ S, D a w = true ∧ w ∉ ball D S v j := by
  by_contra hc
  have cl : ∀ a ∈ ball D S v j, ∀ w ∈ S, D a w = true → w ∈ ball D S v j :=
    fun a ha w hw aw => by_contra fun hn => hc ⟨a, ha, w, hw, aw, hn⟩
  obtain ⟨s, sB, sink⟩ := closed_sink1 free hS hs0 sk0 hv cl
  exact dp s (ball_mono_radius hj sB) sink

theorem deep_grow1 (free : QFree D S q) (hS : S.card ≤ q + 1) (hs0 : s0 ∈ S)
    (sk0 : IsSink D S s0) {m v : ℕ} (hv : v ∈ S) (dp : Deep D S m v) {k : ℕ} (hk : k ≤ m + 1) :
    k + 1 ≤ (ball D S v k).card := by
  have g := grow (W := S) (p := v) (a := 0) (M := k)
    (fun j _ hj => deep_open1 free hS hs0 sk0 hv dp (by omega))
  have one : 1 ≤ (ball D S v 0).card := card_pos.mpr ⟨v, self_mem_ball hv⟩
  rw [Nat.zero_add] at g
  omega

theorem deep_heads1 (free : QFree D S q) (hS : S.card ≤ q + 1) (hs0 : s0 ∈ S)
    (sk0 : IsSink D S s0) (hq : 1 ≤ q) {m v : ℕ} (hv : v ∈ S) (dp : Deep D S m v) :
    (outN D S v).card + m + 1 ≤ S.card := by
  have pp := loopfree free hq hv
  have sub : insert v (outN D S v) ⊆ ball D S v 1 := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact self_mem_ball hv
    · exact (mem_ball_one hv).mpr (Or.inr hw)
  have notin : v ∉ outN D S v := fun h => pp (mem_outN.mp h).2
  have c1 := card_le_card sub
  rw [card_insert_of_notMem notin] at c1
  have g := grow (W := S) (p := v) (a := 1) (M := m)
    (fun j _ hj => deep_open1 free hS hs0 sk0 hv dp (by omega))
  have cap : (ball D S v (1 + m)).card ≤ S.card := card_le_card ball_subset
  omega

/-- At most two labels are deep to radius `m` when `|S| ≤ m + 3`. -/
theorem three_deep1 (free : QFree D S q) (hS : S.card ≤ q + 1) (hs0 : s0 ∈ S)
    (sk0 : IsSink D S s0) {m a b c : ℕ}
    (hm : S.card ≤ m + 3) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ab : a ≠ b) (ac : a ≠ c)
    (bc : b ≠ c) (da : Deep D S m a) (db : Deep D S m b) (dc : Deep D S m c) : False := by
  classical
  have miss : ∀ v ∈ S, Deep D S m v → ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      x ∉ ball D S v (m + 1) → y ∉ ball D S v (m + 1) → False := by
    intro v hv dv x hx y hy xy nx ny
    have g := deep_grow1 free hS hs0 sk0 hv dv (le_refl (m + 1))
    have sub : ball D S v (m + 1) ⊆ (S.erase x).erase y := by
      intro w hw
      refine mem_erase.mpr ⟨fun h => ny (h ▸ hw), mem_erase.mpr ⟨fun h => nx (h ▸ hw), ball_subset hw⟩⟩
    have c := card_le_card sub
    have e1 := card_erase_add_one (mem_erase.mpr ⟨xy.symm, hy⟩)
    have e2 := card_erase_add_one hx
    omega
  have nc : ∀ x n, 1 ≤ n → Walk D S x x n → False := fun x n hn w =>
    no_cycle1 free hS hs0 sk0 hn w
  have mutl : ∀ x y, x ≠ y → x ∈ ball D S y (m + 1) → y ∈ ball D S x (m + 1) → False := by
    intro x y xy hx hy
    obtain ⟨-, i, -, wi⟩ := mem_ball.mp hy
    obtain ⟨-, j, -, wj⟩ := mem_ball.mp hx
    rcases Nat.eq_zero_or_pos i with rfl | ipos
    · exact xy (walk_zero wi)
    · exact nc x (i + j) (by omega) (wi.append wj)
  have tri : ∀ x y z, x ≠ y → y ∈ ball D S x (m + 1) → z ∈ ball D S y (m + 1) →
      x ∈ ball D S z (m + 1) → False := by
    intro x y z xy hy hz hx
    obtain ⟨-, i, -, wi⟩ := mem_ball.mp hy
    obtain ⟨-, j, -, wj⟩ := mem_ball.mp hz
    obtain ⟨-, k, -, wk⟩ := mem_ball.mp hx
    rcases Nat.eq_zero_or_pos i with rfl | ipos
    · exact xy (walk_zero wi)
    · exact nc x (i + j + k) (by omega) ((wi.append wj).append wk)
  by_cases rab : b ∈ ball D S a (m + 1)
  · have rbc : c ∈ ball D S b (m + 1) := by
      by_contra h
      exact miss b hb db a ha c hc ac (fun h' => mutl a b ab h' rab) h
    exact miss c hc dc a ha b hb ab (fun h' => tri a b c ab rab rbc h')
      (fun h' => mutl b c bc h' rbc)
  · have rac : c ∈ ball D S a (m + 1) := by
      by_contra h
      exact miss a ha da b hb c hc bc rab h
    have rcb : b ∈ ball D S c (m + 1) := by
      by_contra h
      exact miss c hc dc a ha b hb ab (fun h' => mutl a c ac h' rac) h
    exact miss b hb db a ha c hc ac (fun h' => tri a c b ac rac rcb h')
      (fun h' => mutl c b bc.symm h' rcb)

end sinkset

/-! ### Two layers of `q + 1` labels

`X, Y ⊆ V` with `q + 1` labels each, every row of `X` inside `X ∪ Y`. -/

section pair
variable {V X Y : Finset ℕ} {q : ℕ}

theorem x_split (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card) (hX : X ⊆ V)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y) :
    ∀ x ∈ X, q + 1 ≤ (outN D X x).card + (outN D Y x).card := by
  intro x hx
  have sub : outN D V x ⊆ outN D X x ∪ outN D Y x := by
    intro w hw
    obtain ⟨wV, xw⟩ := mem_outN.mp hw
    rcases rowX x hx w wV xw with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, xw⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨h, xw⟩)
  exact (deg x (hX hx)).trans ((card_le_card sub).trans (card_union_le _ _))

/-- Sinks of `D[X]` head all of `Y`. -/
theorem x_sink_full (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card) (hX : X ⊆ V)
    (cY : Y.card = q + 1) (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y) :
    ∀ s ∈ X, IsSink D X s → ∀ y ∈ Y, D s y = true := by
  intro s hs sink
  refine full_of_sub (V := V) ?_ cY.le (deg s (hX hs))
  intro w hw
  obtain ⟨wV, sw⟩ := mem_outN.mp hw
  rcases rowX s hs w wV sw with h | h
  · exact (sink w h sw).elim
  · exact h

/-- Every row of `X` has a head in `Y`. -/
theorem x_to_y (free : QFree D V q) (hq : 1 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (cX : X.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y) :
    ∀ x ∈ X, ∃ y ∈ Y, D x y = true := by
  intro p hp
  by_contra none
  have pp := loopfree free hq (hX hp)
  refine too_few (V := V) (T := X.erase p) ?_ (by rw [card_erase_of_mem hp]; omega) (deg p (hX hp))
  intro w hw
  obtain ⟨wV, pw⟩ := mem_outN.mp hw
  rcases rowX p hp w wV pw with h | h
  · exact mem_erase.mpr ⟨fun e => pp (e ▸ pw), h⟩
  · exact (none ⟨w, h, pw⟩).elim

/-- A set of `q + 1` labels without a sink is a loop: one head each. -/
theorem loop_of_noSink (free : QFree D V q) (hq : 1 ≤ q) (hX : X ⊆ V) (cX : X.card = q + 1)
    (ns : ∀ x ∈ X, ¬ IsSink D X x) : ∀ x ∈ X, (outN D X x).card = 1 :=
  LoopCollar.loop_unique_head (free.mono_set hX) hq cX (fun x hx => by
    by_contra h
    have e : outN D X x = ∅ := card_eq_zero.mp (by omega)
    exact ns x hx (fun w hw xw => by
      have : w ∈ outN D X x := mem_outN.mpr ⟨hw, xw⟩
      rw [e] at this
      exact absurd this (notMem_empty w)))

/-- A set of `q + 1` labels without a sink: every label has a parent inside. -/
theorem parent_of_noSink (free : QFree D V q) (hq : 1 ≤ q) (hY : Y ⊆ V) (cY : Y.card = q + 1)
    (ns : ∀ y ∈ Y, ¬ IsSink D Y y) : ∀ y ∈ Y, ∃ a ∈ Y, D a y = true := by
  intro y hy
  by_contra none
  obtain ⟨y1, y1Y, y1n⟩ := exists_mem_notMem_of_card_lt_card (s := {y}) (t := Y)
    (by rw [card_singleton]; omega)
  have pc : ∀ a ∈ Y, ∀ b ∈ ({y} : Finset ℕ), D a b = true → a ∈ ({y} : Finset ℕ) := by
    intro a aY b hb ab
    rw [mem_singleton.mp hb] at ab
    exact (none ⟨a, aY, ab⟩).elim
  obtain ⟨s, sY, sk⟩ := pclosed_sink (free.mono_set hY) cY.le (singleton_subset_iff.mpr hy)
    (mem_singleton_self y) y1Y y1n pc
  exact ns s sY sk

/-- **No return from a loop.** If `D[Y]` has no sink, no row of `Y` points into `X`. -/
theorem no_return (free : QFree D V q) (hq : 4 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    (ns : ∀ y ∈ Y, ¬ IsSink D Y y) : ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true := by
  classical
  intro y0 hy0 x hx y0x
  have fX : QFree D X q := free.mono_set hX
  have fY : QFree D Y q := free.mono_set hY
  have parent := parent_of_noSink free (by omega) hY cY ns
  have rfree : QFree (rev D) Y q := fun a l h1 h2 w => by
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have aY : a ∈ Y := (w.unsnoc).choose_spec.2.1
    exact fY a (l' + 1) h1 h2 (walk_rev aY w)
  have rdeg : ∀ v ∈ Y, 1 ≤ (outN (rev D) Y v).card := by
    intro v hv
    obtain ⟨a, aY, av⟩ := parent v hv
    exact card_pos.mpr ⟨a, mem_outN.mpr ⟨aY, av⟩⟩
  have big := LoopCollar.ball_grow rfree rdeg hy0 (q - 2) (by omega)
  have miss : ∀ a ∈ ball (rev D) Y y0 (q - 2), ¬ D x a = true := by
    intro a ha xa
    obtain ⟨aY, j, hj, wj⟩ := mem_ball.mp ha
    have w' : Walk D Y a y0 j := walk_rev hy0 wj
    exact free x (j + 2) (by omega) (by omega) (.step (hY aY) xa ((w'.mono hY).snoc (hX hx) y0x))
  have fewY : (outN D Y x).card ≤ 2 := by
    have sub : outN D Y x ⊆ Y \ ball (rev D) Y y0 (q - 2) := fun w hw =>
      mem_sdiff.mpr ⟨(mem_outN.mp hw).1, fun h => miss w h (mem_outN.mp hw).2⟩
    have := card_le_card sub
    rw [card_sdiff_of_subset ball_subset] at this
    omega
  have split := x_split deg hX rowX x hx
  by_cases hasSink : ∃ s ∈ X, IsSink D X s
  · obtain ⟨s0, hs0, sk0⟩ := hasSink
    have full := x_sink_full deg hX cY rowX
    have s0y0 := full s0 hs0 sk0 y0 hy0
    have xs0 : ¬ D x s0 = true := fun h => free x 3 (by omega) (by omega)
      (.step (hX hs0) h (.step (hY hy0) s0y0 (.step (hX hx) y0x (.refl x))))
    have xne : x ≠ s0 := by
      rintro rfl
      obtain ⟨w, hw⟩ : (outN D X x).Nonempty := card_pos.mp (by omega)
      exact sk0 w (mem_outN.mp hw).1 (mem_outN.mp hw).2
    have sub : outN D X x ⊆ (X.erase s0).erase x := by
      intro w hw
      obtain ⟨wX, xw⟩ := mem_outN.mp hw
      refine mem_erase.mpr ⟨fun e => loopfree free (by omega) (hX hx) (e ▸ xw),
        mem_erase.mpr ⟨fun e => xs0 (e ▸ xw), wX⟩⟩
    have c1 : ((X.erase s0).erase x).card + 2 = q + 1 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨xne, hx⟩), card_erase_of_mem hs0]
      omega
    have fullX : outN D X x = (X.erase s0).erase x := eq_of_subset_of_card_le sub (by omega)
    obtain ⟨h0, h0X', h0sk⟩ := exists_sink (fX.mono_set (erase_subset _ _))
      ⟨x, mem_erase.mpr ⟨xne, hx⟩⟩ (by rw [card_erase_of_mem hs0]; omega)
    have h0X : h0 ∈ X := mem_of_mem_erase h0X'
    have h0x : h0 ≠ x := by
      rintro rfl
      obtain ⟨w, hw⟩ : (outN D X h0).Nonempty := card_pos.mp (by omega)
      exact h0sk w (mem_of_mem_erase (sub hw)) (mem_outN.mp hw).2
    have xh0 : D x h0 = true := by
      have : h0 ∈ outN D X x := by rw [fullX]; exact mem_erase.mpr ⟨h0x, h0X'⟩
      exact (mem_outN.mp this).2
    by_cases h0s0 : D h0 s0 = true
    · exact free x 4 (by omega) (by omega) (.step (hX h0X) xh0 (.step (hX hs0) h0s0
        (.step (hY hy0) s0y0 (.step (hX hx) y0x (.refl x)))))
    · have h0sink : IsSink D X h0 := fun w hw hw' => by
        by_cases e : w = s0
        · exact h0s0 (e ▸ hw')
        · exact h0sk w (mem_erase.mpr ⟨e, hw⟩) hw'
      have h0y0 := full h0 h0X h0sink y0 hy0
      exact free x 3 (by omega) (by omega) (.step (hX h0X) xh0 (.step (hY hy0) h0y0
        (.step (hX hx) y0x (.refl x))))
  · have ns' : ∀ s ∈ X, ¬ IsSink D X s := fun s hs sk => hasSink ⟨s, hs, sk⟩
    have one := loop_of_noSink free (by omega) hX cX ns' x hx
    omega

/-- **Returning sinks.** If every sink of `D[Y]` points into `X`, then `D[Y]` has no sink. -/
theorem no_sink_of_return (free : QFree D V q) (hq : 4 ≤ q)
    (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    (ret : ∀ t ∈ Y, IsSink D Y t → ∃ x ∈ X, D t x = true) : ∀ t ∈ Y, ¬ IsSink D Y t := by
  classical
  intro t0 ht0 sk
  have fX : QFree D X q := free.mono_set hX
  have fY : QFree D Y q := free.mono_set hY
  have split := x_split deg hX rowX
  by_cases hasSink : ∃ s ∈ X, IsSink D X s
  · -- `X` has a sink: return targets are deep in `X`
    obtain ⟨s0, hs0, sk0⟩ := hasSink
    have full := x_sink_full deg hX cY rowX
    have cX' : X.card ≤ q + 1 := cX.le
    have tgt : ∀ t ∈ Y, ∀ x ∈ X, D t x = true → Deep D X (q - 2) x := by
      intro t ht x hx tx s hs sink
      obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
      exact free x (j + 2) (by omega) (by omega)
        (((wj.mono hX).snoc (hY ht) (full s (ball_subset hs) sink t ht)).snoc (hX hx) tx)
    set Om : ℕ → Finset ℕ := fun p => Y.filter (fun a => ¬ D p a = true) with hOm
    have omDeep : ∀ p ∈ X, Deep D X (q - 2) p → (Om p).card ≤ 2 := by
      intro p hp dp
      have h1 := deep_heads1 fX cX' hs0 sk0 (by omega) hp dp
      have e : (outN D Y p).card + (Om p).card = Y.card :=
        card_filter_add_card_filter_not (s := Y) (fun a => D p a = true)
      have := split p hp
      omega
    set Anc : ℕ → Finset ℕ := fun t => Y.filter (fun a => ∃ n, Walk D Y a t n) with hAnc
    have retL : ∀ t ∈ Y, ∀ p ∈ X, D t p = true → Anc t ⊆ Om p := by
      intro t ht p hp tp y hy
      obtain ⟨yY, n, wn⟩ := mem_filter.mp hy
      refine mem_filter.mpr ⟨yY, fun py => ?_⟩
      have RO : ball (rev D) Y t (q - 2) ⊆ Om p := by
        intro a ha
        obtain ⟨aY, j, hj, wj⟩ := mem_ball.mp ha
        have w' : Walk D Y a t j := walk_rev ht wj
        exact mem_filter.mpr ⟨aY, fun pa => free p (j + 2) (by omega) (by omega)
          (.step (hY aY) pa ((w'.mono hY).snoc (hX hp) tp))⟩
      have yR : y ∈ ball (rev D) Y t n := mem_ball.mpr ⟨yY, n, le_rfl, walk_rev yY wn⟩
      have h3 := omDeep p hp (tgt t ht p hp tp)
      rcases reach_or_grow (D := rev D) (M := q - 2) ht yR with h | h
      · exact (mem_filter.mp (RO h)).2 py
      · have := card_le_card RO
        omega
    have reach : ∀ y ∈ Y, ∃ t ∈ Y, IsSink D Y t ∧ y ∈ Anc t := by
      intro y hy
      rcases closed_or_grow (D := D) (S := Y) (v := y) (a := 0) (M := q + 1) with ⟨j, -, -, cl⟩ | g
      · by_cases sm : (ball D Y y j).card ≤ q
        · obtain ⟨s, hs, sk⟩ := closed_sink fY hy sm cl
          obtain ⟨sY, i, -, wi⟩ := mem_ball.mp hs
          exact ⟨s, sY, sk, mem_filter.mpr ⟨hy, i, wi⟩⟩
        · have fullY : ball D Y y j = Y := eq_of_subset_of_card_le ball_subset (by omega)
          have t0b : t0 ∈ ball D Y y j := by rw [fullY]; exact ht0
          obtain ⟨-, i, -, wi⟩ := mem_ball.mp t0b
          exact ⟨t0, ht0, sk, mem_filter.mpr ⟨hy, i, wi⟩⟩
      · have one : 1 ≤ (ball D Y y 0).card := card_pos.mpr ⟨y, self_mem_ball hy⟩
        have cap : (ball D Y y (0 + (q + 1))).card ≤ Y.card := card_le_card ball_subset
        omega
    set dX := X.filter (fun p => Deep D X (q - 2) p) with hdX
    have cover : Y ⊆ dX.biUnion Om := by
      intro y hy
      obtain ⟨t, tY, tsk, yA⟩ := reach y hy
      obtain ⟨p, hp, tp⟩ := ret t tY tsk
      exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨hp, tgt t tY p hp tp⟩, retL t tY p hp tp yA⟩
    have c2 : (dX.biUnion Om).card ≤ dX.card * 2 :=
      card_biUnion_le_card_mul _ _ _ (fun p hp => omDeep p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
    have cd : dX.card ≤ 2 := by
      by_contra! h
      obtain ⟨a, ha, b, hb, c, hc, ab, ac, bc⟩ := two_lt_card.mp h
      exact three_deep1 fX cX' hs0 sk0 (by omega) (mem_filter.mp ha).1 (mem_filter.mp hb).1
        (mem_filter.mp hc).1 ab ac bc (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2
    have := card_le_card cover
    omega
  · -- `X` is a loop: each row of `X` misses at most one label of `Y`
    have ns' : ∀ s ∈ X, ¬ IsSink D X s := fun s hs sk => hasSink ⟨s, hs, sk⟩
    have one := loop_of_noSink free (by omega) hX cX ns'
    have omit1 : ∀ x ∈ X, ∀ t ∈ Y, D t x = true → ∀ y ∈ Y, y ≠ t → D x y = true := by
      intro x hx t ht tx y hy yt
      have sub : outN D Y x ⊆ Y.erase t := fun w hw => mem_erase.mpr
        ⟨fun e => digonfree free (by omega) (hX hx) (hY ht) (e ▸ (mem_outN.mp hw).2) tx,
          (mem_outN.mp hw).1⟩
      have c := split x hx
      rw [one x hx] at c
      have fullY : outN D Y x = Y.erase t :=
        eq_of_subset_of_card_le sub (by rw [card_erase_of_mem ht]; omega)
      have : y ∈ outN D Y x := by rw [fullY]; exact mem_erase.mpr ⟨yt, hy⟩
      exact (mem_outN.mp this).2
    obtain ⟨x0, hx0, t0x0⟩ := ret t0 ht0 sk
    by_cases par : ∃ a ∈ Y, D a t0 = true
    · obtain ⟨a, aY, at0⟩ := par
      have ne : a ≠ t0 := fun e => loopfree free (by omega) (hY ht0) (e ▸ at0)
      exact free x0 3 (by omega) (by omega) (.step (hY aY) (omit1 x0 hx0 t0 ht0 t0x0 a aY ne)
        (.step (hY ht0) at0 (.step (hX hx0) t0x0 (.refl x0))))
    · obtain ⟨t1, t1Y', t1sk⟩ := exists_sink (fY.mono_set (erase_subset t0 Y))
        (card_pos.mp (by rw [card_erase_of_mem ht0]; omega)) (by rw [card_erase_of_mem ht0]; omega)
      have t1Y := mem_of_mem_erase t1Y'
      have t1ne := ne_of_mem_erase t1Y'
      have t1sink : IsSink D Y t1 := fun w hw tw => by
        by_cases e : w = t0
        · exact par ⟨t1, t1Y, e ▸ tw⟩
        · exact t1sk w (mem_erase.mpr ⟨e, hw⟩) tw
      obtain ⟨x1, hx1, t1x1⟩ := ret t1 t1Y t1sink
      have a := omit1 x0 hx0 t0 ht0 t0x0 t1 t1Y t1ne
      have b := omit1 x1 hx1 t1 t1Y t1x1 t0 ht0 t1ne.symm
      exact free t0 4 (by omega) (by omega) (.step (hX hx0) t0x0 (.step (hY t1Y) a
        (.step (hX hx1) t1x1 (.step (hY ht0) b (.refl t0)))))

end pair

/-! ### Target B1 -/

/-- **B1: a dip after a flat start on the row `r = q + 1`.** A root with exactly `q + 1` heads and
exactly `q + 1` labels in its second layer, at most `q` in its third, in a `q`-free digraph of
minimum out-degree at least `q + 1`, `4 ≤ q`, has at least `q + 1` labels in its fourth layer. -/
theorem row_dip_fourth {V : Finset ℕ} {q u : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (second : (layer D V 2 u).card = q + 1) (third : (layer D V 3 u).card ≤ q) :
    q + 1 ≤ (layer D V 4 u).card := by
  classical
  by_contra! thin
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set W := layer D V 4 u with hWdef
  have hX : X ⊆ V := outN_subset
  have hY : Y ⊆ V := fun w hw => ball_subset (layer_in hw)
  have hZ : Z ⊆ V := fun w hw => ball_subset (layer_in hw)
  have fY : QFree D Y q := free.mono_set hY
  have fZ : QFree D Z q := free.mono_set hZ
  have rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y := by
    intro x hx w wV xw
    obtain ⟨wu, wb⟩ := row_ball free (x_ball hu hx) wV xw (by omega)
    rcases classify hu (ball_mono_radius (by omega) wb) wu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (layer_out h le_rfl wb).elim
    · exact (layer_out h (by omega) wb).elim
  have rowY : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z := by
    intro y hy w wV yw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hy) wV yw (by omega)
    rcases classify hu (ball_mono_radius (by omega) wb) wu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (layer_out h le_rfl wb).elim
  have rowZ : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z ∨ w ∈ W := by
    intro z hz w wV zw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hz) wV zw (by omega)
    exact classify hu wb wu
  -- every sink of `D[Y]` returns into `X`, since `Z` is too small
  have ret : ∀ t ∈ Y, IsSink D Y t → ∃ x ∈ X, D t x = true := by
    intro t ht sink
    by_contra none
    refine too_few (V := V) (T := Z) ?_ (by omega) (deg t (hY ht))
    intro w hw
    obtain ⟨wV, tw⟩ := mem_outN.mp hw
    rcases rowY t ht w wV tw with h | h | h
    · exact (none ⟨w, h, tw⟩).elim
    · exact (sink w h tw).elim
    · exact h
  have ns := no_sink_of_return free hq deg hX hY heads second rowX ret
  have one := loop_of_noSink free (by omega) hY second ns
  have noret := no_return free hq deg hX hY heads second rowX ns
  -- so `Y` is complete to `Z`
  have fullZ : ∀ y ∈ Y, ∀ z ∈ Z, D y z = true := by
    intro y hy
    have sub : outN D V y ⊆ outN D Y y ∪ outN D Z y := by
      intro w hw
      obtain ⟨wV, yw⟩ := mem_outN.mp hw
      rcases rowY y hy w wV yw with h | h | h
      · exact (noret y hy w h yw).elim
      · exact mem_union_left _ (mem_outN.mpr ⟨h, yw⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h, yw⟩)
    have c := (deg y (hY hy)).trans ((card_le_card sub).trans (card_union_le _ _))
    rw [one y hy] at c
    have eq : outN D Z y = Z := eq_of_subset_of_card_le outN_subset (by omega)
    intro z hz
    rw [← eq] at hz
    exact (mem_outN.mp hz).2
  have pY := x_to_y free (by omega) deg hX heads rowX
  have zrow : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ Z ∨ w ∈ W := by
    intro z hz w wV zw
    rcases rowZ z hz w wV zw with h | h | h | h
    · obtain ⟨y, yY, wy⟩ := pY w h
      exact (free w 3 (by omega) (by omega) (.step (hY yY) wy
        (.step (hZ hz) (fullZ y yY z hz) (.step wV zw (.refl w))))).elim
    · exact (digonfree free (by omega) (hY h) (hZ hz) (fullZ w h z hz) zw).elim
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨y0, hy0⟩ : Y.Nonempty := card_pos.mp (by omega)
  have cZ : q ≤ Z.card := by
    have := card_le_card (outN_subset (D := D) (W := Z) (y := y0))
    have sub : outN D V y0 ⊆ outN D Y y0 ∪ outN D Z y0 := by
      intro w hw
      obtain ⟨wV, yw⟩ := mem_outN.mp hw
      rcases rowY y0 hy0 w wV yw with h | h | h
      · exact (noret y0 hy0 w h yw).elim
      · exact mem_union_left _ (mem_outN.mpr ⟨h, yw⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h, yw⟩)
    have c := (deg y0 (hY hy0)).trans ((card_le_card sub).trans (card_union_le _ _))
    rw [one y0 hy0] at c
    omega
  obtain ⟨t, tZ, tsink⟩ := exists_sink fZ (card_pos.mp (by omega)) third
  refine too_few (V := V) (T := W) ?_ (by omega) (deg t (hZ tZ))
  intro w hw
  obtain ⟨wV, tw⟩ := mem_outN.mp hw
  rcases zrow t tZ w wV tw with h | h
  · exact (tsink w h tw).elim
  · exact h

/-! ### Target B2, the case without a forward sink -/

/-- **B2 when every sink of `D[Y]` points back into `X`.** A root with exactly `q + 1` heads and
exactly `q + 1` labels in its second and third layers, in a `q`-free digraph of minimum
out-degree at least `q + 1`, `6 ≤ q`, such that every sink of `D[Y]` (if any) has a head in `X`:
the fourth layer has at least `q` labels. -/
theorem flat_run_fourth_of_return {V : Finset ℕ} {q u : ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (hu : u ∈ V) (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (second : (layer D V 2 u).card = q + 1) (third : (layer D V 3 u).card = q + 1)
    (back : ∀ t ∈ layer D V 2 u, IsSink D (layer D V 2 u) t → ∃ x ∈ outN D V u, D t x = true) :
    q ≤ (layer D V 4 u).card := by
  classical
  by_contra! thin
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set W := layer D V 4 u with hWdef
  have hX : X ⊆ V := outN_subset
  have hY : Y ⊆ V := fun w hw => ball_subset (layer_in hw)
  have hZ : Z ⊆ V := fun w hw => ball_subset (layer_in hw)
  have fY : QFree D Y q := free.mono_set hY
  have fZ : QFree D Z q := free.mono_set hZ
  have rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y := by
    intro x hx w wV xw
    obtain ⟨wu, wb⟩ := row_ball free (x_ball hu hx) wV xw (by omega)
    rcases classify hu (ball_mono_radius (by omega) wb) wu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (layer_out h le_rfl wb).elim
    · exact (layer_out h (by omega) wb).elim
  have rowY : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z := by
    intro y hy w wV yw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hy) wV yw (by omega)
    rcases classify hu (ball_mono_radius (by omega) wb) wu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (layer_out h le_rfl wb).elim
  have rowZ : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z ∨ w ∈ W := by
    intro z hz w wV zw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hz) wV zw (by omega)
    exact classify hu wb wu
  have ns := no_sink_of_return free (by omega) deg hX hY heads second rowX back
  have one := loop_of_noSink free (by omega) hY second ns
  have noret := no_return free (by omega) deg hX hY heads second rowX ns
  have pY := x_to_y free (by omega) deg hX heads rowX
  -- each row of `Y` misses at most one label of `Z`
  have zHeads : ∀ y ∈ Y, q ≤ (outN D Z y).card := by
    intro y hy
    have sub : outN D V y ⊆ outN D Y y ∪ outN D Z y := by
      intro w hw
      obtain ⟨wV, yw⟩ := mem_outN.mp hw
      rcases rowY y hy w wV yw with h | h | h
      · exact (noret y hy w h yw).elim
      · exact mem_union_left _ (mem_outN.mpr ⟨h, yw⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h, yw⟩)
    have c := (deg y (hY hy)).trans ((card_le_card sub).trans (card_union_le _ _))
    rw [one y hy] at c
    omega
  have omit1 : ∀ y ∈ Y, ∀ a ∈ Z, ∀ b ∈ Z, ¬ D y a = true → ¬ D y b = true → a = b := by
    intro y hy a ha b hb na nb
    by_contra ne
    have := TubeAtCutoff.card_two_out (outN_subset (D := D) (W := Z) (y := y)) ha hb
      (fun h => na (mem_outN.mp h).2) (fun h => nb (mem_outN.mp h).2) ne
    have := zHeads y hy
    omega
  have grow1 : ∀ y ∈ Y, ∀ j, j ≤ q → j + 1 ≤ (ball D Y y j).card :=
    fun y hy => LoopCollar.ball_grow fY (fun v hv => (one v hv).ge) hy
  -- a returning row of `Z` is missed by at least `q - 2` rows of `Y`
  set O : ℕ → Finset ℕ := fun z => Y.filter (fun y => ¬ D y z = true) with hO
  have retO : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ X ∨ w ∈ Y → q - 2 ≤ (O z).card := by
    intro z hz w wV zw hw
    rcases hw with wX | wY
    · obtain ⟨y, yY, wy⟩ := pY w wX
      have sub : ball D Y y (q - 3) ⊆ O z := by
        intro v hv
        obtain ⟨vY, j, hj, wj⟩ := mem_ball.mp hv
        exact mem_filter.mpr ⟨vY, fun vz => free w (j + 3) (by omega) (by omega)
          (.step (hY yY) wy (((wj.mono hY).snoc (hZ hz) vz).snoc wV zw))⟩
      have := card_le_card sub
      have := grow1 y yY (q - 3) (by omega)
      omega
    · have sub : ball D Y w (q - 2) ⊆ O z := by
        intro v hv
        obtain ⟨vY, j, hj, wj⟩ := mem_ball.mp hv
        exact mem_filter.mpr ⟨vY, fun vz => free w (j + 2) (by omega) (by omega)
          (((wj.mono hY).snoc (hZ hz) vz).snoc wV zw)⟩
      have := card_le_card sub
      have := grow1 w wY (q - 2) (by omega)
      omega
  -- so at most one row of `Z` returns
  have once : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, ∀ w₁ ∈ V, ∀ w₂ ∈ V, D z₁ w₁ = true → D z₂ w₂ = true →
      (w₁ ∈ X ∨ w₁ ∈ Y) → (w₂ ∈ X ∨ w₂ ∈ Y) → z₁ = z₂ := by
    intro z₁ h₁ z₂ h₂ w₁ v₁ w₂ v₂ a₁ a₂ b₁ b₂
    by_contra ne
    have o₁ := retO z₁ h₁ w₁ v₁ a₁ b₁
    have o₂ := retO z₂ h₂ w₂ v₂ a₂ b₂
    have dj : Disjoint (O z₁) (O z₂) := by
      rw [disjoint_left]
      intro y hy hy'
      exact ne (omit1 y (mem_filter.mp hy).1 z₁ h₁ z₂ h₂ (mem_filter.mp hy).2 (mem_filter.mp hy').2)
    have := card_union_of_disjoint dj
    have := card_le_card (union_subset (filter_subset _ Y) (filter_subset _ Y) :
      O z₁ ∪ O z₂ ⊆ Y)
    omega
  obtain ⟨z0, hz0, keep⟩ : ∃ z0 ∈ Z, ∀ z ∈ Z, z ≠ z0 → ∀ w ∈ V, D z w = true → w ∈ Z ∨ w ∈ W := by
    by_cases some : ∃ z ∈ Z, ∃ w ∈ V, D z w = true ∧ (w ∈ X ∨ w ∈ Y)
    · obtain ⟨z0, hz0, w0, w0V, zw0, hw0⟩ := some
      refine ⟨z0, hz0, fun z hz ne w wV zw => ?_⟩
      rcases rowZ z hz w wV zw with h | h | h | h
      · exact (ne (once z hz z0 hz0 w wV w0 w0V zw zw0 (Or.inl h) hw0)).elim
      · exact (ne (once z hz z0 hz0 w wV w0 w0V zw zw0 (Or.inr h) hw0)).elim
      · exact Or.inl h
      · exact Or.inr h
    · obtain ⟨z0, hz0⟩ : Z.Nonempty := card_pos.mp (by omega)
      refine ⟨z0, hz0, fun z hz _ w wV zw => ?_⟩
      rcases rowZ z hz w wV zw with h | h | h | h
      · exact (some ⟨z, hz, w, wV, zw, Or.inl h⟩).elim
      · exact (some ⟨z, hz, w, wV, zw, Or.inr h⟩).elim
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨t, tZ', tsink⟩ := exists_sink (fZ.mono_set (erase_subset z0 Z))
    (card_pos.mp (by rw [card_erase_of_mem hz0]; omega)) (by rw [card_erase_of_mem hz0]; omega)
  have tZ := mem_of_mem_erase tZ'
  refine too_few (V := V) (T := insert z0 W) ?_
    (by have := card_insert_le z0 W; omega) (deg t (hZ tZ))
  intro w hw
  obtain ⟨wV, tw⟩ := mem_outN.mp hw
  rcases keep t tZ (ne_of_mem_erase tZ') w wV tw with h | h
  · by_cases e : w = z0
    · rw [e]; exact mem_insert_self _ _
    · exact (tsink w (mem_erase.mpr ⟨e, h⟩) tw).elim
  · exact mem_insert_of_mem h

/-- **Two-ball floor on the row.** In a `q`-free digraph of minimum out-degree at least `q + 1`,
every label has at least `2q + 2` labels within two steps (`LoopCollar.collar`). -/
theorem ball_two_floor {V : Finset ℕ} {q v : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (deg : ∀ w ∈ V, q + 1 ≤ (outN D V w).card) (hv : v ∈ V) :
    2 * q + 2 ≤ (ball D V v 2).card := by
  obtain ⟨E, -, -, root, degE, freeE, balls⟩ := ShapeClimbRoot.exact_root (deg v hv) free deg
  refine le_trans ?_ (card_le_card (balls 2))
  have b1 := ReachLedger.ball_one freeE (by omega) hv
  have s : (ball E V v 2).card = (layer E V 2 v).card + (ball E V v 1).card :=
    ShapeClimbRoot.card_ball_succ (D := E) (V := V) (u := v) 1
  by_contra! small
  have thin : (layer E V 2 v).card + 1 ≤ q + 1 := by omega
  obtain ⟨-, width, -⟩ := LoopCollar.collar (r := q + 1) freeE hq hv root
    (fun x hx => degE x (outN_subset hx)) thin
  omega

/-- **What is left of B2.** A root with widths `(q + 1, q + 1, q + 1)` and a fourth layer of at
most `q - 1` labels, `6 ≤ q`: some label `t` of the second layer has exactly the third layer as
its heads (a sink of `D[Y]` that does not point back), and `t` itself has at least `q + 1` labels
in its own second layer. (Otherwise either every sink of `D[Y]` points back,
`flat_run_fourth_of_return`, or `t` is a collar root whose second layer is a common head of the
whole third layer; such a head `p` lies in `X ∪ Y`, cannot see the third layer within two steps,
so its two-ball misses a label of `X ∪ Y`, against `ball_two_floor`.) -/
theorem flat_run_residual {V : Finset ℕ} {q u : ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (hu : u ∈ V) (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (second : (layer D V 2 u).card = q + 1) (third : (layer D V 3 u).card = q + 1)
    (thin : (layer D V 4 u).card + 1 ≤ q) :
    ∃ t ∈ layer D V 2 u, outN D V t = layer D V 3 u ∧ q + 1 ≤ (layer D V 2 t).card := by
  classical
  by_contra hno
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set W := layer D V 4 u with hWdef
  have hX : X ⊆ V := outN_subset
  have hY : Y ⊆ V := fun w hw => ball_subset (layer_in hw)
  have hZ : Z ⊆ V := fun w hw => ball_subset (layer_in hw)
  have rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y := by
    intro x hx w wV xw
    obtain ⟨wu, wb⟩ := row_ball free (x_ball hu hx) wV xw (by omega)
    rcases classify hu (ball_mono_radius (by omega) wb) wu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (layer_out h le_rfl wb).elim
    · exact (layer_out h (by omega) wb).elim
  have rowY : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z := by
    intro y hy w wV yw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hy) wV yw (by omega)
    rcases classify hu (ball_mono_radius (by omega) wb) wu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (layer_out h le_rfl wb).elim
  have rowZ : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z ∨ w ∈ W := by
    intro z hz w wV zw
    obtain ⟨wu, wb⟩ := row_ball free (layer_in hz) wV zw (by omega)
    exact classify hu wb wu
  -- a label of `Y` with a head in `Z`
  obtain ⟨z1, hz1⟩ : Z.Nonempty := card_pos.mp (by omega)
  obtain ⟨y1, y1b, y1z1⟩ := ball_succ_pred hu (layer_in hz1) (layer_out hz1 le_rfl)
  have y1Y : y1 ∈ Y := by
    refine mem_layer.mpr ⟨y1b, fun h => ?_⟩
    exact layer_out hz1 le_rfl (ball_step h (hZ hz1) y1z1)
  have back : ∀ t ∈ Y, IsSink D Y t → ∃ x ∈ X, D t x = true := by
    intro t ht sk
    by_contra none
    have tV := hY ht
    have sub : outN D V t ⊆ Z := by
      intro w hw
      obtain ⟨wV, tw⟩ := mem_outN.mp hw
      rcases rowY t ht w wV tw with h | h | h
      · exact (none ⟨w, h, tw⟩).elim
      · exact (sk w h tw).elim
      · exact h
    have eqZ : outN D V t = Z := eq_of_subset_of_card_le sub (by have := deg t tV; omega)
    have small : (layer D V 2 t).card ≤ q := by
      by_contra! big
      exact hno ⟨t, ht, eqZ, big⟩
    have rootT : (outN D V t).card = q + 1 := by rw [eqZ]; exact third
    obtain ⟨-, width, all⟩ := LoopCollar.collar (r := q + 1) free (by omega) tV rootT
      (fun x hx => deg x (outN_subset hx)) (by omega)
    -- a common head `p` of `Z` outside `W`
    obtain ⟨p, hp2, pW⟩ := exists_mem_notMem_of_card_lt_card (s := W) (t := layer D V 2 t)
      (by omega)
    have pb : p ∈ ball D V t 2 := (mem_layer.mp hp2).1
    have pV : p ∈ V := ball_subset pb
    obtain ⟨z2, z2b, z2p⟩ := ball_succ_pred tV pb (layer_out hp2 le_rfl)
    have z2Z : z2 ∈ Z := by
      rcases (mem_ball_one tV).mp z2b with rfl | h
      · exact (layer_out hp2 le_rfl ((mem_ball_one tV).mpr (Or.inr (mem_outN.mpr ⟨pV, z2p⟩)))).elim
      · rw [← eqZ]; exact h
    have pXY : p ∈ X ∨ p ∈ Y := by
      rcases rowZ z2 z2Z p pV z2p with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (layer_out hp2 le_rfl ((mem_ball_one tV).mpr (Or.inr (eqZ ▸ h)))).elim
      · exact (pW h).elim
    have allZ : ∀ z ∈ Z, D z p = true := by
      intro z hz
      have hz' : z ∈ outN D V t := by rw [eqZ]; exact hz
      exact (mem_outN.mp ((all z hz').2 hp2)).2
    have noZ : ∀ v ∈ ball D V p 2, ∀ z ∈ Z, ¬ D v z = true := by
      intro v hv z hz vz
      obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hv
      exact free z (j + 2) (by omega) (by omega) (.step pV (allZ z hz) (wj.snoc (hZ hz) vz))
    have inXY : ∀ k, k ≤ 2 → ∀ v ∈ ball D V p k, v ∈ X ∨ v ∈ Y := by
      intro k
      induction k with
      | zero =>
        intro _ v hv
        obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hv
        obtain rfl : j = 0 := by omega
        rw [← walk_zero wj]
        exact pXY
      | succ k ih =>
        intro hk v hv
        by_cases old : v ∈ ball D V p k
        · exact ih (by omega) v old
        · obtain ⟨a, ab, av⟩ := ball_succ_pred pV hv old
          have vV : v ∈ V := ball_subset hv
          rcases ih (by omega) a ab with aX | aY
          · exact rowX a aX v vV av
          · rcases rowY a aY v vV av with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact (noZ a (ball_mono_radius (by omega) ab) v h av).elim
    have sub : ball D V p 2 ⊆ (X ∪ Y).erase y1 := by
      intro v hv
      refine mem_erase.mpr ⟨fun e => noZ v hv z1 hz1 (e ▸ y1z1), ?_⟩
      rcases inXY 2 le_rfl v hv with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ h
    have c1 := card_le_card sub
    rw [card_erase_of_mem (mem_union_right _ y1Y)] at c1
    have c2 := card_union_le X Y
    have fl := ball_two_floor free (by omega) deg pV
    omega
  have h4 : q ≤ W.card := flat_run_fourth_of_return free hq hu heads deg second third back
  omega

/-! ### The patterns -/

/-- B1: `r = q + 1`, `4 ≤ q`, second layer exactly `r`, third at most `r - 1`, fourth at most
`r - 1`. -/
def dipB1 (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (q + 1 = r ∧ 4 ≤ q ∧ 3 ≤ ws.length ∧ ws.getD 1 0 = r ∧ ws.getD 2 0 + 1 ≤ r ∧
    (if 4 ≤ ws.length then ws.getD 3 0 else last) + 1 ≤ r)

theorem dipB1_sound (q r : ℕ) : ShapeClimbX.SoundX q r (dipB1 q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨qr, hq, len, w2, w3, w4⟩ := of_decide_eq_true h
  subst qr
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := row_dip_fourth free hq hu root deg (by omega) (by omega)
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    have e : ws.length + 1 = 4 := by omega
    rw [e] at bound
    omega

/-- The collar dip and B1: the proved patterns on the row `r = q + 1`. -/
def collarRowX (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  ShapeClimbX.collarDip q r ws last || dipB1 q r ws last

theorem collarRowX_sound (q r : ℕ) : ShapeClimbX.SoundX q r (collarRowX q r) :=
  TubeAtCutoff.soundX_or (ShapeClimbX.collarDip_sound q r) (dipB1_sound q r)

/-- B2 as a width pattern: `r = q + 1`, widths `(r, r, r)`, fourth at most `r - 2`.
**Not proved sound here**: only `flat_run_fourth_of_return` and `flat_run_residual` are proved.
Defined for the evaluation only. -/
def dipB2Unproved (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (q + 1 = r ∧ 6 ≤ q ∧ 3 ≤ ws.length ∧ ws.getD 1 0 = r ∧ ws.getD 2 0 = r ∧
    (if 4 ≤ ws.length then ws.getD 3 0 else last) + 2 ≤ r)

#print axioms row_dip_fourth
#print axioms dipB1_sound
#print axioms collarRowX_sound
#print axioms flat_run_fourth_of_return
#print axioms ball_two_floor
#print axioms flat_run_residual
end LeanCH.BR.CollarRowDips
