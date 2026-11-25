import checkpoints.shen_extension.CollarRowDips2

/-!
# The one-return law, hence B2 on the row `r = q + 1`

A root `u` of out-degree exactly `q + 1` in a `q`-free digraph of minimum out-degree `q + 1`,
layers `X, Y, Z` of `q + 1` labels each, `t ∈ Y` heading all of `Z`. Proved for `6 ≤ q`:

* `once_return`: `CollarRowDips.OnceReturn` (at most one label of `Z` has a head in `X ∪ Y`);
* `flat_run_fourth` (B2): widths `(q + 1, q + 1, q + 1)` force a fourth layer of at least `q`;
* `dipB2_sound`, and `collarRowX2 = collarRowX || dipB2` with `collarRowX2_sound`.

The steps, all generic in `q`:

* `three_miss`, `two_miss`: a row `x ∈ X` with a parent `y ∈ Y` has at most two heads in `X`
  (if `D[X]` has a sink, the sinks head all of `Y`, so `x` is deep to radius `q - 2`; otherwise
  `D[X]` is a loop), so it misses at most two labels of `Y`. If it misses `y` and a second label
  and so do its heads in `X`, then (sink case) its two heads in `X` must head each other inside a
  two-ball of at most four labels.
* `no_zx` (no return into `X`): if `z → x`, then `x` misses `t`, has at least `q - 2` heads in
  `Y - t`, and some sink `σ` of `D[Y - t]` lies within three steps of `x` inside `{x} ∪ (Y - t)`.
  `σ` cannot point to `t`, `z` or into `X` (each closes a walk of length at most `6 ≤ q`, or makes
  a row of `X` miss three labels of `Y`), so it has at most `q` heads.
* `far_x`: if `z → p ∈ Y`, no label within `q - 2` of `p` inside `Y` points into `X`, for the
  same reason.
* `two_returns`: two return targets `p₁, p₂` of distinct `z₁, z₂`. Inside `Y` the `(q-2)`-ball of
  each avoids `t` and its return label, so its rows have a head in `Y` and the balls grow by one
  label per step up to radius `q - 1`; hence the ball of radius `k` has at most `k + 2` labels.
  A row of the first ball with at most one head in `Y` heads `z₂`, so it lies outside the second
  ball, which has at least `q - 1` of the `q` labels of `Y - t`: at most one such row. `local3`
  shows that a three-ball of at most `5` labels cannot carry this.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarRowDips
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open FlatAtCutoff (grow)
open TubeAtCutoff (IsSink Deep closed_sink too_few full_of_sub closed_or_grow card_two_out
  row_ball classify x_ball layer_in layer_out)

variable {D : CH.Digraph}

/-! ### Rows of `X` with a parent in `Y` -/

section pair3
variable {V X Y : Finset ℕ} {q : ℕ}

/-- An `X`-label with a parent in `Y` has at most two heads in `X`. -/
theorem yparent_X (free : QFree D V q) (hq : 2 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    {x y : ℕ} (hx : x ∈ X) (hy : y ∈ Y) (yx : D y x = true) : (outN D X x).card ≤ 2 := by
  have fX : QFree D X q := free.mono_set hX
  by_cases hasSink : ∃ s ∈ X, IsSink D X s
  · obtain ⟨s0, hs0, sk0⟩ := hasSink
    have full := x_sink_full deg hX cY rowX
    have dp : Deep D X (q - 2) x := by
      intro s hs sink
      obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
      exact free x (j + 2) (by omega) (by omega)
        (((wj.mono hX).snoc (hY hy) (full s (ball_subset hs) sink y hy)).snoc (hX hx) yx)
    have := deep_heads1 fX cX.le hs0 sk0 (by omega) hx dp
    omega
  · have := loop_of_noSink free (by omega) hX cX (fun s hs sk => hasSink ⟨s, hs, sk⟩) x hx
    omega

/-- An `X`-label with a parent in `Y` misses at most two labels of `Y`. -/
theorem three_miss (free : QFree D V q) (hq : 2 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    {x y a b c : ℕ} (hx : x ∈ X) (hy : y ∈ Y) (yx : D y x = true)
    (ha : a ∈ Y) (hb : b ∈ Y) (hc : c ∈ Y) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (na : ¬ D x a = true) (nb : ¬ D x b = true) (nc : ¬ D x c = true) : False := by
  have h2 := yparent_X free hq deg hX hY cX cY rowX hx hy yx
  have split := x_split deg hX rowX x hx
  have sub : outN D Y x ⊆ Y.erase c := fun w hw =>
    mem_erase.mpr ⟨fun e => nc (e ▸ (mem_outN.mp hw).2), (mem_outN.mp hw).1⟩
  have := card_two_out sub (mem_erase.mpr ⟨ac, ha⟩) (mem_erase.mpr ⟨bc, hb⟩)
    (fun h => na (mem_outN.mp h).2) (fun h => nb (mem_outN.mp h).2) ab
  rw [card_erase_of_mem hc] at this
  omega

/-- An `X`-label `x` with a parent `y ∈ Y`, missing `y` and a second label `t'`, whose heads in
`X` also miss `y` and `t'`: impossible. In the loop case `x` misses at most one label of `Y`; in
the sink case `x` has exactly two heads in `X`, each needing two heads in `X` inside a two-ball
of at most four labels, so they form a digon. -/
theorem two_miss (free : QFree D V q) (hq : 4 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    {x y t' : ℕ} (hx : x ∈ X) (hy : y ∈ Y) (yx : D y x = true) (ht' : t' ∈ Y) (yt : y ≠ t')
    (nt : ¬ D x t' = true)
    (hd : ∀ a ∈ X, D x a = true → ¬ D a y = true ∧ ¬ D a t' = true) : False := by
  classical
  have fX : QFree D X q := free.mono_set hX
  have split := x_split deg hX rowX
  have ny : ¬ D x y = true := fun h => digonfree free (by omega) (hX hx) (hY hy) h yx
  have missY : ∀ v ∈ X, ¬ D v y = true → ¬ D v t' = true → (outN D Y v).card + 1 ≤ q := by
    intro v hv n1 n2
    have := card_two_out (outN_subset (D := D) (W := Y) (y := v)) hy ht'
      (fun h => n1 (mem_outN.mp h).2) (fun h => n2 (mem_outN.mp h).2) yt
    omega
  have mx := missY x hx ny nt
  by_cases hasSink : ∃ s ∈ X, IsSink D X s
  · obtain ⟨s0, hs0, sk0⟩ := hasSink
    have full := x_sink_full deg hX cY rowX
    have dp : Deep D X (q - 2) x := by
      intro s hs sink
      obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
      exact free x (j + 2) (by omega) (by omega)
        (((wj.mono hX).snoc (hY hy) (full s (ball_subset hs) sink y hy)).snoc (hX hx) yx)
    have h2 := deep_heads1 fX cX.le hs0 sk0 (by omega) hx dp
    have sx := split x hx
    have two : (outN D X x).card = 2 := by omega
    obtain ⟨a, b, ab, hab⟩ := card_eq_two.mp two
    have aX : a ∈ outN D X x := by rw [hab]; exact mem_insert_self _ _
    have bX : b ∈ outN D X x := by rw [hab]; exact mem_insert_of_mem (mem_singleton_self _)
    -- the two-ball of `x` inside `X` has at most four labels
    have g := grow (D := D) (W := X) (p := x) (a := 2) (M := q - 3)
      (fun j _ hj => deep_open1 fX cX.le hs0 sk0 hx dp (by omega))
    have cap : (ball D X x (2 + (q - 3))).card ≤ X.card := card_le_card ball_subset
    have b2 : (ball D X x 2).card ≤ 4 := by omega
    have key : ∀ a ∈ outN D X x, ∀ b ∈ outN D X x, a ≠ b → D a b = true := by
      intro a ha b hb ab
      obtain ⟨aX', xa⟩ := mem_outN.mp ha
      obtain ⟨bX', xb⟩ := mem_outN.mp hb
      have a1 : a ∈ ball D X x 1 := (mem_ball_one hx).mpr (Or.inr ha)
      have b1 : b ∈ ball D X x 1 := (mem_ball_one hx).mpr (Or.inr hb)
      have xa' : x ≠ a := fun e => loopfree free (by omega) (hX hx) (e ▸ xa)
      have xb' : x ≠ b := fun e => loopfree free (by omega) (hX hx) (e ▸ xb)
      obtain ⟨n1, n2⟩ := hd a aX' xa
      have ma := missY a aX' n1 n2
      have sa := split a aX'
      set T := ((ball D X x 2).erase x).erase a with hT
      have sub : outN D X a ⊆ T := by
        intro w hw
        obtain ⟨wX, aw⟩ := mem_outN.mp hw
        refine mem_erase.mpr ⟨fun e => loopfree free (by omega) (hX aX') (e ▸ aw),
          mem_erase.mpr ⟨fun e => digonfree free (by omega) (hX hx) (hX aX') xa (e ▸ aw),
            ball_step a1 wX aw⟩⟩
      have cT : T.card ≤ 2 := by
        rw [hT, card_erase_of_mem (mem_erase.mpr ⟨xa'.symm, ball_mono_radius (by omega) a1⟩),
          card_erase_of_mem (self_mem_ball hx)]
        omega
      exact full_of_sub (V := X) sub cT (by omega) b
        (mem_erase.mpr ⟨fun e => ab e.symm, mem_erase.mpr ⟨xb'.symm, ball_mono_radius (by omega) b1⟩⟩)
    exact digonfree free (by omega) (hX (mem_outN.mp aX).1) (hX (mem_outN.mp bX).1)
      (key a aX b bX ab) (key b bX a aX (Ne.symm ab))
  · have := loop_of_noSink free (by omega) hX cX (fun s hs sk => hasSink ⟨s, hs, sk⟩) x hx
    have := split x hx
    omega

end pair3

/-! ### A thin ball in an acyclic second layer -/

/-- In a `q`-free set `Y`, `3 ≤ q`, a label `p` whose balls have at most `2, 3, 4, 5` labels at
radii `0..3` (written as the bounds at `1, 2, 3`), every label of the two-ball having a head in
`Y`, and at most one label of the two-ball having fewer than two heads in `Y`: impossible. -/
theorem local3 {Y : Finset ℕ} {q p : ℕ} (free : QFree D Y q) (hq : 3 ≤ q) (hp : p ∈ Y)
    (b1 : (ball D Y p 1).card ≤ 3) (b2 : (ball D Y p 2).card ≤ 4) (b3 : (ball D Y p 3).card ≤ 5)
    (one : ∀ v ∈ ball D Y p 2, 1 ≤ (outN D Y v).card)
    (exc : ∀ v ∈ ball D Y p 2, ∀ w ∈ ball D Y p 2,
      (outN D Y v).card ≤ 1 → (outN D Y w).card ≤ 1 → v = w) : False := by
  classical
  have lf : ∀ v ∈ Y, ¬ D v v = true := fun v hv => loopfree free (by omega) hv
  have dg : ∀ v ∈ Y, ∀ w ∈ Y, D v w = true → D w v = true → False :=
    fun v hv w hw => digonfree free (by omega) hv hw
  have tri : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, D a b = true → D b c = true → D c a = true → False :=
    fun a ha b hb c hc ab bc ca => free a 3 (by omega) (by omega)
      (.step hb ab (.step hc bc (.step ha ca (.refl a))))
  have m12 : ball D Y p 1 ⊆ ball D Y p 2 := ball_mono_radius (by omega)
  have m23 : ball D Y p 2 ⊆ ball D Y p 3 := ball_mono_radius (by omega)
  have p1 : p ∈ ball D Y p 1 := self_mem_ball hp
  have out1 : ∀ a ∈ outN D Y p, a ∈ ball D Y p 1 := fun a ha => (mem_ball_one hp).mpr (Or.inr ha)
  have pa : ∀ a ∈ outN D Y p, a ≠ p := fun a ha e => lf p hp (e ▸ (mem_outN.mp ha).2)
  -- heads of a head of `p` lie in the two-ball minus `p` and itself
  have sub2 : ∀ a ∈ outN D Y p,
      outN D Y a ⊆ ((ball D Y p 2).erase p).erase a ∧ (((ball D Y p 2).erase p).erase a).card ≤ 2 := by
    intro a ha
    obtain ⟨aY, pa'⟩ := mem_outN.mp ha
    refine ⟨fun w hw => ?_, ?_⟩
    · obtain ⟨wY, aw⟩ := mem_outN.mp hw
      exact mem_erase.mpr ⟨fun e => lf a aY (e ▸ aw),
        mem_erase.mpr ⟨fun e => dg p hp a aY pa' (e ▸ aw), ball_step (out1 a ha) wY aw⟩⟩
    · rw [card_erase_of_mem (mem_erase.mpr ⟨pa a ha, m12 (out1 a ha)⟩),
        card_erase_of_mem (m12 p1)]
      omega
  have hN : (outN D Y p).card ≤ 2 := by
    have sub : insert p (outN D Y p) ⊆ ball D Y p 1 := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact p1
      · exact out1 w hw
    have := card_le_card sub
    rw [card_insert_of_notMem (fun h => lf p hp (mem_outN.mp h).2)] at this
    omega
  have hN1 := one p (m12 p1)
  rcases (show (outN D Y p).card = 1 ∨ (outN D Y p).card = 2 by omega) with c1 | c2
  · -- one head `a`: `p` is the exception, `a` heads `b, c`, which then form a digon
    obtain ⟨a, ha⟩ := card_eq_one.mp c1
    have aN : a ∈ outN D Y p := by rw [ha]; exact mem_singleton_self _
    obtain ⟨aY, pa'⟩ := mem_outN.mp aN
    have big : ∀ v ∈ ball D Y p 2, v ≠ p → 2 ≤ (outN D Y v).card := by
      intro v hv vp
      by_contra h
      exact vp (exc v hv p (m12 p1) (by omega) (by omega))
    have ca := big a (m12 (out1 a aN)) (pa a aN)
    obtain ⟨sa, cs⟩ := sub2 a aN
    have eqa : outN D Y a = ((ball D Y p 2).erase p).erase a :=
      eq_of_subset_of_card_le sa (by omega)
    have key : ∀ b ∈ outN D Y a, ∀ c ∈ outN D Y a, b ≠ c → D b c = true := by
      intro b hb c hc bc
      obtain ⟨bY, ab⟩ := mem_outN.mp hb
      obtain ⟨cY, ac⟩ := mem_outN.mp hc
      have hb' := hb; rw [eqa] at hb'
      have hc' := hc; rw [eqa] at hc'
      obtain ⟨ba, hb''⟩ := mem_erase.mp hb'
      obtain ⟨bp, b2'⟩ := mem_erase.mp hb''
      obtain ⟨ca', hc''⟩ := mem_erase.mp hc'
      obtain ⟨cp, c2'⟩ := mem_erase.mp hc''
      have cb := big b b2' bp
      set T := (((ball D Y p 3).erase p).erase a).erase b with hT
      have sub : outN D Y b ⊆ T := by
        intro w hw
        obtain ⟨wY, bw⟩ := mem_outN.mp hw
        refine mem_erase.mpr ⟨fun e => lf b bY (e ▸ bw), mem_erase.mpr ⟨fun e => dg a aY b bY ab (e ▸ bw),
          mem_erase.mpr ⟨fun e => tri p hp a aY b bY pa' ab (e ▸ bw), ball_step b2' wY bw⟩⟩⟩
      have cT : T.card ≤ 2 := by
        rw [hT, card_erase_of_mem (mem_erase.mpr ⟨ba, mem_erase.mpr ⟨bp, m23 b2'⟩⟩),
          card_erase_of_mem (mem_erase.mpr ⟨pa a aN, m23 (m12 (out1 a aN))⟩),
          card_erase_of_mem (m23 (m12 p1))]
        omega
      exact full_of_sub (V := Y) sub cT cb c
        (mem_erase.mpr ⟨bc.symm, mem_erase.mpr ⟨ca', mem_erase.mpr ⟨cp, m23 c2'⟩⟩⟩)
    obtain ⟨b, c, bc, hbc⟩ := card_eq_two.mp (show (outN D Y a).card = 2 by
      have := card_le_card sa; omega)
    have bA : b ∈ outN D Y a := by rw [hbc]; exact mem_insert_self _ _
    have cA : c ∈ outN D Y a := by rw [hbc]; exact mem_insert_of_mem (mem_singleton_self _)
    exact dg b (mem_outN.mp bA).1 c (mem_outN.mp cA).1 (key b bA c cA bc) (key c cA b bA (Ne.symm bc))
  · -- two heads `a, b`
    obtain ⟨a, b, ab, hab⟩ := card_eq_two.mp c2
    have aN : a ∈ outN D Y p := by rw [hab]; exact mem_insert_self _ _
    have bN : b ∈ outN D Y p := by rw [hab]; exact mem_insert_of_mem (mem_singleton_self _)
    -- if `a` has at most one head, then `b → a, c`, `a → c`, and `c` has no room
    have side : ∀ a ∈ outN D Y p, ∀ b ∈ outN D Y p, a ≠ b → (outN D Y a).card ≤ 1 → False := by
      intro a aN b bN ab ca
      obtain ⟨aY, pa'⟩ := mem_outN.mp aN
      obtain ⟨bY, pb'⟩ := mem_outN.mp bN
      have big : ∀ v ∈ ball D Y p 2, v ≠ a → 2 ≤ (outN D Y v).card := by
        intro v hv va
        by_contra h
        exact va (exc v hv a (m12 (out1 a aN)) (by omega) ca)
      have cb := big b (m12 (out1 b bN)) (Ne.symm ab)
      obtain ⟨sb, cs⟩ := sub2 b bN
      have fb := full_of_sub (V := Y) sb cs cb
      have aT : a ∈ ((ball D Y p 2).erase p).erase b :=
        mem_erase.mpr ⟨ab, mem_erase.mpr ⟨pa a aN, m12 (out1 a aN)⟩⟩
      have ba := fb a aT
      have two : 1 < (((ball D Y p 2).erase p).erase b).card :=
        lt_of_lt_of_le (by omega) (le_trans cb (card_le_card sb))
      obtain ⟨c, cT, cane⟩ := exists_mem_ne two a
      have bc := fb c cT
      obtain ⟨cb', cT'⟩ := mem_erase.mp cT
      obtain ⟨cp, c2⟩ := mem_erase.mp cT'
      have cY := ball_subset c2
      -- the head of `a` is `c`
      obtain ⟨w, hw⟩ : (outN D Y a).Nonempty := card_pos.mp (one a (m12 (out1 a aN)))
      obtain ⟨wY, aw⟩ := mem_outN.mp hw
      have wb : w ≠ b := fun e => dg a aY b bY (e ▸ aw) ba
      obtain ⟨sa, csa⟩ := sub2 a aN
      have wT := sa hw
      set R := (((ball D Y p 2).erase p).erase a).erase b with hR
      have cR : R.card ≤ 1 := by
        rw [hR, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm ab, mem_erase.mpr ⟨pa b bN, m12 (out1 b bN)⟩⟩)]
        omega
      have wR : w ∈ R := mem_erase.mpr ⟨wb, wT⟩
      have cR' : c ∈ R := mem_erase.mpr ⟨cb', mem_erase.mpr ⟨cane, cT'⟩⟩
      have wc : w = c := card_le_one.mp cR w wR c cR'
      rw [wc] at aw
      -- `c` has at most one head left
      have cc := big c c2 cane
      have sub : outN D Y c ⊆ ((((ball D Y p 3).erase p).erase a).erase b).erase c := by
        intro v hv
        obtain ⟨vY, cv⟩ := mem_outN.mp hv
        refine mem_erase.mpr ⟨fun e => lf c cY (e ▸ cv),
          mem_erase.mpr ⟨fun e => dg b bY c cY bc (e ▸ cv),
          mem_erase.mpr ⟨fun e => dg a aY c cY aw (e ▸ cv),
          mem_erase.mpr ⟨fun e => tri p hp b bY c cY pb' bc (e ▸ cv), ball_step c2 vY cv⟩⟩⟩⟩
      have := card_le_card sub
      rw [card_erase_of_mem (mem_erase.mpr ⟨cb', mem_erase.mpr ⟨cane, mem_erase.mpr ⟨cp, m23 c2⟩⟩⟩),
        card_erase_of_mem (mem_erase.mpr ⟨Ne.symm ab, mem_erase.mpr ⟨pa b bN, m23 (m12 (out1 b bN))⟩⟩),
        card_erase_of_mem (mem_erase.mpr ⟨pa a aN, m23 (m12 (out1 a aN))⟩),
        card_erase_of_mem (m23 (m12 p1))] at this
      omega
    by_cases ca : (outN D Y a).card ≤ 1
    · exact side a aN b bN ab ca
    by_cases cb : (outN D Y b).card ≤ 1
    · exact side b bN a aN (Ne.symm ab) cb
    obtain ⟨sa, csa⟩ := sub2 a aN
    obtain ⟨sb, csb⟩ := sub2 b bN
    have hab' := full_of_sub (V := Y) sa csa (by omega) b
      (mem_erase.mpr ⟨Ne.symm ab, mem_erase.mpr ⟨pa b bN, m12 (out1 b bN)⟩⟩)
    have hba' := full_of_sub (V := Y) sb csb (by omega) a
      (mem_erase.mpr ⟨ab, mem_erase.mpr ⟨pa a aN, m12 (out1 a aN)⟩⟩)
    exact dg a (mem_outN.mp aN).1 b (mem_outN.mp bN).1 hab' hba'

/-! ### Returns from the third layer

Setting: `X, Y, Z ⊆ V` with `q + 1` labels each, rows of `X` inside `X ∪ Y`, rows of `Y` inside
`X ∪ Y ∪ Z`, `X ∩ Y = ∅`, and `t ∈ Y` heading all of `Z`. -/

section returns
variable {V X Y Z : Finset ℕ} {q t : ℕ}

/-- **No return into `X`** (`6 ≤ q`). -/
theorem no_zx (free : QFree D V q) (hq : 6 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (hZ : Z ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (cZ : Z.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    (rowY : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z)
    (XY : ∀ x ∈ X, x ∉ Y) (tY : t ∈ Y) (tZ : ∀ z ∈ Z, D t z = true)
    {z x : ℕ} (hz : z ∈ Z) (hx : x ∈ X) (zx : D z x = true) : False := by
  classical
  have fX : QFree D X q := free.mono_set hX
  have xV := hX hx
  have zV := hZ hz
  have tV := hY tY
  have tz := tZ z hz
  have xt : ¬ D x t = true := fun h => free x 3 (by omega) (by omega)
    (.step tV h (.step zV tz (.step xV zx (.refl x))))
  have xX : (outN D X x).card ≤ 3 := by
    by_cases hasSink : ∃ s ∈ X, IsSink D X s
    · obtain ⟨s0, hs0, sk0⟩ := hasSink
      have full := x_sink_full deg hX cY rowX
      have dp : Deep D X (q - 3) x := by
        intro s hs sink
        obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
        exact free x (j + 3) (by omega) (by omega)
          ((((wj.mono hX).snoc tV (full s (ball_subset hs) sink t tY)).snoc zV tz).snoc xV zx)
      have := deep_heads1 fX cX.le hs0 sk0 (by omega) hx dp
      omega
    · have := loop_of_noSink free (by omega) hX cX (fun s hs sk => hasSink ⟨s, hs, sk⟩) x hx
      omega
  have split := x_split deg hX rowX x hx
  set Y' := Y.erase t with hY'
  set V' := insert x Y' with hV'
  have hY'V : Y' ⊆ V := (erase_subset t Y).trans hY
  have hV'V : V' ⊆ V := insert_subset xV hY'V
  have cY' : Y'.card = q := by rw [hY', card_erase_of_mem tY]; omega
  have xY' : x ∉ Y' := fun h => XY x hx (mem_of_mem_erase h)
  have cV' : V'.card = q + 1 := by rw [hV', card_insert_of_notMem xY']; omega
  have fV' : QFree D V' q := free.mono_set hV'V
  have fY' : QFree D Y' q := free.mono_set hY'V
  have xV' : x ∈ V' := mem_insert_self _ _
  -- a sink of `D[Y - t]` within three steps of `x` inside `V'`
  obtain ⟨σ, σY', σsk, σb⟩ : ∃ σ ∈ Y', IsSink D Y' σ ∧ σ ∈ ball D V' x 3 := by
    have anySink : ball D V' x 3 = V' → ∃ σ ∈ Y', IsSink D Y' σ ∧ σ ∈ ball D V' x 3 := by
      intro e
      obtain ⟨σ, hσ, sk⟩ := exists_sink fY' (card_pos.mp (by omega)) (by omega)
      exact ⟨σ, hσ, sk, by rw [e]; exact mem_insert_of_mem hσ⟩
    have b1 : q - 1 ≤ (ball D V' x 1).card := by
      have sub : insert x (outN D Y x) ⊆ ball D V' x 1 := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact self_mem_ball xV'
        · obtain ⟨wY, xw⟩ := mem_outN.mp hw
          have wt : w ≠ t := fun e => xt (e ▸ xw)
          exact (mem_ball_one xV').mpr
            (Or.inr (mem_outN.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨wt, wY⟩), xw⟩))
      have := card_le_card sub
      rw [card_insert_of_notMem (fun h => XY x hx (mem_outN.mp h).1)] at this
      omega
    have full3 : ∀ j, j ≤ 3 → V' ⊆ ball D V' x j → ball D V' x 3 = V' := fun j hj h =>
      subset_antisymm ball_subset (h.trans (ball_mono_radius hj))
    rcases closed_or_grow (D := D) (S := V') (v := x) (a := 1) (M := 2) with ⟨j, hj1, hj2, cl⟩ | g
    · by_cases sm : (ball D V' x j).card ≤ q
      · obtain ⟨s, sb, sk⟩ := closed_sink fV' xV' sm cl
        have sx : s ≠ x := by
          intro e
          rw [e] at sk
          obtain ⟨w, hw⟩ : (outN D Y x).Nonempty := card_pos.mp (by omega)
          obtain ⟨wY, xw⟩ := mem_outN.mp hw
          exact sk w (mem_insert_of_mem (mem_erase.mpr ⟨fun e => xt (e ▸ xw), wY⟩)) xw
        have sY' : s ∈ Y' := by
          rcases mem_insert.mp (ball_subset sb) with h | h
          · exact (sx h).elim
          · exact h
        exact ⟨s, sY', fun w hw sw => sk w (mem_insert_of_mem hw) sw, ball_mono_radius (by omega) sb⟩
      · have e : ball D V' x j = V' := eq_of_subset_of_card_le ball_subset (by omega)
        exact anySink (full3 j (by omega) e.symm.subset)
    · have g' : (ball D V' x 1).card + 2 ≤ (ball D V' x 3).card := g
      have e : ball D V' x 3 = V' := eq_of_subset_of_card_le ball_subset (by omega)
      exact anySink e
  have σY : σ ∈ Y := mem_of_mem_erase σY'
  have σt : σ ≠ t := ne_of_mem_erase σY'
  have σV := hY σY
  obtain ⟨-, d, hd, wd⟩ := mem_ball.mp σb
  have wdV : Walk D V x σ d := wd.mono hV'V
  have σnt : ¬ D σ t = true := fun h => free x (d + 3) (by omega) (by omega)
    (((wdV.snoc tV h).snoc zV tz).snoc xV zx)
  have σnz : ¬ D σ z = true := fun h => free x (d + 2) (by omega) (by omega)
    ((wdV.snoc zV h).snoc xV zx)
  -- `σ` has no head in `X`
  have σX : ∀ x' ∈ X, ¬ D σ x' = true := by
    intro x' hx' σx'
    have x'V := hX hx'
    have nσ : ¬ D x' σ = true := fun h => digonfree free (by omega) σV x'V σx' h
    -- the case `x → σ`
    have case1 : D x σ = true → False := by
      intro xσ
      refine two_miss free (by omega) deg hX hY cX cY rowX hx' σY σx' tY σt
        (fun h => free x 5 (by omega) (by omega) (.step σV xσ (.step x'V σx' (.step tV h
          (.step zV tz (.step xV zx (.refl x))))))) ?_
      intro a aX x'a
      have aV := hX aX
      exact ⟨fun h => free σ 3 (by omega) (by omega) (.step x'V σx' (.step aV x'a (.step σV h (.refl σ)))),
        fun h => free x 6 (by omega) (by omega) (.step σV xσ (.step x'V σx' (.step aV x'a
          (.step tV h (.step zV tz (.step xV zx (.refl x)))))))⟩
    rcases Nat.eq_zero_or_pos d with rfl | dpos
    · have e := walk_zero wd
      rw [← e] at σY'
      exact (xY' σY').elim
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨a, wa, -, aσ⟩ := wd.unsnoc
    by_cases ax : a = x
    · exact case1 (ax ▸ aσ)
    have aY' : a ∈ Y' := by
      rcases wa.end_mem_or with h | h
      · exact (ax h).elim
      · rcases mem_insert.mp h with h | h
        · exact (ax h).elim
        · exact h
    have aY := mem_of_mem_erase aY'
    have aV := hY aY
    have aσ' : a ≠ σ := fun e => loopfree free (by omega) aV (e ▸ aσ)
    have na : ¬ D x' a = true := fun h => free a 3 (by omega) (by omega)
      (.step σV aσ (.step x'V σx' (.step aV h (.refl a))))
    rcases Nat.eq_zero_or_pos d' with rfl | dpos'
    · exact ax (walk_zero wa).symm
    obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
    obtain ⟨b, wb, -, ba⟩ := wa.unsnoc
    by_cases bx : b = x
    · -- `x → a → σ → x'`
      rw [bx] at ba
      exact three_miss free (by omega) deg hX hY cX cY rowX hx' σY σx' σY aY tY (Ne.symm aσ') σt (ne_of_mem_erase aY') nσ na
        (fun h => free x 6 (by omega) (by omega) (.step aV ba (.step σV aσ (.step x'V σx'
          (.step tV h (.step zV tz (.step xV zx (.refl x))))))))
    · have bY' : b ∈ Y' := by
        rcases wb.end_mem_or with h | h
        · exact (bx h).elim
        · rcases mem_insert.mp h with h | h
          · exact (bx h).elim
          · exact h
      have bY := mem_of_mem_erase bY'
      have bV := hY bY
      have ba' : b ≠ a := fun e => loopfree free (by omega) bV (e ▸ ba)
      have bσ : b ≠ σ := fun e => digonfree free (by omega) σV aV (e ▸ ba) aσ
      exact three_miss free (by omega) deg hX hY cX cY rowX hx' σY σx' σY aY bY (Ne.symm aσ') (Ne.symm bσ) (Ne.symm ba') nσ na
        (fun h => free b 4 (by omega) (by omega)
          (.step aV ba (.step σV aσ (.step x'V σx' (.step bV h (.refl b))))))
  -- so all heads of `σ` lie in `Z - z`
  refine too_few (V := V) (T := Z.erase z) ?_ (by rw [card_erase_of_mem hz]; omega) (deg σ σV)
  intro w hw
  obtain ⟨wV, σw⟩ := mem_outN.mp hw
  rcases rowY σ σY w wV σw with h | h | h
  · exact (σX w h σw).elim
  · by_cases wt : w = t
    · exact (σnt (wt ▸ σw)).elim
    · exact (σsk w (mem_erase.mpr ⟨wt, h⟩) σw).elim
  · exact mem_erase.mpr ⟨fun e => σnz (e ▸ σw), h⟩

/-- **Returns land far from `X`** (`6 ≤ q`): if `z → p` with `p ∈ Y`, no label within `q - 2`
of `p` inside `Y` has a head in `X`. -/
theorem far_x (free : QFree D V q) (hq : 6 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (hZ : Z ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    (tY : t ∈ Y) (tZ : ∀ z ∈ Z, D t z = true)
    {z p : ℕ} (hz : z ∈ Z) (hp : p ∈ Y) (zp : D z p = true)
    {y x' : ℕ} (hy : y ∈ ball D Y p (q - 2)) (hx' : x' ∈ X) (yx : D y x' = true) : False := by
  have zV := hZ hz
  have pV := hY hp
  have tV := hY tY
  have x'V := hX hx'
  have tz := tZ z hz
  have tfar : ∀ v ∈ ball D Y p (q - 2), v ≠ t := by
    intro v hv e
    obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hv
    rw [e] at wj
    exact free p (j + 2) (by omega) (by omega) (((wj.mono hY).snoc zV tz).snoc pV zp)
  have pt := tfar p (self_mem_ball hp)
  obtain ⟨yY, j, hj, wj⟩ := mem_ball.mp hy
  have yV := hY yY
  have yt := tfar y hy
  have ny : ¬ D x' y = true := fun h => digonfree free (by omega) yV x'V yx h
  by_cases ep : y = p
  · rw [ep] at yx
    refine two_miss free (by omega) deg hX hY cX cY rowX hx' hp yx tY pt
      (fun h => free p 4 (by omega) (by omega)
        (.step x'V yx (.step tV h (.step zV tz (.step pV zp (.refl p)))))) ?_
    intro a aX x'a
    have aV := hX aX
    exact ⟨fun h => free p 3 (by omega) (by omega) (.step x'V yx (.step aV x'a (.step pV h (.refl p)))),
      fun h => free p 5 (by omega) (by omega) (.step x'V yx (.step aV x'a (.step tV h
        (.step zV tz (.step pV zp (.refl p))))))⟩
  rcases Nat.eq_zero_or_pos j with rfl | jpos
  · exact ep (walk_zero wj).symm
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨a, wa, -, ay⟩ := wj.unsnoc
  have aY : a ∈ Y := by
    rcases wa.end_mem_or with h | h
    · rw [h]; exact hp
    · exact h
  have aV := hY aY
  have na : ¬ D x' a = true := fun h => free a 3 (by omega) (by omega)
    (.step yV ay (.step x'V yx (.step aV h (.refl a))))
  have ya : y ≠ a := fun e => loopfree free (by omega) aV (e ▸ ay)
  by_cases ea : a = p
  · rw [ea] at ay na ya
    exact three_miss free (by omega) deg hX hY cX cY rowX hx' yY yx yY hp tY ya yt pt ny na
      (fun h => free p 5 (by omega) (by omega) (.step yV ay (.step x'V yx (.step tV h
        (.step zV tz (.step pV zp (.refl p)))))))
  rcases Nat.eq_zero_or_pos j' with rfl | jpos'
  · exact ea (walk_zero wa).symm
  obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
  obtain ⟨b, wb, -, ba⟩ := wa.unsnoc
  have bY : b ∈ Y := by
    rcases wb.end_mem_or with h | h
    · rw [h]; exact hp
    · exact h
  have bV := hY bY
  have ab : a ≠ b := fun e => loopfree free (by omega) bV (e ▸ ba)
  have yb : y ≠ b := fun e => digonfree free (by omega) yV aV (e ▸ ba) ay
  exact three_miss free (by omega) deg hX hY cX cY rowX hx' yY yx yY aY bY ya yb ab ny na
    (fun h => free b 4 (by omega) (by omega) (.step aV ba (.step yV ay (.step x'V yx (.step bV h (.refl b))))))

/-- **Two returns are impossible** (`6 ≤ q`): two distinct labels of `Z` cannot both point into
`Y`. Each return target `p` has a `(q-2)`-ball inside `Y` of at least `q - 1` labels, none
pointing to its return label and none pointing into `X`; balls grow by one per step up to radius
`q - 1`. A label of the first ball with at most one head in `Y` heads all of `Z` except the first
return label, so it lies outside the second ball: at most one such label. `local3` then fails. -/
theorem two_returns (free : QFree D V q) (hq : 6 ≤ q) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (hX : X ⊆ V) (hY : Y ⊆ V) (hZ : Z ⊆ V) (cX : X.card = q + 1) (cY : Y.card = q + 1)
    (cZ : Z.card = q + 1)
    (rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y)
    (rowY : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z)
    (tY : t ∈ Y) (tZ : ∀ z ∈ Z, D t z = true)
    {z₁ z₂ p₁ p₂ : ℕ} (h₁ : z₁ ∈ Z) (h₂ : z₂ ∈ Z) (ne : z₁ ≠ z₂)
    (hp₁ : p₁ ∈ Y) (hp₂ : p₂ ∈ Y) (a₁ : D z₁ p₁ = true) (a₂ : D z₂ p₂ = true) : False := by
  classical
  have fY : QFree D Y q := free.mono_set hY
  have facts : ∀ z ∈ Z, ∀ p ∈ Y, D z p = true →
      (∀ v ∈ ball D Y p (q - 2), v ≠ t ∧ ¬ D v z = true ∧ 1 ≤ (outN D Y v).card ∧
        ∀ w ∈ Z, w ≠ z → (outN D Y v).card ≤ 1 → D v w = true) ∧
      (∀ k, k ≤ q - 1 → k + 1 ≤ (ball D Y p k).card ∧ (ball D Y p k).card + (q - 1 - k) ≤ q + 1) := by
    intro z hz p hp zp
    have zV := hZ hz
    have pV := hY hp
    have tz := tZ z hz
    have row : ∀ v ∈ ball D Y p (q - 2), v ≠ t ∧ ¬ D v z = true ∧ 1 ≤ (outN D Y v).card ∧
        ∀ w ∈ Z, w ≠ z → (outN D Y v).card ≤ 1 → D v w = true := by
      intro v hv
      obtain ⟨vY, j, hj, wj⟩ := mem_ball.mp hv
      have vt : v ≠ t := by
        intro e
        rw [e] at wj
        exact free p (j + 2) (by omega) (by omega) (((wj.mono hY).snoc zV tz).snoc pV zp)
      have vz : ¬ D v z = true := fun h => free p (j + 2) (by omega) (by omega)
        (((wj.mono hY).snoc zV h).snoc pV zp)
      have cov : ∀ u ∈ outN D V v, u ∈ outN D Y v ∨ (u ∈ Z ∧ u ≠ z) := by
        intro u hu
        obtain ⟨uV, vu⟩ := mem_outN.mp hu
        rcases rowY v vY u uV vu with h | h | h
        · exact (far_x free hq deg hX hY hZ cX cY rowX tY tZ hz hp zp hv h vu).elim
        · exact Or.inl (mem_outN.mpr ⟨h, vu⟩)
        · exact Or.inr ⟨h, fun e => vz (e ▸ vu)⟩
      refine ⟨vt, vz, ?_, ?_⟩
      · have sub : outN D V v ⊆ outN D Y v ∪ Z.erase z := by
          intro u hu
          rcases cov u hu with h | ⟨h1, h2⟩
          · exact mem_union_left _ h
          · exact mem_union_right _ (mem_erase.mpr ⟨h2, h1⟩)
        have := (deg v (hY vY)).trans ((card_le_card sub).trans (card_union_le _ _))
        rw [card_erase_of_mem hz] at this
        omega
      · intro w hw wz small
        by_contra nw
        have sub : outN D V v ⊆ outN D Y v ∪ (Z.erase z).erase w := by
          intro u hu
          rcases cov u hu with h | ⟨h1, h2⟩
          · exact mem_union_left _ h
          · refine mem_union_right _ (mem_erase.mpr ⟨fun e => nw ?_, mem_erase.mpr ⟨h2, h1⟩⟩)
            rw [← e]; exact (mem_outN.mp hu).2
        have := (deg v (hY vY)).trans ((card_le_card sub).trans (card_union_le _ _))
        rw [card_erase_of_mem (mem_erase.mpr ⟨wz, hw⟩), card_erase_of_mem hz] at this
        omega
    refine ⟨row, ?_⟩
    have opn : ∀ j, j < q - 1 → ∃ a ∈ ball D Y p j, ∃ w ∈ Y, D a w = true ∧ w ∉ ball D Y p j := by
      intro j hj
      by_contra hc
      have cl : ∀ a ∈ ball D Y p j, ∀ w ∈ Y, D a w = true → w ∈ ball D Y p j :=
        fun a ha w hw aw => by_contra fun hn => hc ⟨a, ha, w, hw, aw, hn⟩
      have inB : ball D Y p j ⊆ ball D Y p (q - 2) := ball_mono_radius (by omega)
      have small : (ball D Y p j).card ≤ q := by
        have sub : ball D Y p j ⊆ Y.erase t := fun w hw =>
          mem_erase.mpr ⟨(row w (inB hw)).1, ball_subset hw⟩
        have := card_le_card sub
        rw [card_erase_of_mem tY] at this
        omega
      obtain ⟨s, sb, sk⟩ := closed_sink fY hp small cl
      obtain ⟨w, hw⟩ : (outN D Y s).Nonempty := card_pos.mp (row s (inB sb)).2.2.1
      exact sk w (mem_outN.mp hw).1 (mem_outN.mp hw).2
    intro k hk
    constructor
    · have g := grow (D := D) (W := Y) (p := p) (a := 0) (M := k) (fun j _ hj => opn j (by omega))
      have one : 1 ≤ (ball D Y p 0).card := card_pos.mpr ⟨p, self_mem_ball hp⟩
      rw [Nat.zero_add] at g
      omega
    · have g := grow (D := D) (W := Y) (p := p) (a := k) (M := q - 1 - k) (fun j _ hj => opn j (by omega))
      have e : k + (q - 1 - k) = q - 1 := by omega
      rw [e] at g
      have := card_le_card (ball_subset (D := D) (W := Y) (u := p) (k := q - 1))
      omega
  obtain ⟨r₁, g₁⟩ := facts z₁ h₁ p₁ hp₁ a₁
  obtain ⟨r₂, g₂⟩ := facts z₂ h₂ p₂ hp₂ a₂
  have B2 := (g₂ (q - 2) (by omega)).1
  have exc : ∀ v ∈ ball D Y p₁ (q - 2), ∀ w ∈ ball D Y p₁ (q - 2),
      (outN D Y v).card ≤ 1 → (outN D Y w).card ≤ 1 → v = w := by
    intro v hv w hw cv cw
    by_contra vw
    have out : ∀ u ∈ ball D Y p₁ (q - 2), (outN D Y u).card ≤ 1 → u ∉ ball D Y p₂ (q - 2) := by
      intro u hu cu h
      exact (r₂ u h).2.1 ((r₁ u hu).2.2.2 z₂ h₂ (Ne.symm ne) cu)
    have sub : ball D Y p₂ (q - 2) ⊆ Y.erase t := fun u hu =>
      mem_erase.mpr ⟨(r₂ u hu).1, ball_subset hu⟩
    have := card_two_out sub (mem_erase.mpr ⟨(r₁ v hv).1, ball_subset hv⟩)
      (mem_erase.mpr ⟨(r₁ w hw).1, ball_subset hw⟩) (out v hv cv) (out w hw cw) vw
    rw [card_erase_of_mem tY] at this
    omega
  have m2 : ball D Y p₁ 2 ⊆ ball D Y p₁ (q - 2) := ball_mono_radius (by omega)
  have c1 := (g₁ 1 (by omega)).2
  have c2 := (g₁ 2 (by omega)).2
  have c3 := (g₁ 3 (by omega)).2
  exact local3 fY (by omega) hp₁ (by omega) (by omega) (by omega)
    (fun v hv => (r₁ v (m2 hv)).2.2.1) (fun v hv w hw => exc v (m2 hv) w (m2 hw))

end returns

/-! ### The one-return law and B2 -/

/-- **The one-return law** (`6 ≤ q`): a root with exactly `q + 1` heads and exactly `q + 1`
labels in its second and third layers, in a `q`-free digraph of minimum out-degree at least
`q + 1`, satisfies `OnceReturn`. -/
theorem once_return {V : Finset ℕ} {q u : ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (hu : u ∈ V) (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (second : (layer D V 2 u).card = q + 1) (third : (layer D V 3 u).card = q + 1) :
    OnceReturn D V u := by
  classical
  intro t tY tZ z₁ h₁ z₂ h₂ w₁ v₁ w₂ v₂ a₁ a₂ b₁ b₂
  by_contra ne
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
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
  have XY : ∀ x ∈ X, x ∉ Y := fun x hx hy => layer_out hy le_rfl (x_ball hu hx)
  have tZ' : ∀ z ∈ Z, D t z = true := by
    intro z hz
    have : z ∈ outN D V t := by rw [tZ]; exact hz
    exact (mem_outN.mp this).2
  have inY : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → (w ∈ X ∨ w ∈ Y) → w ∈ Y := by
    intro z hz w wV zw hw
    rcases hw with h | h
    · exact (no_zx free hq deg hX hY hZ heads second third rowX rowY XY tY tZ' hz h zw).elim
    · exact h
  exact two_returns free hq deg hX hY hZ heads second third rowX rowY tY tZ' h₁ h₂ ne
    (inY z₁ h₁ w₁ v₁ a₁ b₁) (inY z₂ h₂ w₂ v₂ a₂ b₂) a₁ a₂

/-- **B2** (`6 ≤ q`): widths `(q + 1, q + 1, q + 1)` force a fourth layer of at least `q`. -/
theorem flat_run_fourth {V : Finset ℕ} {q u : ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (hu : u ∈ V) (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card)
    (second : (layer D V 2 u).card = q + 1) (third : (layer D V 3 u).card = q + 1) :
    q ≤ (layer D V 4 u).card :=
  flat_run_fourth_of_once free hq hu heads deg second third
    (once_return free hq hu heads deg second third)

/-- `dipB2` is sound. (Proved directly from `flat_run_fourth`: `dipB2_sound_of_once` asks for the
law at every root, while `once_return` needs the widths that the pattern itself supplies.) -/
theorem dipB2_sound (q r : ℕ) : ShapeClimbX.SoundX q r (dipB2 q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨qr, hq, len, w2, w3, w4⟩ := of_decide_eq_true h
  subst qr
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := flat_run_fourth free hq hu root deg (by omega) (by omega)
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    have e : ws.length + 1 = 4 := by omega
    rw [e] at bound
    omega

/-- The proved patterns on the row `r = q + 1`: collar dip, B1 and B2. -/
def collarRowX2 (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  collarRowX q r ws last || dipB2 q r ws last

theorem collarRowX2_sound (q r : ℕ) : ShapeClimbX.SoundX q r (collarRowX2 q r) :=
  TubeAtCutoff.soundX_or (collarRowX_sound q r) (dipB2_sound q r)

#print axioms three_miss
#print axioms two_miss
#print axioms local3
#print axioms no_zx
#print axioms far_x
#print axioms two_returns
#print axioms once_return
#print axioms flat_run_fourth
#print axioms dipB2_sound
#print axioms collarRowX2_sound
end LeanCH.BR.CollarRowDips
