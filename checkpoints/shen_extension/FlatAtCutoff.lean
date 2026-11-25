import checkpoints.shen_extension.ShapeClimbX

/-!
# The flat dip at the cutoff

`flat_third`: in a `q`-free digraph of minimum out-degree at least `r`, with `3 ≤ r ≤ q`, a root
with exactly `r` heads and exactly `r` labels in its second layer has at least `r` labels in its
third layer. The case that matters is `r = q` (`r < q` is `DipCost.flat_keep`).

Write `X` for the heads, `Y` for the second layer, `Z` for the third, and suppose `|Z| ≤ r - 1`.

* Rows of `X` point into `X ∪ Y`, rows of `Y` into `X ∪ Y ∪ Z` (an arc back to the root closes a
  walk of length at most three).
* A sink of `D[X]` points to all `r` labels of `Y`. A sink of `D[Y]` has a head in `X`, since at
  most `r - 1` of its heads are new.
* `X` and `Y` have at most `q` labels, so every nonempty subset has a sink (`exists_sink`) and
  there is no closed walk inside either (`no_cycle`).
* Call `p ∈ X` a return target if some label of `Y` points to `p`. Then no sink of `D[X]` lies
  within `r - 2` of `p` inside `X`: it would close a walk `p ⇝ s → t → p` of length at most `r`.
  So the balls of `p` inside `X` strictly grow up to radius `r - 1` (`grow`), the `(r-1)`-ball is
  all of `X`, and two return targets would reach each other: a closed walk inside `X`. The
  return target is unique.
* `p` has at most one head in `X`: with two, the `1`-ball has three labels and the
  `(r-1)`-ball would have `r + 1`.
* `p` has at most one head in `Y`: inside `W = {p} ∪ Y` the balls of `p` strictly grow up to
  radius `r`. A closed ball would have a sink of `D[Y]` in it besides `p`; its head in `X` is a
  return target, so it is `p`, and that closes a walk of length at most `r`. Two heads in `Y`
  would make the `r`-ball have `r + 2 > |W|` labels.
* So `p` has at most two heads, all in `X ∪ Y`, against out-degree `r ≥ 3`.

`flatQ q r` is the pattern `q = r`, second layer exactly `r`, third layer at most `r - 1`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FlatAtCutoff
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)

variable {D : CH.Digraph}

theorem walk_first {W : Finset ℕ} {a b n : ℕ} (w : Walk D W a b (n + 1)) :
    ∃ c, c ∈ W ∧ D a c = true ∧ Walk D W c b n := by
  cases w with
  | step hc hac w' => exact ⟨_, hc, hac, w'⟩

theorem walk_zero {W : Finset ℕ} {a b : ℕ} (w : Walk D W a b 0) : a = b := by
  cases w
  rfl

/-- A `q`-free set of at most `q` labels has no closed walk of positive length at all. -/
theorem no_cycle {W : Finset ℕ} {q : ℕ} (free : QFree D W q) (small : W.card ≤ q)
    {a n : ℕ} (hn : 1 ≤ n) (w : Walk D W a a n) : False := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have aW : a ∈ W := (w.unsnoc).choose_spec.2.1
  let C := W.filter (fun v => ∃ m, 1 ≤ m ∧ Walk D W v v m)
  have aC : a ∈ C := mem_filter.mpr ⟨aW, n' + 1, by omega, w⟩
  obtain ⟨s, sC, sink⟩ := exists_sink (free.mono_set (filter_subset _ _)) ⟨a, aC⟩
    ((card_le_card (filter_subset _ _)).trans small)
  obtain ⟨sW, m, hm, ws⟩ := mem_filter.mp sC
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨c, cW, sc, wc⟩ := walk_first ws
  exact sink c (mem_filter.mpr ⟨cW, m' + 1, by omega, wc.snoc cW sc⟩) sc

/-- Balls that are never closed grow by at least one label per step. -/
theorem grow {W : Finset ℕ} {p a M : ℕ}
    (opn : ∀ j, a ≤ j → j < a + M →
      ∃ v ∈ ball D W p j, ∃ w ∈ W, D v w = true ∧ w ∉ ball D W p j) :
    (ball D W p a).card + M ≤ (ball D W p (a + M)).card := by
  suffices h : ∀ m, m ≤ M → (ball D W p a).card + m ≤ (ball D W p (a + m)).card from h M le_rfl
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have prev := ih (by omega)
    obtain ⟨v, hv, w, wW, vw, wout⟩ := opn (a + m) (by omega) (by omega)
    have sub : ball D W p (a + m) ⊆ ball D W p (a + (m + 1)) := ball_mono_radius (by omega)
    have win : w ∈ ball D W p (a + (m + 1)) := ball_step hv wW vw
    have lt := card_lt_card ((ssubset_iff_of_subset sub).mpr ⟨w, win, wout⟩)
    omega

/-- **The flat dip at the cutoff.** A root with exactly `r` heads and exactly `r` labels in its
second layer, in a `q`-free digraph of minimum out-degree at least `r`, `3 ≤ r ≤ q`, has at least
`r` labels in its third layer. -/
theorem flat_third {D : CH.Digraph} {V : Finset ℕ} {q r u : ℕ} (free : QFree D V q)
    (hr : 3 ≤ r) (rq : r ≤ q) (hu : u ∈ V) (heads : (outN D V u).card = r)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (second : (layer D V 2 u).card = r) :
    r ≤ (layer D V 3 u).card := by
  classical
  by_contra! thin
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  have hX : X ⊆ V := outN_subset
  have hY : Y ⊆ V := fun w hw => ball_subset (mem_layer.mp hw).1
  have XnY : ∀ x ∈ X, x ∉ Y := by
    intro x hx hy
    exact (mem_layer.mp hy).2 ((mem_ball_one hu).mpr (Or.inr hx))
  -- rows of `X` and `Y`
  have rowX : ∀ x ∈ X, ∀ w ∈ V, D x w = true → w ∈ X ∨ w ∈ Y := by
    intro x hx w wV xw
    have x1 : x ∈ ball D V u 1 := (mem_ball_one hu).mpr (Or.inr hx)
    have w2 : w ∈ ball D V u 2 := ball_step x1 wV xw
    by_cases w1 : w ∈ ball D V u 1
    · rcases (mem_ball_one hu).mp w1 with rfl | wX
      · exact (free _ 2 (by omega) (by omega)
          (.step (hX hx) (mem_outN.mp hx).2 (.step wV xw (.refl _)))).elim
      · exact Or.inl wX
    · exact Or.inr (mem_layer.mpr ⟨w2, w1⟩)
  have rowY : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ X ∨ w ∈ Y ∨ w ∈ Z := by
    intro y hy w wV yw
    have y2 : y ∈ ball D V u 2 := (mem_layer.mp hy).1
    by_cases w2 : w ∈ ball D V u 2
    · by_cases w1 : w ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp w1 with rfl | wX
        · obtain ⟨-, i, hi, wi⟩ := mem_ball.mp y2
          exact (free _ (i + 1) (by omega) (by omega) (wi.snoc wV yw)).elim
        · exact Or.inl wX
      · exact Or.inr (Or.inl (mem_layer.mpr ⟨w2, w1⟩))
    · exact Or.inr (Or.inr (mem_layer.mpr ⟨ball_step y2 wV yw, w2⟩))
  -- sinks of `D[X]` and `D[Y]`
  have Xsink : ∀ s ∈ X, (∀ w ∈ X, ¬ D s w = true) → ∀ y ∈ Y, D s y = true := by
    intro s hs sink
    have sub : outN D V s ⊆ Y := by
      intro w hw
      obtain ⟨wV, sw⟩ := mem_outN.mp hw
      rcases rowX s hs w wV sw with wX | wY
      · exact (sink w wX sw).elim
      · exact wY
    have eq : outN D V s = Y :=
      eq_of_subset_of_card_le sub (by rw [second]; exact deg s (hX hs))
    intro y hy
    rw [← eq] at hy
    exact (mem_outN.mp hy).2
  have Ysink : ∀ t ∈ Y, (∀ w ∈ Y, ¬ D t w = true) → ∃ x ∈ X, D t x = true := by
    intro t ht sink
    by_contra none
    have sub : outN D V t ⊆ Z := by
      intro w hw
      obtain ⟨wV, tw⟩ := mem_outN.mp hw
      rcases rowY t ht w wV tw with wX | wY | wZ
      · exact (none ⟨w, wX, tw⟩).elim
      · exact (sink w wY tw).elim
      · exact wZ
    have := (deg t (hY ht)).trans (card_le_card sub)
    omega
  -- a return target `p` (some label of `Y` points to it) has no `X`-sink within `r - 2`
  have openX : ∀ p ∈ X, (∃ t ∈ Y, D t p = true) → ∀ j, j ≤ r - 2 →
      ∃ v ∈ ball D X p j, ∃ w ∈ X, D v w = true ∧ w ∉ ball D X p j := by
    intro p hp back j hj
    obtain ⟨t, ht, tp⟩ := back
    by_contra hc
    have closed : ∀ v ∈ ball D X p j, ∀ w ∈ X, D v w = true → w ∈ ball D X p j :=
      fun v hv w hw vw => by_contra fun hn => hc ⟨v, hv, w, hw, vw, hn⟩
    obtain ⟨s, sB, sink⟩ := exists_sink ((free.mono_set hX).mono_set ball_subset)
      ⟨p, self_mem_ball hp⟩ ((card_le_card ball_subset).trans (by omega))
    have sX : ∀ w ∈ X, ¬ D s w = true := fun w hw sw => sink w (closed s sB w hw sw) sw
    have st := Xsink s (ball_subset sB) sX t ht
    obtain ⟨-, i, hi, wi⟩ := mem_ball.mp sB
    exact free p (i + 1 + 1) (by omega) (by omega)
      (((wi.mono hX).snoc (hY ht) st).snoc (hX hp) tp)
  have fullX : ∀ p ∈ X, (∃ t ∈ Y, D t p = true) → ball D X p (r - 1) = X := by
    intro p hp back
    have g := grow (W := X) (p := p) (a := 0) (M := r - 1)
      (fun j _ hj => openX p hp back j (by omega))
    have one : 1 ≤ (ball D X p 0).card := card_pos.mpr ⟨p, self_mem_ball hp⟩
    rw [Nat.zero_add] at g
    exact eq_of_subset_of_card_le ball_subset (by omega)
  have unique : ∀ p ∈ X, (∃ t ∈ Y, D t p = true) →
      ∀ x ∈ X, (∃ t ∈ Y, D t x = true) → x = p := by
    intro p hp bp x hx bx
    by_contra ne
    have xin : x ∈ ball D X p (r - 1) := by rw [fullX p hp bp]; exact hx
    have pin : p ∈ ball D X x (r - 1) := by rw [fullX x hx bx]; exact hp
    obtain ⟨-, i, -, wi⟩ := mem_ball.mp xin
    obtain ⟨-, j, -, wj⟩ := mem_ball.mp pin
    rcases Nat.eq_zero_or_pos i with rfl | ipos
    · exact ne (walk_zero wi).symm
    · exact no_cycle (free.mono_set hX) (by omega) (by omega : 1 ≤ i + j) (wi.append wj)
  -- at most one head in `X`
  have headsX : ∀ p ∈ X, (∃ t ∈ Y, D t p = true) → (outN D X p).card ≤ 1 := by
    intro p hp back
    by_contra! two
    have pp := loopfree free (by omega) (hX hp)
    have sub : insert p (outN D X p) ⊆ ball D X p 1 := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact self_mem_ball hp
      · exact (mem_ball_one hp).mpr (Or.inr hv)
    have notin : p ∉ outN D X p := fun h => pp (mem_outN.mp h).2
    have c1 := card_le_card sub
    rw [card_insert_of_notMem notin] at c1
    have g := grow (W := X) (p := p) (a := 1) (M := r - 2)
      (fun j _ hj => openX p hp back j (by omega))
    have cap : (ball D X p (1 + (r - 2))).card ≤ X.card := card_le_card ball_subset
    omega
  -- at most one head in `Y`
  have headsY : ∀ p ∈ X, (∃ t ∈ Y, D t p = true) → (outN D Y p).card ≤ 1 := by
    intro p hp back
    by_contra! two
    have pY : p ∉ Y := XnY p hp
    obtain ⟨W, hW⟩ : ∃ W, W = insert p Y := ⟨_, rfl⟩
    have pW : p ∈ W := hW ▸ mem_insert_self p Y
    have YW : Y ⊆ W := hW ▸ subset_insert p Y
    have WV : W ⊆ V := hW ▸ insert_subset (hX hp) hY
    have headW : ∀ v ∈ outN D Y p, v ∈ ball D W p 1 := fun v hv =>
      (mem_ball_one pW).mpr (Or.inr (mem_outN.mpr ⟨YW (mem_outN.mp hv).1, (mem_outN.mp hv).2⟩))
    have sub : insert p (outN D Y p) ⊆ ball D W p 1 := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact self_mem_ball pW
      · exact headW v hv
    have notin : p ∉ outN D Y p := fun h => pY (mem_outN.mp h).1
    have c1 := card_le_card sub
    rw [card_insert_of_notMem notin] at c1
    obtain ⟨y0, hy0⟩ : (outN D Y p).Nonempty := card_pos.mp (by omega)
    have openY : ∀ j, 1 ≤ j → j < 1 + (r - 1) →
        ∃ v ∈ ball D W p j, ∃ w ∈ W, D v w = true ∧ w ∉ ball D W p j := by
      intro j hj1 hj
      by_contra hc
      have closed : ∀ v ∈ ball D W p j, ∀ w ∈ W, D v w = true → w ∈ ball D W p j :=
        fun v hv w hw vw => by_contra fun hn => hc ⟨v, hv, w, hw, vw, hn⟩
      have SY : (ball D W p j).erase p ⊆ Y := by
        intro v hv
        obtain ⟨vp, vB⟩ := mem_erase.mp hv
        have vW : v ∈ insert p Y := hW ▸ ball_subset vB
        rcases mem_insert.mp vW with h | h
        · exact (vp h).elim
        · exact h
      have y0S : y0 ∈ (ball D W p j).erase p :=
        mem_erase.mpr ⟨fun h => pY (by rw [← h]; exact (mem_outN.mp hy0).1),
          ball_mono_radius hj1 (headW y0 hy0)⟩
      obtain ⟨t, tS, sink⟩ := exists_sink ((free.mono_set hY).mono_set SY) ⟨y0, y0S⟩
        ((card_le_card SY).trans (by omega))
      have tY := SY tS
      have tsink : ∀ w ∈ Y, ¬ D t w = true := by
        intro w hw tw
        have wB := closed t (mem_erase.mp tS).2 w (YW hw) tw
        exact sink w (mem_erase.mpr ⟨fun h => pY (by rw [← h]; exact hw), wB⟩) tw
      obtain ⟨x, hx, tx⟩ := Ysink t tY tsink
      have xp : x = p := unique p hp back x hx ⟨t, tY, tx⟩
      rw [xp] at tx
      obtain ⟨-, i, hi, wi⟩ := mem_ball.mp (mem_erase.mp tS).2
      exact free _ (i + 1) (by omega) (by omega) ((wi.snoc pW tx).mono WV)
    have g := grow (W := W) (p := p) (a := 1) (M := r - 1) openY
    have cW : W.card ≤ r + 1 := by
      have := card_insert_le p Y
      rw [← hW] at this
      omega
    have cap : (ball D W p (1 + (r - 1))).card ≤ W.card := card_le_card ball_subset
    omega
  -- the return target has too few heads
  have Yne : Y.Nonempty := card_pos.mp (by omega)
  obtain ⟨t, tY, tsink⟩ := exists_sink (free.mono_set hY) Yne (by omega)
  obtain ⟨p, hp, tp⟩ := Ysink t tY tsink
  have back : ∃ t ∈ Y, D t p = true := ⟨t, tY, tp⟩
  have sub : outN D V p ⊆ outN D X p ∪ outN D Y p := by
    intro w hw
    obtain ⟨wV, pw⟩ := mem_outN.mp hw
    rcases rowX p hp w wV pw with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, pw⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨h, pw⟩)
  have total := (deg p (hX hp)).trans ((card_le_card sub).trans (card_union_le _ _))
  have h1 := headsX p hp back
  have h2 := headsY p hp back
  omega

/-- `q = r`: a second layer of exactly `r` labels and a third layer of at most `r - 1`. -/
def flatQ (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (q = r ∧ 3 ≤ r ∧ 2 ≤ ws.length ∧ ws.getD 1 0 = r ∧
    (if 3 ≤ ws.length then ws.getD 2 0 else last) + 1 ≤ r)

theorem flatQ_sound (q r : ℕ) : ShapeClimbX.SoundX q r (flatQ q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨qr, hr, len, w2, w3⟩ := of_decide_eq_true h
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have third := flat_third free hr (by omega) hu root deg (by omega)
  by_cases long : 3 ≤ ws.length
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    simp only [long, ↓reduceIte] at w3
    omega
  · simp only [long, ↓reduceIte] at w3
    have e : ws.length + 1 = 3 := by omega
    rw [e] at bound
    omega

#print axioms flat_third
#print axioms flatQ_sound
end LeanCH.BR.FlatAtCutoff
