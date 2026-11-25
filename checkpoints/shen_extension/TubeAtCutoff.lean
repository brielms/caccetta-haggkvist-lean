import checkpoints.shen_extension.FlatAtCutoff

/-!
# The flat tube and the loop dip at the cutoff

Two dead width patterns for a root of out-degree exactly `r` in a `q`-free digraph of minimum
out-degree `r`, `r ≤ q` (the case that matters is `r = q`).

* `flat_fourth` (`5 ≤ r`): widths `(r, r, r)` force a fourth layer of at least `r` labels.
* `loop_dip_recover` (`8 ≤ r`): widths `(r, r + 1, r - 1)` force a fourth layer of at least `r`.

Write `X, Y, Z, W` for the first four layers. Both proofs use balls inside a layer: in a set `S`
of at most `q` labels (no closed walk at all, `FlatAtCutoff.no_cycle`) call `v` *deep* to radius
`m` if no sink of `D[S]` lies within `m` of `v`. Deep balls grow by one label per step
(`deep_grow`), a deep label has few heads in `S` (`deep_heads`), and there are at most one deep
label when `|S| ≤ m + 2` (`two_deep`) and at most two when `|S| ≤ m + 3` (`three_deep`).

`flat_fourth`. Sinks of `D[X]` head all of `Y`. A return `t → p` from `Y` into `X` makes `p`
deep to radius `r - 2` in `X`, so the return target `x` is unique and has at most one head in
`X`; its `Y`-heads `A` miss only the return tail `t₀`.
* With a return: rows of `A` stay in `A ∪ Z` (an arc to `X` is a digon at `x`, an arc to `t₀`
  a triangle through `x`), so sinks of `D[A]` head all of `Z`, and every label of `A` reaches
  one within `r - 2`. A `Z → A` arc closes within `r`, `Z → t₀` closes `z → t₀ → x → a → z`,
  and a `Z → X` target is deep to radius `r - 3` in `X`, so it has at least two heads in `A`,
  both deep to radius `r - 3` in `A`, against `two_deep`.
* Without a return: sinks of `D[Y]` head all of `Z`. A `Z → X` target has at least three heads
  in `Y`, all deep to radius `r - 3`, against `three_deep`. A `Z → Y` target is deep to radius
  `r - 2`, so it is unique, has at most one head in `Y`, and its `Z`-heads `B` miss only the
  return tail; rows of `B` then stay in `B ∪ W`.
In either case some sink of `D[Z]` (or `D[B]`) has all `r` heads in `W`, which has `r - 1`.

`loop_dip_recover`. Sinks of `D[X]` miss at most one label of `Y`; a label deep to radius
`r - 3` in `X` misses at most three. For a return `t → p` with `t ∈ Y`, every `Y`-ancestor of
`t` is missed by a sink of `X` (if `p` is shallow) or by `p` itself (if `p` is deep): the
ancestors within `r - 2` of `t` are missed by `p`, and they are at least `r - 1` if any
ancestor is farther (`reach_or_grow` on the reversed digraph).
* If `D[Y]` has a sink, every label of `Y` reaches a sink of `D[Y]`, and every such sink
  returns to `X` because `Z` has only `r - 1` labels. So `Y` is covered by the misses of the
  sinks and deep labels of `X`: at most `r` labels if no label is deep, else at most
  `2 + 2 · 3 = 8 < r + 1`.
* If `D[Y]` has no sink, the ancestor set of a return tail is a proper parent-closed subset of
  `Y`, whose complement would contain a sink: so there is no return. Every label of `Y` has a
  parent and (by ball growth) exactly one head in `Y`, hence heads all of `Z`; every label of
  `X` has a head in `Y`; so rows of `Z` stay in `Z ∪ W`.

The paper source (degree-nine dossier, Appendix 19 "Exclude b=18 locally" and Appendix 20
"Cutoff-nine transfer: 80 vertices") argues with nearest-sink depths; the balls replace them.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TubeAtCutoff
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open FlatAtCutoff (no_cycle grow)

variable {D : CH.Digraph}

/-! ### Balls inside a small set -/

/-- `s` has no head in `S`. -/
def IsSink (D : CH.Digraph) (S : Finset ℕ) (s : ℕ) : Prop := ∀ w ∈ S, ¬ D s w = true

/-- No sink of `D[S]` lies within `m` of `v`. -/
def Deep (D : CH.Digraph) (S : Finset ℕ) (m v : ℕ) : Prop := ∀ s ∈ ball D S v m, ¬ IsSink D S s

theorem ball_card_le {S : Finset ℕ} {v m : ℕ} : (ball D S v m).card ≤ S.card :=
  card_le_card ball_subset

/-- A closed ball of at most `q` labels contains a sink of `D[S]`. -/
theorem closed_sink {S : Finset ℕ} {q v j : ℕ} (free : QFree D S q) (hv : v ∈ S)
    (small : (ball D S v j).card ≤ q)
    (cl : ∀ a ∈ ball D S v j, ∀ w ∈ S, D a w = true → w ∈ ball D S v j) :
    ∃ s ∈ ball D S v j, IsSink D S s := by
  obtain ⟨s, sB, sink⟩ := exists_sink (free.mono_set ball_subset) ⟨v, self_mem_ball hv⟩ small
  exact ⟨s, sB, fun w hw sw => sink w (cl s sB w hw sw) sw⟩

theorem deep_open {S : Finset ℕ} {q m v : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hv : v ∈ S) (dp : Deep D S m v) {j : ℕ} (hj : j ≤ m) :
    ∃ a ∈ ball D S v j, ∃ w ∈ S, D a w = true ∧ w ∉ ball D S v j := by
  by_contra hc
  have cl : ∀ a ∈ ball D S v j, ∀ w ∈ S, D a w = true → w ∈ ball D S v j :=
    fun a ha w hw aw => by_contra fun hn => hc ⟨a, ha, w, hw, aw, hn⟩
  obtain ⟨s, sB, sink⟩ := closed_sink free hv (ball_card_le.trans small) cl
  exact dp s (ball_mono_radius hj sB) sink

/-- Deep balls grow by one label per step. -/
theorem deep_grow {S : Finset ℕ} {q m v : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hv : v ∈ S) (dp : Deep D S m v) {k : ℕ} (hk : k ≤ m + 1) :
    k + 1 ≤ (ball D S v k).card := by
  have g := grow (W := S) (p := v) (a := 0) (M := k)
    (fun j _ hj => deep_open free small hv dp (by omega))
  have one : 1 ≤ (ball D S v 0).card := card_pos.mpr ⟨v, self_mem_ball hv⟩
  rw [Nat.zero_add] at g
  omega

/-- A label deep to radius `m` has at most `|S| - m - 1` heads in `S`. -/
theorem deep_heads {S : Finset ℕ} {q m v : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hv : v ∈ S) (dp : Deep D S m v) : (outN D S v).card + m + 1 ≤ S.card := by
  have pp := loopfree free (by have := card_pos.mpr ⟨v, hv⟩; omega) hv
  have sub : insert v (outN D S v) ⊆ ball D S v 1 := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact self_mem_ball hv
    · exact (mem_ball_one hv).mpr (Or.inr hw)
  have notin : v ∉ outN D S v := fun h => pp (mem_outN.mp h).2
  have c1 := card_le_card sub
  rw [card_insert_of_notMem notin] at c1
  have g := grow (W := S) (p := v) (a := 1) (M := m)
    (fun j _ hj => deep_open free small hv dp (by omega))
  have cap : (ball D S v (1 + m)).card ≤ S.card := ball_card_le
  omega

/-- Every label of `S` has a sink of `D[S]` within `|S| - 1`. -/
theorem sink_within {S : Finset ℕ} {q m v : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hv : v ∈ S) (hm : S.card ≤ m + 1) : ∃ s ∈ ball D S v m, IsSink D S s := by
  by_contra h
  have dp : Deep D S m v := fun s hs sk => h ⟨s, hs, sk⟩
  have := deep_grow free small hv dp (le_refl (m + 1))
  have := ball_card_le (D := D) (S := S) (v := v) (m := m + 1)
  omega

theorem deep_full {S : Finset ℕ} {q m v : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hv : v ∈ S) (dp : Deep D S m v) (hm : S.card ≤ m + 2) : ball D S v (m + 1) = S :=
  eq_of_subset_of_card_le ball_subset (by have := deep_grow free small hv dp (le_refl (m + 1)); omega)

theorem no_mutual {S : Finset ℕ} {q a b i j : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (ab : a ≠ b) (wi : Walk D S a b i) (wj : Walk D S b a j) : False := by
  rcases Nat.eq_zero_or_pos i with rfl | ipos
  · exact ab (walk_zero wi)
  · exact no_cycle free small (by omega : 1 ≤ i + j) (wi.append wj)

/-- At most one label is deep to radius `m` when `|S| ≤ m + 2`. -/
theorem two_deep {S : Finset ℕ} {q m v v' : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hm : S.card ≤ m + 2) (hv : v ∈ S) (hv' : v' ∈ S) (dv : Deep D S m v) (dv' : Deep D S m v') :
    v = v' := by
  by_contra ne
  have a : v' ∈ ball D S v (m + 1) := by rw [deep_full free small hv dv hm]; exact hv'
  have b : v ∈ ball D S v' (m + 1) := by rw [deep_full free small hv' dv' hm]; exact hv
  obtain ⟨-, i, -, wi⟩ := mem_ball.mp a
  obtain ⟨-, j, -, wj⟩ := mem_ball.mp b
  exact no_mutual free small ne wi wj

/-- At most two labels are deep to radius `m` when `|S| ≤ m + 3`. -/
theorem three_deep {S : Finset ℕ} {q m a b c : ℕ} (free : QFree D S q) (small : S.card ≤ q)
    (hm : S.card ≤ m + 3) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ab : a ≠ b) (ac : a ≠ c)
    (bc : b ≠ c) (da : Deep D S m a) (db : Deep D S m b) (dc : Deep D S m c) : False := by
  classical
  have miss : ∀ v ∈ S, Deep D S m v → ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      x ∉ ball D S v (m + 1) → y ∉ ball D S v (m + 1) → False := by
    intro v hv dv x hx y hy xy nx ny
    have g := deep_grow free small hv dv (le_refl (m + 1))
    have sub : ball D S v (m + 1) ⊆ (S.erase x).erase y := by
      intro w hw
      refine mem_erase.mpr ⟨fun h => ny (h ▸ hw), mem_erase.mpr ⟨fun h => nx (h ▸ hw), ball_subset hw⟩⟩
    have c := card_le_card sub
    have e1 := card_erase_add_one (mem_erase.mpr ⟨xy.symm, hy⟩)
    have e2 := card_erase_add_one hx
    have := ball_card_le (D := D) (S := S) (v := v) (m := m + 1)
    omega
  have mutl : ∀ x y, x ≠ y → x ∈ ball D S y (m + 1) → y ∈ ball D S x (m + 1) → False := by
    intro x y xy hx hy
    obtain ⟨-, i, -, wi⟩ := mem_ball.mp hy
    obtain ⟨-, j, -, wj⟩ := mem_ball.mp hx
    exact no_mutual free small xy wi wj
  have tri : ∀ x y z, x ≠ y → y ∈ ball D S x (m + 1) → z ∈ ball D S y (m + 1) →
      x ∈ ball D S z (m + 1) → False := by
    intro x y z xy hy hz hx
    obtain ⟨-, i, -, wi⟩ := mem_ball.mp hy
    obtain ⟨-, j, -, wj⟩ := mem_ball.mp hz
    obtain ⟨-, k, -, wk⟩ := mem_ball.mp hx
    rcases Nat.eq_zero_or_pos i with rfl | ipos
    · exact xy (walk_zero wi)
    · exact no_cycle free small (by omega : 1 ≤ i + j + k) ((wi.append wj).append wk)
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

/-- Either some ball between radii `a` and `a + M` is closed, or the balls grow. -/
theorem closed_or_grow {S : Finset ℕ} {v a M : ℕ} :
    (∃ j, a ≤ j ∧ j < a + M ∧ ∀ x ∈ ball D S v j, ∀ w ∈ S, D x w = true → w ∈ ball D S v j) ∨
      (ball D S v a).card + M ≤ (ball D S v (a + M)).card := by
  by_cases opn : ∀ j, a ≤ j → j < a + M →
      ∃ x ∈ ball D S v j, ∃ w ∈ S, D x w = true ∧ w ∉ ball D S v j
  · exact Or.inr (grow opn)
  · left
    by_contra hc
    exact opn fun j h0 hj => by
      by_contra hn
      exact hc ⟨j, h0, hj, fun x hx w hw xw => by_contra fun hw' => hn ⟨x, hx, w, hw, xw, hw'⟩⟩

/-- A label reachable from `v` is within `M` of it, or the `M`-ball has `M + 1` labels. -/
theorem reach_or_grow {S : Finset ℕ} {v x n M : ℕ} (hv : v ∈ S) (hx : x ∈ ball D S v n) :
    x ∈ ball D S v M ∨ M + 1 ≤ (ball D S v M).card := by
  by_cases opn : ∀ j, 0 ≤ j → j < 0 + M →
      ∃ a ∈ ball D S v j, ∃ w ∈ S, D a w = true ∧ w ∉ ball D S v j
  · right
    have g := grow opn
    have one : 1 ≤ (ball D S v 0).card := card_pos.mpr ⟨v, self_mem_ball hv⟩
    rw [Nat.zero_add] at g
    omega
  · left
    obtain ⟨j, -, hj, cl⟩ : ∃ j, 0 ≤ j ∧ j < 0 + M ∧
        ∀ a ∈ ball D S v j, ∀ w ∈ S, D a w = true → w ∈ ball D S v j := by
      by_contra hc
      exact opn fun j h0 hj => by
        by_contra hn
        exact hc ⟨j, h0, hj, fun a ha w hw aw => by_contra fun hw' => hn ⟨a, ha, w, hw, aw, hw'⟩⟩
    have absorb : ∀ i y, Walk D S v y i → y ∈ ball D S v j := by
      intro i
      induction i with
      | zero => intro y w; rw [← walk_zero w]; exact self_mem_ball hv
      | succ i ih =>
        intro y w
        obtain ⟨y', w', yS, y'y⟩ := w.unsnoc
        exact cl y' (ih y' w') y yS y'y
    obtain ⟨-, i, -, wi⟩ := mem_ball.mp hx
    exact ball_mono_radius (by omega) (absorb i x wi)

/-- The reversed digraph. -/
def rev (D : CH.Digraph) : CH.Digraph := fun a b => D b a

theorem walk_rev {S : Finset ℕ} {a b n : ℕ} (ha : a ∈ S) (w : Walk D S a b n) :
    Walk (rev D) S b a n := by
  induction w with
  | refl a => exact .refl a
  | step hb hab _ ih => exact (ih hb).snoc ha hab

/-- A proper parent-closed subset of a set of at most `q + 1` labels leaves a sink. -/
theorem pclosed_sink {Y C : Finset ℕ} {q c y0 : ℕ} (free : QFree D Y q) (hY : Y.card ≤ q + 1)
    (sub : C ⊆ Y) (hc : c ∈ C) (hy0 : y0 ∈ Y) (ny0 : y0 ∉ C)
    (pc : ∀ a ∈ Y, ∀ b ∈ C, D a b = true → a ∈ C) : ∃ t ∈ Y, IsSink D Y t := by
  classical
  have card : (Y \ C).card ≤ q := by
    rw [card_sdiff_of_subset sub]
    have := card_pos.mpr ⟨c, hc⟩
    omega
  obtain ⟨t, tT, sink⟩ := exists_sink (free.mono_set sdiff_subset) ⟨y0, mem_sdiff.mpr ⟨hy0, ny0⟩⟩ card
  refine ⟨t, (mem_sdiff.mp tT).1, fun w hw tw => ?_⟩
  by_cases wC : w ∈ C
  · exact (mem_sdiff.mp tT).2 (pc t (mem_sdiff.mp tT).1 w wC tw)
  · exact sink w (mem_sdiff.mpr ⟨hw, wC⟩) tw

/-- Two labels of `Y` outside `A ⊆ Y`. -/
theorem card_two_out {A Y : Finset ℕ} {a b : ℕ} (sub : A ⊆ Y) (ha : a ∈ Y) (hb : b ∈ Y)
    (na : a ∉ A) (nb : b ∉ A) (ab : a ≠ b) : A.card + 2 ≤ Y.card := by
  have s : A ⊆ (Y.erase a).erase b := fun w hw =>
    mem_erase.mpr ⟨fun h => nb (h ▸ hw), mem_erase.mpr ⟨fun h => na (h ▸ hw), sub hw⟩⟩
  have c := card_le_card s
  have e1 := card_erase_add_one (mem_erase.mpr ⟨ab.symm, hb⟩)
  have e2 := card_erase_add_one ha
  omega

/-- A row confined to at most `r - 1` labels has degree below `r`. -/
theorem too_few {V T : Finset ℕ} {r v : ℕ} (sub : outN D V v ⊆ T) (hT : T.card + 1 ≤ r)
    (hd : r ≤ (outN D V v).card) : False := by
  have := card_le_card sub
  omega

/-- A row confined to at most `r` labels heads all of them. -/
theorem full_of_sub {V T : Finset ℕ} {r v : ℕ} (sub : outN D V v ⊆ T) (hT : T.card ≤ r)
    (hd : r ≤ (outN D V v).card) : ∀ y ∈ T, D v y = true := by
  have eq := eq_of_subset_of_card_le sub (hT.trans hd)
  intro y hy
  rw [← eq] at hy
  exact (mem_outN.mp hy).2

/-! ### Layers -/

section layers
variable {V : Finset ℕ} {q u : ℕ}

theorem row_ball (free : QFree D V q) {i v w : ℕ} (hv : v ∈ ball D V u i) (wV : w ∈ V)
    (vw : D v w = true) (hi : i + 1 ≤ q) : w ≠ u ∧ w ∈ ball D V u (i + 1) := by
  refine ⟨?_, ball_step hv wV vw⟩
  rintro rfl
  obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hv
  exact free w (j + 1) (by omega) (by omega) (wj.snoc wV vw)

theorem classify (hu : u ∈ V) {w : ℕ} (hw : w ∈ ball D V u 4) (wu : w ≠ u) :
    w ∈ outN D V u ∨ w ∈ layer D V 2 u ∨ w ∈ layer D V 3 u ∨ w ∈ layer D V 4 u := by
  by_cases h1 : w ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp h1 with h | h
    · exact (wu h).elim
    · exact Or.inl h
  by_cases h2 : w ∈ ball D V u 2
  · exact Or.inr (Or.inl (mem_layer.mpr ⟨h2, h1⟩))
  by_cases h3 : w ∈ ball D V u 3
  · exact Or.inr (Or.inr (Or.inl (mem_layer.mpr ⟨h3, h2⟩)))
  · exact Or.inr (Or.inr (Or.inr (mem_layer.mpr ⟨hw, h3⟩)))

theorem x_ball (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) : x ∈ ball D V u 1 :=
  (mem_ball_one hu).mpr (Or.inr hx)

theorem layer_in {k y : ℕ} (hy : y ∈ layer D V k u) : y ∈ ball D V u k := (mem_layer.mp hy).1

theorem layer_out {k j y : ℕ} (hy : y ∈ layer D V k u) (hj : j + 1 ≤ k) : y ∉ ball D V u j :=
  fun h => (mem_layer.mp hy).2 (ball_mono_radius (by omega) h)

end layers

/-! ### The flat tube -/

/-- **The flat tube at the cutoff.** A root with exactly `r` heads and exactly `r` labels in its
second and third layers, in a `q`-free digraph of minimum out-degree at least `r`,
`5 ≤ r ≤ q`, has at least `r` labels in its fourth layer. -/
theorem flat_fourth {V : Finset ℕ} {q r u : ℕ} (free : QFree D V q)
    (hr : 5 ≤ r) (rq : r ≤ q) (hu : u ∈ V) (heads : (outN D V u).card = r)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (second : (layer D V 2 u).card = r)
    (third : (layer D V 3 u).card = r) : r ≤ (layer D V 4 u).card := by
  classical
  by_contra! thin
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set W := layer D V 4 u with hWdef
  have hX : X ⊆ V := outN_subset
  have hY : Y ⊆ V := fun w hw => ball_subset (layer_in hw)
  have hZ : Z ⊆ V := fun w hw => ball_subset (layer_in hw)
  have fX : QFree D X q := free.mono_set hX
  have fY : QFree D Y q := free.mono_set hY
  have fZ : QFree D Z q := free.mono_set hZ
  have cX : X.card ≤ q := by omega
  have cY : Y.card ≤ q := by omega
  -- rows
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
  have XnY : ∀ x ∈ X, x ∉ Y := fun x hx hy => layer_out hy le_rfl (x_ball hu hx)
  have YnZ : ∀ y ∈ Y, y ∉ Z := fun y hy hz => layer_out hz le_rfl (layer_in hy)
  -- sinks of `X` head all of `Y`
  have Xsink : ∀ s ∈ X, IsSink D X s → ∀ y ∈ Y, D s y = true := by
    intro s hs sink
    refine full_of_sub (V := V) ?_ second.le (deg s (hX hs))
    intro w hw
    obtain ⟨wV, sw⟩ := mem_outN.mp hw
    rcases rowX s hs w wV sw with h | h
    · exact (sink w h sw).elim
    · exact h
  have closeX : ∀ p ∈ X, ∀ s ∈ ball D X p (r - 2), ∀ {k : ℕ} {y : ℕ}, y ∈ V → D s y = true →
      Walk D V y p k → k + (r - 2) + 1 ≤ r → False := by
    intro p hp s hs k y yV sy wk hk
    obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
    exact free p (j + 1 + k) (by omega) (by omega) (((wj.mono hX).snoc yV sy).append wk)
  by_cases ret : ∃ t ∈ Y, ∃ p ∈ X, D t p = true
  · -- a return from `Y` into `X`
    obtain ⟨t0, ht0, x, hx, t0x⟩ := ret
    have tgt : ∀ t ∈ Y, ∀ p ∈ X, D t p = true → Deep D X (r - 2) p := by
      intro t ht p hp tp s hs sink
      exact closeX p hp s hs (hY ht)
        (Xsink s (ball_subset hs) sink t ht) (.step (hX hp) tp (.refl p)) (by omega)
    have uniq : ∀ t ∈ Y, ∀ p ∈ X, D t p = true → p = x := fun t ht p hp tp =>
      two_deep fX cX (by omega) hp hx (tgt t ht p hp tp) (tgt t0 ht0 x hx t0x)
    have hx1 := deep_heads fX cX hx (tgt t0 ht0 x hx t0x)
    set A := outN D Y x with hAdef
    have AY : A ⊆ Y := outN_subset
    have hA : r ≤ (outN D X x).card + A.card := by
      have sub : outN D V x ⊆ outN D X x ∪ A := by
        intro w hw
        obtain ⟨wV, xw⟩ := mem_outN.mp hw
        rcases rowX x hx w wV xw with h | h
        · exact mem_union_left _ (mem_outN.mpr ⟨h, xw⟩)
        · exact mem_union_right _ (mem_outN.mpr ⟨h, xw⟩)
      exact (deg x (hX hx)).trans ((card_le_card sub).trans (card_union_le _ _))
    have t0A : t0 ∉ A := fun h =>
      digonfree free (by omega) (hX hx) (hY ht0) (mem_outN.mp h).2 t0x
    have YA : ∀ y ∈ Y, y ∉ A → y = t0 := by
      intro y hy ny
      by_contra ne
      have := card_two_out AY hy ht0 ny t0A ne
      omega
    have cA : A.card + 1 ≤ r := by
      have := card_lt_card ((ssubset_iff_of_subset AY).mpr ⟨t0, ht0, t0A⟩)
      omega
    have xa : ∀ a ∈ A, D x a = true := fun a ha => (mem_outN.mp ha).2
    have Arow : ∀ a ∈ A, ∀ w ∈ V, D a w = true → w ∈ A ∨ w ∈ Z := by
      intro a ha w wV aw
      rcases rowY a (AY ha) w wV aw with h | h | h
      · rw [uniq a (AY ha) w h aw] at aw
        exact (digonfree free (by omega) (hX hx) (hY (AY ha)) (xa a ha) aw).elim
      · by_cases wA : w ∈ A
        · exact Or.inl wA
        · rw [YA w h wA] at aw
          exact (free x 3 (by omega) (by omega) (.step (hY (AY ha)) (xa a ha)
            (.step (hY ht0) aw (.step (hX hx) t0x (.refl x))))).elim
      · exact Or.inr h
    have fA : QFree D A q := fY.mono_set AY
    have cAq : A.card ≤ q := by omega
    have Asink : ∀ s ∈ A, IsSink D A s → ∀ z ∈ Z, D s z = true := by
      intro s hs sink
      refine full_of_sub (V := V) ?_ third.le (deg s (hY (AY hs)))
      intro w hw
      obtain ⟨wV, sw⟩ := mem_outN.mp hw
      rcases Arow s hs w wV sw with h | h
      · exact (sink w h sw).elim
      · exact h
    have Ane : A.Nonempty := card_pos.mp (by omega)
    obtain ⟨s0, hs0, s0sink⟩ := exists_sink fA Ane cAq
    -- rows of `Z` stay in `Z ∪ W`
    have zrow : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ Z ∨ w ∈ W := by
      intro z hz w wV zw
      have s0z := Asink s0 hs0 s0sink z hz
      rcases rowZ z hz w wV zw with h | h | h | h
      · -- `w` is deep to radius `r - 3` in `X`
        have dw : Deep D X (r - 3) w := by
          intro s hs sink
          obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
          exact free w (j + 3) (by omega) (by omega)
            ((((wj.mono hX).snoc (hY (AY hs0)) (Xsink s (ball_subset hs) sink s0 (AY hs0))).snoc
              (hZ hz) s0z).snoc wV zw)
        have hw2 := deep_heads fX cX h dw
        have sub : outN D V w ⊆ outN D X w ∪ (insert t0 (outN D A w)) := by
          intro v hv
          obtain ⟨vV, wv⟩ := mem_outN.mp hv
          rcases rowX w h v vV wv with h' | h'
          · exact mem_union_left _ (mem_outN.mpr ⟨h', wv⟩)
          · by_cases vA : v ∈ A
            · exact mem_union_right _ (mem_insert_of_mem (mem_outN.mpr ⟨vA, wv⟩))
            · rw [YA v h' vA]; exact mem_union_right _ (mem_insert_self _ _)
        have c := (deg w wV).trans ((card_le_card sub).trans (card_union_le _ _))
        have c2 := card_insert_le t0 (outN D A w)
        obtain ⟨a, ha, b, hb, ab⟩ := one_lt_card.mp (show 1 < (outN D A w).card by omega)
        have deepA : ∀ a ∈ outN D A w, Deep D A (r - 3) a := by
          intro a ha s hs sink
          obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
          exact free w (j + 3) (by omega) (by omega)
            ((.step (hY (AY (mem_outN.mp ha).1)) (mem_outN.mp ha).2
              (((wj.mono (AY.trans hY)).snoc (hZ hz) (Asink s (ball_subset hs) sink z hz)).snoc wV zw)))
        exact (ab (two_deep fA cAq (by omega) (mem_outN.mp ha).1 (mem_outN.mp hb).1
          (deepA a ha) (deepA b hb))).elim
      · by_cases wA : w ∈ A
        · obtain ⟨s, hs, sink⟩ := sink_within (m := r - 2) fA cAq wA (by omega)
          obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
          exact (free w (j + 2) (by omega) (by omega)
            (((wj.mono (AY.trans hY)).snoc (hZ hz) (Asink s (ball_subset hs) sink z hz)).snoc wV zw)).elim
        · rw [YA w h wA] at zw
          exact (free x 4 (by omega) (by omega) (.step (hY (AY hs0)) (xa s0 hs0)
            (.step (hZ hz) s0z (.step (hY ht0) zw (.step (hX hx) t0x (.refl x)))))).elim
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨t, tZ, tsink⟩ := exists_sink fZ (card_pos.mp (by omega)) (by omega)
    refine too_few (V := V) (T := W) ?_ (by omega) (deg t (hZ tZ))
    intro w hw
    obtain ⟨wV, tw⟩ := mem_outN.mp hw
    rcases zrow t tZ w wV tw with h | h
    · exact (tsink w h tw).elim
    · exact h
  · -- no return from `Y` into `X`
    have noret : ∀ t ∈ Y, ∀ p ∈ X, ¬ D t p = true := fun t ht p hp tp => ret ⟨t, ht, p, hp, tp⟩
    have rowY' : ∀ y ∈ Y, ∀ w ∈ V, D y w = true → w ∈ Y ∨ w ∈ Z := by
      intro y hy w wV yw
      rcases rowY y hy w wV yw with h | h | h
      · exact (noret y hy w h yw).elim
      · exact Or.inl h
      · exact Or.inr h
    have Ysink : ∀ s ∈ Y, IsSink D Y s → ∀ z ∈ Z, D s z = true := by
      intro s hs sink
      refine full_of_sub (V := V) ?_ third.le (deg s (hY hs))
      intro w hw
      obtain ⟨wV, sw⟩ := mem_outN.mp hw
      rcases rowY' s hs w wV sw with h | h
      · exact (sink w h sw).elim
      · exact h
    obtain ⟨s0, hs0, s0sink⟩ := exists_sink fY (card_pos.mp (by omega)) cY
    have noZX : ∀ z ∈ Z, ∀ p ∈ X, ¬ D z p = true := by
      intro z hz p hp zp
      have s0z := Ysink s0 hs0 s0sink z hz
      have dp : Deep D X (r - 3) p := by
        intro s hs sink
        obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
        exact free p (j + 3) (by omega) (by omega)
          ((((wj.mono hX).snoc (hY hs0) (Xsink s (ball_subset hs) sink s0 hs0)).snoc
            (hZ hz) s0z).snoc (hX hp) zp)
      have hp2 := deep_heads fX cX hp dp
      have sub : outN D V p ⊆ outN D X p ∪ outN D Y p := by
        intro v hv
        obtain ⟨vV, pv⟩ := mem_outN.mp hv
        rcases rowX p hp v vV pv with h' | h'
        · exact mem_union_left _ (mem_outN.mpr ⟨h', pv⟩)
        · exact mem_union_right _ (mem_outN.mpr ⟨h', pv⟩)
      have c := (deg p (hX hp)).trans ((card_le_card sub).trans (card_union_le _ _))
      obtain ⟨a, ha, b, hb, c', hc', ab, ac, bc⟩ :=
        two_lt_card.mp (show 2 < (outN D Y p).card by omega)
      have deepY : ∀ a ∈ outN D Y p, Deep D Y (r - 3) a := by
        intro a ha s hs sink
        obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
        exact free p (j + 3) (by omega) (by omega)
          ((.step (hY (mem_outN.mp ha).1) (mem_outN.mp ha).2
            (((wj.mono hY).snoc (hZ hz) (Ysink s (ball_subset hs) sink z hz)).snoc (hX hp) zp)))
      exact three_deep fY cY (by omega) (mem_outN.mp ha).1 (mem_outN.mp hb).1 (mem_outN.mp hc').1
        ab ac bc (deepY a ha) (deepY b hb) (deepY c' hc')
    have ZYdeep : ∀ z ∈ Z, ∀ y ∈ Y, D z y = true → Deep D Y (r - 2) y := by
      intro z hz y hy zy s hs sink
      obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
      exact free y (j + 2) (by omega) (by omega)
        (((wj.mono hY).snoc (hZ hz) (Ysink s (ball_subset hs) sink z hz)).snoc (hY hy) zy)
    by_cases zy : ∃ z ∈ Z, ∃ y ∈ Y, D z y = true
    · obtain ⟨z0, hz0, y0, hy0, z0y0⟩ := zy
      have dy0 := ZYdeep z0 hz0 y0 hy0 z0y0
      have h1 := deep_heads fY cY hy0 dy0
      set B := outN D Z y0 with hBdef
      have BZ : B ⊆ Z := outN_subset
      have hB : r ≤ (outN D Y y0).card + B.card := by
        have sub : outN D V y0 ⊆ outN D Y y0 ∪ B := by
          intro w hw
          obtain ⟨wV, yw⟩ := mem_outN.mp hw
          rcases rowY' y0 hy0 w wV yw with h | h
          · exact mem_union_left _ (mem_outN.mpr ⟨h, yw⟩)
          · exact mem_union_right _ (mem_outN.mpr ⟨h, yw⟩)
        exact (deg y0 (hY hy0)).trans ((card_le_card sub).trans (card_union_le _ _))
      have z0B : z0 ∉ B := fun h =>
        digonfree free (by omega) (hY hy0) (hZ hz0) (mem_outN.mp h).2 z0y0
      have ZB : ∀ z ∈ Z, z ∉ B → z = z0 := by
        intro z hz nz
        by_contra ne
        have := card_two_out BZ hz hz0 nz z0B ne
        omega
      have yb : ∀ b ∈ B, D y0 b = true := fun b hb => (mem_outN.mp hb).2
      have Brow : ∀ b ∈ B, ∀ w ∈ V, D b w = true → w ∈ B ∨ w ∈ W := by
        intro b hb w wV bw
        rcases rowZ b (BZ hb) w wV bw with h | h | h | h
        · exact (noZX b (BZ hb) w h bw).elim
        · have e := two_deep fY cY (by omega) h hy0 (ZYdeep b (BZ hb) w h bw) dy0
          rw [e] at bw
          exact (digonfree free (by omega) (hY hy0) (hZ (BZ hb)) (yb b hb) bw).elim
        · by_cases wB : w ∈ B
          · exact Or.inl wB
          · rw [ZB w h wB] at bw
            exact (free y0 3 (by omega) (by omega) (.step (hZ (BZ hb)) (yb b hb)
              (.step (hZ hz0) bw (.step (hY hy0) z0y0 (.refl y0))))).elim
        · exact Or.inr h
      obtain ⟨t, tB, tsink⟩ := exists_sink (fZ.mono_set BZ) (card_pos.mp (by omega))
        ((card_le_card BZ).trans (by omega))
      refine too_few (V := V) (T := W) ?_ (by omega) (deg t (hZ (BZ tB)))
      intro w hw
      obtain ⟨wV, tw⟩ := mem_outN.mp hw
      rcases Brow t tB w wV tw with h | h
      · exact (tsink w h tw).elim
      · exact h
    · obtain ⟨t, tZ, tsink⟩ := exists_sink fZ (card_pos.mp (by omega)) (by omega)
      refine too_few (V := V) (T := W) ?_ (by omega) (deg t (hZ tZ))
      intro w hw
      obtain ⟨wV, tw⟩ := mem_outN.mp hw
      rcases rowZ t tZ w wV tw with h | h | h | h
      · exact (noZX t tZ w h tw).elim
      · exact (zy ⟨t, tZ, w, h, tw⟩).elim
      · exact (tsink w h tw).elim
      · exact h


/-! ### The loop dip -/

/-- **Loop layer, dip, recovery at the cutoff.** A root with exactly `r` heads, exactly `r + 1`
labels in its second layer and exactly `r - 1` in its third, in a `q`-free digraph of minimum
out-degree at least `r`, `8 ≤ r ≤ q`, has at least `r` labels in its fourth layer. -/
theorem loop_dip_recover {V : Finset ℕ} {q r u : ℕ} (free : QFree D V q)
    (hr : 8 ≤ r) (rq : r ≤ q) (hu : u ∈ V) (heads : (outN D V u).card = r)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (second : (layer D V 2 u).card = r + 1)
    (third : (layer D V 3 u).card + 1 = r) : r ≤ (layer D V 4 u).card := by
  classical
  by_contra! thin
  set X := outN D V u with hXdef
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set W := layer D V 4 u with hWdef
  have hX : X ⊆ V := outN_subset
  have hY : Y ⊆ V := fun w hw => ball_subset (layer_in hw)
  have hZ : Z ⊆ V := fun w hw => ball_subset (layer_in hw)
  have fX : QFree D X q := free.mono_set hX
  have fY : QFree D Y q := free.mono_set hY
  have fZ : QFree D Z q := free.mono_set hZ
  have cX : X.card ≤ q := by omega
  -- rows
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
  -- the labels of `Y` missed by a label of `X`
  set Om : ℕ → Finset ℕ := fun p => Y.filter (fun a => ¬ D p a = true) with hOm
  have omCard : ∀ p ∈ X, (Om p).card + r ≤ r + 1 + (outN D X p).card := by
    intro p hp
    have e : (outN D Y p).card + (Om p).card = Y.card :=
      card_filter_add_card_filter_not (s := Y) (fun a => D p a = true)
    have sub : outN D V p ⊆ outN D X p ∪ outN D Y p := by
      intro v hv
      obtain ⟨vV, pv⟩ := mem_outN.mp hv
      rcases rowX p hp v vV pv with h' | h'
      · exact mem_union_left _ (mem_outN.mpr ⟨h', pv⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h', pv⟩)
    have c := (deg p (hX hp)).trans ((card_le_card sub).trans (card_union_le _ _))
    omega
  have miss1 : ∀ s ∈ X, IsSink D X s → ∀ a ∈ Y, ∀ b ∈ Y, ¬ D s a = true → ¬ D s b = true →
      a = b := by
    intro s hs sink a ha b hb na nb
    by_contra ne
    have sub : outN D V s ⊆ Y := by
      intro w hw
      obtain ⟨wV, sw⟩ := mem_outN.mp hw
      rcases rowX s hs w wV sw with h | h
      · exact (sink w h sw).elim
      · exact h
    have := card_two_out sub ha hb (fun h => na (mem_outN.mp h).2) (fun h => nb (mem_outN.mp h).2) ne
    have := deg s (hX hs)
    omega
  have omSink : ∀ s ∈ X, IsSink D X s → (Om s).card ≤ 1 := by
    intro s hs sink
    refine card_le_one.mpr (fun a ha b hb => ?_)
    obtain ⟨aY, na⟩ := mem_filter.mp ha
    obtain ⟨bY, nb⟩ := mem_filter.mp hb
    exact miss1 s hs sink a aY b bY na nb
  have omDeep : ∀ p ∈ X, Deep D X (r - 3) p → (Om p).card ≤ 3 := by
    intro p hp dp
    have := deep_heads fX cX hp dp
    have := omCard p hp
    omega
  -- the ancestors of a return tail are missed
  set Anc : ℕ → Finset ℕ := fun t => Y.filter (fun a => ∃ n, Walk D Y a t n) with hAnc
  have retL : ∀ t ∈ Y, ∀ p ∈ X, D t p = true →
      (∃ s ∈ X, IsSink D X s ∧ Anc t ⊆ Om s) ∨ (Deep D X (r - 3) p ∧ Anc t ⊆ Om p) := by
    intro t ht p hp tp
    by_cases dp : Deep D X (r - 3) p
    · refine Or.inr ⟨dp, fun y hy => ?_⟩
      obtain ⟨yY, n, wn⟩ := mem_filter.mp hy
      refine mem_filter.mpr ⟨yY, fun py => ?_⟩
      have RO : ball (rev D) Y t (r - 2) ⊆ Om p := by
        intro a ha
        obtain ⟨aY, j, hj, wj⟩ := mem_ball.mp ha
        have w' : Walk D Y a t j := walk_rev ht wj
        exact mem_filter.mpr ⟨aY, fun pa => free p (j + 2) (by omega) (by omega)
          (.step (hY aY) pa ((w'.mono hY).snoc (hX hp) tp))⟩
      have yR : y ∈ ball (rev D) Y t n := mem_ball.mpr ⟨yY, n, le_rfl, walk_rev yY wn⟩
      have h3 := omDeep p hp dp
      rcases reach_or_grow (D := rev D) (M := r - 2) ht yR with h | h
      · exact (mem_filter.mp (RO h)).2 py
      · have := card_le_card RO
        omega
    · left
      obtain ⟨s, hs, sink⟩ : ∃ s ∈ ball D X p (r - 3), IsSink D X s := by
        by_contra h
        exact dp (fun s hs sk => h ⟨s, hs, sk⟩)
      obtain ⟨-, j, hj, wj⟩ := mem_ball.mp hs
      have sX := ball_subset hs
      have st : ¬ D s t = true := fun st =>
        free p (j + 2) (by omega) (by omega) (((wj.mono hX).snoc (hY ht) st).snoc (hX hp) tp)
      refine ⟨s, sX, sink, fun y hy => ?_⟩
      obtain ⟨yY, n, wn⟩ := mem_filter.mp hy
      cases n with
      | zero =>
        rw [walk_zero wn]
        exact mem_filter.mpr ⟨ht, st⟩
      | succ n =>
        obtain ⟨y', wy', -, y't⟩ := wn.unsnoc
        have y'Y : y' ∈ Y := by
          rcases wy'.end_mem_or with h | h
          · rw [h]; exact yY
          · exact h
        have sy' : ¬ D s y' = true := fun sy => free p (j + 3) (by omega) (by omega)
          ((((wj.mono hX).snoc (hY y'Y) sy).snoc (hY ht) y't).snoc (hX hp) tp)
        have e : y' = t := miss1 s sX sink y' y'Y t ht sy' st
        rw [e] at y't
        exact (loopfree free (by omega) (hY ht) y't).elim
  by_cases hasSink : ∃ t ∈ Y, IsSink D Y t
  · -- every label of `Y` reaches a sink of `D[Y]`, and the sinks return
    obtain ⟨t0, ht0, t0s⟩ := hasSink
    have reach : ∀ y ∈ Y, ∃ t ∈ Y, IsSink D Y t ∧ y ∈ Anc t := by
      intro y hy
      rcases closed_or_grow (D := D) (S := Y) (v := y) (a := 0) (M := r + 1) with ⟨j, -, -, cl⟩ | g
      · by_cases sm : (ball D Y y j).card ≤ q
        · obtain ⟨s, hs, sk⟩ := closed_sink fY hy sm cl
          obtain ⟨sY, i, -, wi⟩ := mem_ball.mp hs
          exact ⟨s, sY, sk, mem_filter.mpr ⟨hy, i, wi⟩⟩
        · have full : ball D Y y j = Y := eq_of_subset_of_card_le ball_subset (by omega)
          have t0b : t0 ∈ ball D Y y j := by rw [full]; exact ht0
          obtain ⟨-, i, -, wi⟩ := mem_ball.mp t0b
          exact ⟨t0, ht0, t0s, mem_filter.mpr ⟨hy, i, wi⟩⟩
      · have one : 1 ≤ (ball D Y y 0).card := card_pos.mpr ⟨y, self_mem_ball hy⟩
        have cap : (ball D Y y (0 + (r + 1))).card ≤ Y.card := ball_card_le
        omega
    have ret : ∀ t ∈ Y, IsSink D Y t → ∃ p ∈ X, D t p = true := by
      intro t ht sink
      by_contra none
      refine too_few (V := V) (T := Z) ?_ (by omega) (deg t (hY ht))
      intro w hw
      obtain ⟨wV, tw⟩ := mem_outN.mp hw
      rcases rowY t ht w wV tw with h | h | h
      · exact (none ⟨w, h, tw⟩).elim
      · exact (sink w h tw).elim
      · exact h
    set sX := X.filter (fun s => IsSink D X s) with hsX
    set dX := X.filter (fun p => Deep D X (r - 3) p) with hdX
    have cover : Y ⊆ sX.biUnion Om ∪ dX.biUnion Om := by
      intro y hy
      obtain ⟨t, tY, tsk, yA⟩ := reach y hy
      obtain ⟨p, hp, tp⟩ := ret t tY tsk
      rcases retL t tY p hp tp with ⟨s, sX', sk, sub⟩ | ⟨dp, sub⟩
      · exact mem_union_left _ (mem_biUnion.mpr ⟨s, mem_filter.mpr ⟨sX', sk⟩, sub yA⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨hp, dp⟩, sub yA⟩)
    have c1 : (sX.biUnion Om).card ≤ sX.card * 1 :=
      card_biUnion_le_card_mul _ _ _ (fun s hs => omSink s (mem_filter.mp hs).1 (mem_filter.mp hs).2)
    have c2 : (dX.biUnion Om).card ≤ dX.card * 3 :=
      card_biUnion_le_card_mul _ _ _ (fun p hp => omDeep p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
    have total := (card_le_card cover).trans (card_union_le _ _)
    by_cases dne : dX.Nonempty
    · obtain ⟨p0, hp0⟩ := dne
      obtain ⟨p0X, dp0⟩ := mem_filter.mp hp0
      have sub : sX ⊆ X \ ball D X p0 (r - 3) := by
        intro s hs
        obtain ⟨sX', sk⟩ := mem_filter.mp hs
        exact mem_sdiff.mpr ⟨sX', fun h => dp0 s h sk⟩
      have g := deep_grow fX cX p0X dp0 (k := r - 3) (by omega)
      have cs : sX.card ≤ 2 := by
        have := card_le_card sub
        rw [card_sdiff_of_subset ball_subset] at this
        omega
      have cd : dX.card ≤ 2 := by
        by_contra! h
        obtain ⟨a, ha, b, hb, c, hc, ab, ac, bc⟩ := two_lt_card.mp h
        exact three_deep fX cX (by omega) (mem_filter.mp ha).1 (mem_filter.mp hb).1
          (mem_filter.mp hc).1 ab ac bc (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2
      omega
    · have e : dX = ∅ := not_nonempty_iff_eq_empty.mp dne
      have e0 : dX.card = 0 := by rw [e, card_empty]
      have : sX.card ≤ X.card := card_le_card (filter_subset _ _)
      omega
  · -- no sink in `D[Y]`: no return, and `Y` is a chordless cycle complete to `Z`
    have noSink : ∀ t ∈ Y, ¬ IsSink D Y t := fun t ht sk => hasSink ⟨t, ht, sk⟩
    have cY1 : Y.card ≤ q + 1 := by omega
    have noret : ∀ t ∈ Y, ∀ p ∈ X, ¬ D t p = true := by
      intro t ht p hp tp
      have tA : t ∈ Anc t := mem_filter.mpr ⟨ht, 0, .refl t⟩
      have pc : ∀ a ∈ Y, ∀ b ∈ Anc t, D a b = true → a ∈ Anc t := by
        intro a aY b hb ab
        obtain ⟨bY, n, wn⟩ := mem_filter.mp hb
        exact mem_filter.mpr ⟨aY, n + 1, .step bY ab wn⟩
      have small : (Anc t).card ≤ 3 := by
        rcases retL t ht p hp tp with ⟨s, sX', sk, sub⟩ | ⟨dp, sub⟩
        · exact (card_le_card sub).trans ((omSink s sX' sk).trans (by omega))
        · exact (card_le_card sub).trans (omDeep p hp dp)
      obtain ⟨y0, y0Y, y0n⟩ := exists_mem_notMem_of_card_lt_card (s := Anc t) (t := Y) (by omega)
      obtain ⟨s, sY, sk⟩ := pclosed_sink fY cY1 (filter_subset _ _) tA y0Y y0n pc
      exact noSink s sY sk
    have parent : ∀ y ∈ Y, ∃ a ∈ Y, D a y = true := by
      intro y hy
      by_contra none
      obtain ⟨y0, y0Y, y0n⟩ := exists_mem_notMem_of_card_lt_card (s := {y}) (t := Y)
        (by rw [card_singleton]; omega)
      have pc : ∀ a ∈ Y, ∀ b ∈ ({y} : Finset ℕ), D a b = true → a ∈ ({y} : Finset ℕ) := by
        intro a aY b hb ab
        rw [mem_singleton.mp hb] at ab
        exact (none ⟨a, aY, ab⟩).elim
      obtain ⟨s, sY, sk⟩ := pclosed_sink fY cY1 (singleton_subset_iff.mpr hy) (mem_singleton_self y)
        y0Y y0n pc
      exact noSink s sY sk
    have oneHead : ∀ y ∈ Y, (outN D Y y).card ≤ 1 := by
      intro y hy
      by_contra! two
      obtain ⟨y', y'Y, y'y⟩ := parent y hy
      have reachAll : y' ∈ ball D Y y (r - 1) := by
        rcases closed_or_grow (D := D) (S := Y) (v := y) (a := 1) (M := r - 2) with ⟨j, -, hj, cl⟩ | g
        · by_cases sm : (ball D Y y j).card ≤ q
          · obtain ⟨s, hs, sk⟩ := closed_sink fY hy sm cl
            exact (noSink s (ball_subset hs) sk).elim
          · have full : ball D Y y j = Y := eq_of_subset_of_card_le ball_subset (by omega)
            have yj : y' ∈ ball D Y y j := by rw [full]; exact y'Y
            exact ball_mono_radius (by omega) yj
        · have pp := loopfree free (by omega) (hY hy)
          have sub : insert y (outN D Y y) ⊆ ball D Y y 1 := by
            intro w hw
            rcases mem_insert.mp hw with rfl | hw
            · exact self_mem_ball hy
            · exact (mem_ball_one hy).mpr (Or.inr hw)
          have notin : y ∉ outN D Y y := fun h => pp (mem_outN.mp h).2
          have c1 := card_le_card sub
          rw [card_insert_of_notMem notin] at c1
          rw [show 1 + (r - 2) = r - 1 by omega] at g
          have full : ball D Y y (r - 1) = Y := eq_of_subset_of_card_le ball_subset (by omega)
          rw [full]; exact y'Y
      obtain ⟨-, i, hi, wi⟩ := mem_ball.mp reachAll
      exact free y (i + 1) (by omega) (by omega) ((wi.mono hY).snoc (hY hy) y'y)
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
      have h1 := oneHead y hy
      have eq : outN D Z y = Z := eq_of_subset_of_card_le outN_subset (by omega)
      intro z hz
      rw [← eq] at hz
      exact (mem_outN.mp hz).2
    have pY : ∀ p ∈ X, ∃ y ∈ Y, D p y = true := by
      intro p hp
      by_contra none
      have pp := loopfree free (by omega) (hX hp)
      refine too_few (V := V) (T := X.erase p) ?_ (by rw [card_erase_of_mem hp]; omega) (deg p (hX hp))
      intro w hw
      obtain ⟨wV, pw⟩ := mem_outN.mp hw
      rcases rowX p hp w wV pw with h | h
      · exact mem_erase.mpr ⟨fun e => pp (e ▸ pw), h⟩
      · exact (none ⟨w, h, pw⟩).elim
    have zrow : ∀ z ∈ Z, ∀ w ∈ V, D z w = true → w ∈ Z ∨ w ∈ W := by
      intro z hz w wV zw
      rcases rowZ z hz w wV zw with h | h | h | h
      · obtain ⟨y, yY, wy⟩ := pY w h
        exact (free w 3 (by omega) (by omega) (.step (hY yY) wy
          (.step (hZ hz) (fullZ y yY z hz) (.step wV zw (.refl w))))).elim
      · exact (digonfree free (by omega) (hY h) (hZ hz) (fullZ w h z hz) zw).elim
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨t, tZ, tsink⟩ := exists_sink fZ (card_pos.mp (by omega)) (by omega)
    refine too_few (V := V) (T := W) ?_ (by omega) (deg t (hZ tZ))
    intro w hw
    obtain ⟨wV, tw⟩ := mem_outN.mp hw
    rcases zrow t tZ w wV tw with h | h
    · exact (tsink w h tw).elim
    · exact h

/-! ### The patterns -/

/-- A flat run of three: `r ≤ q`, `5 ≤ r`, second and third layers exactly `r`, fourth at most
`r - 1`. -/
def flatRunQ (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (r ≤ q ∧ 5 ≤ r ∧ 3 ≤ ws.length ∧ ws.getD 1 0 = r ∧ ws.getD 2 0 = r ∧
    (if 4 ≤ ws.length then ws.getD 3 0 else last) + 1 ≤ r)

theorem flatRunQ_sound (q r : ℕ) : ShapeClimbX.SoundX q r (flatRunQ q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨rq, hr, len, w2, w3, w4⟩ := of_decide_eq_true h
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := flat_fourth free hr rq hu root deg (by omega) (by omega)
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    have e : ws.length + 1 = 4 := by omega
    rw [e] at bound
    omega

/-- Loop layer, dip, recovery: `r ≤ q`, `8 ≤ r`, second layer exactly `r + 1`, third exactly
`r - 1`, fourth at most `r - 1`. -/
def loopDipQ (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (r ≤ q ∧ 8 ≤ r ∧ 3 ≤ ws.length ∧ ws.getD 1 0 = r + 1 ∧ ws.getD 2 0 + 1 = r ∧
    (if 4 ≤ ws.length then ws.getD 3 0 else last) + 1 ≤ r)

theorem loopDipQ_sound (q r : ℕ) : ShapeClimbX.SoundX q r (loopDipQ q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨rq, hr, len, w2, w3, w4⟩ := of_decide_eq_true h
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := loop_dip_recover free hr rq hu root deg (by omega) (by omega)
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    have e : ws.length + 1 = 4 := by omega
    rw [e] at bound
    omega

/-- The Boolean `||` of two sound patterns is sound. -/
theorem soundX_or {q r : ℕ} {X₁ X₂ : List ℕ → ℕ → Bool} (h₁ : ShapeClimbX.SoundX q r X₁)
    (h₂ : ShapeClimbX.SoundX q r X₂) :
    ShapeClimbX.SoundX q r (fun ws last => X₁ ws last || X₂ ws last) := by
  intro D V u ws last free deg hu root exact bound h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact h₁ D V u ws last free deg hu root exact bound h
  · exact h₂ D V u ws last free deg hu root exact bound h

/-- The flat dip, the flat run of three and the loop dip. -/
def tubeQ (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  FlatAtCutoff.flatQ q r ws last || flatRunQ q r ws last || loopDipQ q r ws last

theorem tubeQ_sound (q r : ℕ) : ShapeClimbX.SoundX q r (tubeQ q r) :=
  soundX_or (soundX_or (FlatAtCutoff.flatQ_sound q r) (flatRunQ_sound q r)) (loopDipQ_sound q r)

#print axioms flat_fourth
#print axioms loop_dip_recover
#print axioms flatRunQ_sound
#print axioms loopDipQ_sound
#print axioms tubeQ_sound
end LeanCH.BR.TubeAtCutoff
