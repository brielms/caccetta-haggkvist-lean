import checkpoints.shen_extension.ThirtySixClose

/-!
# Equal strict layers; the high-class count

Generic in `D`, `V`, the cutoff `q`, the layer `j`, the radius `k`, the degree `r` and the
counts `c`, `d`, `p`. No rule, no wiring.

## D1: equal strict layers

`QFree D V q`, `u ≠ v`, `1 ≤ j`, `layer j u = layer j v`, and `v ∈ ball u q`:

* `equal_layer_near`: `v ∈ ball u (j - 1)`. Otherwise the walk from `u` to `v` crosses
  `layer j u = layer j v` at some `z` (`through_layer`), and `v → z → v` is a closed walk of
  length at most `q`.
* `equal_layer_ball` (`2j ≤ q + 2`): `ball v (j - 1) ⊆ (ball u (j - 1)).erase u`. A walk of
  length `≤ j - 1` from `v` starts in `ball u (j - 1)` and could only leave it through
  `layer j u = layer j v`; it cannot reach `u` (a closed walk of length `≤ 2j - 2`).
* `equal_layer_far`, `equal_layer_gap`: equal layer `j` and equal `(j - 1)`-balls give
  `v ∉ ball u q`, so the pair is a `ReachLedger.gap` at all radii `≤ q`.
* `equal_layer_pair`: two distinct `v`, `v'` with the layer `j` of `u`, both within `q` of `u`,
  both with `(j - 1)`-ball one smaller than that of `u`, are impossible.

## D2: the high-class count (`high_class`)

`QFree D V q`, `2k ≤ q`, out-degree `r` everywhere, `H ⊆ V`, `T = V \ H`, `S a = seen D V H k a`
(the rows of `H` other than `a` within `k` steps). Hypotheses: `c ≤ |S a|` on `H`; for `u ∈ T` a
set `P u ⊆ H` with `c ≤ |P u|`, and `P u ⊆ ball a k`, `a ∉ P u` whenever `a ∈ H` heads `u`;
in-degree `≤ d` on `H`; every row of `T` has `≥ p` heads in `H`. Then
(1) `2 ∑ |S a| + ∑ |blind a| = h (h - 1)` and `2c + 1 ≤ h` when `H` is nonempty;
(2) there is `L ⊆ H` with `|S a| = c` on `L`, `S` injective on `L`, and
`2 (c + 1) h ≤ 2 |L| + h (h - 1)` (rows with equal `S` are blind to each other);
(3) every row of `T` heads at most one row of `L`; (4) `r |L| + p |T| ≤ |T| + d h`.

`no36_regular'`: `ThirtySixClose.no36_regular` again, from `high_class` at `c = p = 8`, `d = 11`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.EqualLayers
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open HostTwo (inN)
open ThirtySixClose (seen blind mutual_eq pair_count heads_seen out_seen)

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### D1: equal strict layers -/

/-- A label at distance `> j - 1` and `≤ m + j` from `u` is within `m` of a label of layer `j`. -/
theorem through_layer {u j : ℕ} (hu : u ∈ V) (hj : 1 ≤ j) :
    ∀ m, ∀ w ∈ ball D V u (m + j), w ∉ ball D V u (j - 1) →
      ∃ z ∈ layer D V j u, w ∈ ball D V z m := by
  intro m
  induction m with
  | zero =>
    intro w hw out
    rw [Nat.zero_add] at hw
    exact ⟨w, mem_layer.mpr ⟨hw, out⟩, self_mem_ball (ball_subset hw)⟩
  | succ m ih =>
    intro w hw out
    have wV : w ∈ V := ball_subset hw
    by_cases old : w ∈ ball D V u (m + j)
    · obtain ⟨z, hz, wz⟩ := ih w old out
      exact ⟨z, hz, ball_mono_radius (Nat.le_succ m) wz⟩
    · have hw' : w ∈ ball D V u ((m + j) + 1) := by
        rwa [show m + j + 1 = m + 1 + j by omega]
      obtain ⟨p, pb, pw⟩ := ball_succ_pred hu hw' old
      by_cases p1 : p ∈ ball D V u (j - 1)
      · have wj : w ∈ ball D V u j := by
          have := ball_step p1 wV pw
          rwa [show j - 1 + 1 = j by omega] at this
        exact ⟨w, mem_layer.mpr ⟨wj, out⟩, ball_mono_radius (Nat.zero_le _) (self_mem_ball wV)⟩
      · obtain ⟨z, hz, pz⟩ := ih p pb p1
        exact ⟨z, hz, ball_step pz wV pw⟩

/-- **(i)** Equal layer `j` and `v` within `q` of `u`: `v ∈ ball u (j - 1)`. -/
theorem equal_layer_near (free : QFree D V q) {u v j : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (hj : 1 ≤ j) (same : layer D V j u = layer D V j v) (reach : v ∈ ball D V u q) :
    v ∈ ball D V u (j - 1) := by
  by_contra far
  by_cases jq : j ≤ q
  · have h' : v ∈ ball D V u ((q - j) + j) := by rwa [show q - j + j = q by omega]
    obtain ⟨z, hz, vz⟩ := through_layer hu hj (q - j) v h' far
    rw [same] at hz
    obtain ⟨zb, zn⟩ := mem_layer.mp hz
    obtain ⟨-, a, ha, wa⟩ := mem_ball.mp zb
    obtain ⟨-, b, hb, wb⟩ := mem_ball.mp vz
    rcases Nat.eq_zero_or_pos a with rfl | apos
    · have e := FlatAtCutoff.walk_zero wa
      subst e
      exact zn (self_mem_ball hv)
    · exact free v (a + b) (by omega) (by omega) (wa.append wb)
  · exact far (ball_mono_radius (by omega) reach)

/-- **(ii)** Equal layer `j`, `2j ≤ q + 2`, `v` within `q` of `u`:
`ball v (j - 1) ⊆ (ball u (j - 1)).erase u`. -/
theorem equal_layer_ball (free : QFree D V q) {u v j : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (ne : u ≠ v) (hj : 1 ≤ j) (hjq : 2 * j ≤ q + 2) (same : layer D V j u = layer D V j v)
    (reach : v ∈ ball D V u q) : ball D V v (j - 1) ⊆ (ball D V u (j - 1)).erase u := by
  have near := equal_layer_near free hu hv hj same reach
  have inside : ∀ i, i ≤ j - 1 → ∀ y ∈ ball D V v i, y ∈ ball D V u (j - 1) := by
    intro i
    induction i with
    | zero =>
      intro _ y hy
      rw [ShapeClimbRoot.ball_zero_eq hv] at hy
      rw [mem_singleton.mp hy]
      exact near
    | succ i ih =>
      intro hi y hy
      by_cases old : y ∈ ball D V v i
      · exact ih (by omega) y old
      · obtain ⟨p, pb, py⟩ := ball_succ_pred hv hy old
        have pu := ih (by omega) p pb
        by_contra out
        have yj : y ∈ ball D V u j := by
          have := ball_step pu (ball_subset hy) py
          rwa [show j - 1 + 1 = j by omega] at this
        have yl : y ∈ layer D V j v := by
          rw [← same]
          exact mem_layer.mpr ⟨yj, out⟩
        exact (mem_layer.mp yl).2 (ball_mono_radius hi hy)
  intro y hy
  refine mem_erase.mpr ⟨fun e => ?_, inside (j - 1) le_rfl y hy⟩
  rw [e] at hy
  exact ne (mutual_eq (k := j - 1) free (by omega) hv hy near)

/-- **(a)** Equal layer `j` and equal `(j - 1)`-balls: `v` is not within `q` of `u`. -/
theorem equal_layer_far (free : QFree D V q) {u v j : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (ne : u ≠ v) (hj : 1 ≤ j) (hjq : 2 * j ≤ q + 2) (same : layer D V j u = layer D V j v)
    (cards : (ball D V u (j - 1)).card = (ball D V v (j - 1)).card) : v ∉ ball D V u q := by
  intro reach
  have sub := card_le_card (equal_layer_ball free hu hv ne hj hjq same reach)
  rw [card_erase_of_mem (self_mem_ball hu)] at sub
  have : 0 < (ball D V u (j - 1)).card := card_pos.mpr ⟨u, self_mem_ball hu⟩
  omega

/-- **(a)** as a gap: the pair is a `ReachLedger.gap` at all radii `i, i' ≤ q`. -/
theorem equal_layer_gap (free : QFree D V q) {u v j : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (ne : u ≠ v) (hj : 1 ≤ j) (hjq : 2 * j ≤ q + 2) (same : layer D V j u = layer D V j v)
    (cards : (ball D V u (j - 1)).card = (ball D V v (j - 1)).card) {i i' : ℕ} (hi : i ≤ q)
    (hi' : i' ≤ q) : v ∈ ReachLedger.gap D V i i' u :=
  ReachLedger.mem_gap.mpr ⟨hv,
    fun h => equal_layer_far free hu hv ne hj hjq same cards (ball_mono_radius hi h),
    fun h => equal_layer_far free hv hu (Ne.symm ne) hj hjq same.symm cards.symm
      (ball_mono_radius hi' h)⟩

/-- **(b)** Two distinct labels with the layer `j` of `u`, within `q` of `u`, each with
`(j - 1)`-ball one smaller than that of `u`: impossible. -/
theorem equal_layer_pair (free : QFree D V q) {u v v' j : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (hv' : v' ∈ V) (nev : u ≠ v) (nev' : u ≠ v') (ne : v ≠ v') (hj : 1 ≤ j)
    (hjq : 2 * j ≤ q + 2) (same : layer D V j u = layer D V j v)
    (same' : layer D V j u = layer D V j v') (reach : v ∈ ball D V u q)
    (reach' : v' ∈ ball D V u q)
    (c : (ball D V v (j - 1)).card + 1 = (ball D V u (j - 1)).card)
    (c' : (ball D V v' (j - 1)).card + 1 = (ball D V u (j - 1)).card) : False := by
  have s := equal_layer_ball free hu hv nev hj hjq same reach
  have s' := equal_layer_ball free hu hv' nev' hj hjq same' reach'
  have e := eq_of_subset_of_card_le s (by rw [card_erase_of_mem (self_mem_ball hu)]; omega)
  have e' := eq_of_subset_of_card_le s' (by rw [card_erase_of_mem (self_mem_ball hu)]; omega)
  have m : v ∈ ball D V v' (j - 1) := by rw [e', ← e]; exact self_mem_ball hv
  have m' : v' ∈ ball D V v (j - 1) := by rw [e, ← e']; exact self_mem_ball hv'
  exact ne (mutual_eq (k := j - 1) free (by omega) hv' m m')

/-! ### D2: the high-class count -/

/-- `2 m ≤ m (m - 1) + 2` for every `m`. -/
theorem two_le (m : ℕ) : 2 * m ≤ m * (m - 1) + 2 := by
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m <;> simp
  · have : 2 * m ≤ m * (m - 1) := by
      calc 2 * m = m * 2 := by ring
        _ ≤ m * (m - 1) := Nat.mul_le_mul_left m (by omega)
    omega

theorem sq_split (m : ℕ) : m * m = m * (m - 1) + m := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [Nat.add_sub_cancel]
    ring

theorem three_le (m : ℕ) : 2 * m + m ≤ m * m + 2 := by
  have := two_le m
  have := sq_split m
  omega

/-- Rows of `L0` with equal seen sets are blind to each other, so the duplicates are paid by the
blind pairs: `2 (|L0| - #classes) ≤ ∑_{a ∈ L0} |blind a|`. -/
theorem duplicates_blind {H L0 : Finset ℕ} {k : ℕ} (L0H : L0 ⊆ H) :
    2 * L0.card ≤ 2 * (L0.image (seen D V H k)).card + ∑ a ∈ L0, (blind D V H k a).card := by
  classical
  set S := seen D V H k with hS
  set I := L0.image S with hI
  have maps : ∀ a ∈ L0, S a ∈ I := fun a ha => mem_image_of_mem S ha
  -- per row: the other rows of its class are blind to it
  have per : ∀ a ∈ L0, (L0.filter (fun b => S b = S a)).card ≤ (blind D V H k a).card + 1 := by
    intro a ha
    have sub : (L0.filter (fun b => S b = S a)).erase a ⊆ blind D V H k a := by
      intro b hb
      obtain ⟨ne, hb'⟩ := mem_erase.mp hb
      obtain ⟨bL, eq⟩ := mem_filter.mp hb'
      refine mem_filter.mpr ⟨L0H bL, ne, fun h => ?_, fun h => ?_⟩
      · have m : b ∈ S a := mem_filter.mpr ⟨L0H bL, ne, h⟩
        rw [← eq] at m
        exact (mem_filter.mp m).2.1 rfl
      · have m : a ∈ S b := mem_filter.mpr ⟨L0H ha, Ne.symm ne, h⟩
        rw [eq] at m
        exact (mem_filter.mp m).2.1 rfl
    have := card_le_card sub
    have := card_erase_of_mem (mem_filter.mpr ⟨ha, rfl⟩ : a ∈ L0.filter (fun b => S b = S a))
    omega
  -- sum over classes
  have fib : ∑ s ∈ I, ∑ a ∈ L0.filter (fun a => S a = s), (L0.filter (fun b => S b = S a)).card =
      ∑ a ∈ L0, (L0.filter (fun b => S b = S a)).card :=
    sum_fiberwise_of_maps_to maps _
  have inner : ∀ s ∈ I, ∑ a ∈ L0.filter (fun a => S a = s), (L0.filter (fun b => S b = S a)).card =
      (L0.filter (fun a => S a = s)).card * (L0.filter (fun a => S a = s)).card := by
    intro s _
    rw [sum_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2]), sum_const, smul_eq_mul]
  rw [sum_congr rfl inner] at fib
  have cnt : L0.card = ∑ s ∈ I, (L0.filter (fun a => S a = s)).card :=
    card_eq_sum_card_fiberwise maps
  have sq : ∀ s ∈ I, 2 * (L0.filter (fun a => S a = s)).card + (L0.filter (fun a => S a = s)).card ≤
      (L0.filter (fun a => S a = s)).card * (L0.filter (fun a => S a = s)).card + 2 :=
    fun s _ => three_le _
  have total := sum_le_sum sq
  simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum] at total
  rw [← cnt, fib] at total
  have perSum := sum_le_sum per
  rw [sum_add_distrib, sum_const, smul_eq_mul] at perSum
  omega

/-- A set of representatives: `L ⊆ L0` with `S` injective on `L` and `|L| = |S '' L0|`. -/
theorem representatives {L0 : Finset ℕ} (S : ℕ → Finset ℕ) :
    ∃ L ⊆ L0, Set.InjOn S L ∧ L.card = (L0.image S).card := by
  classical
  let g : Finset ℕ → ℕ := fun s => if h : ∃ a ∈ L0, S a = s then h.choose else 0
  have gspec : ∀ s ∈ L0.image S, g s ∈ L0 ∧ S (g s) = s := by
    intro s hs
    have h : ∃ a ∈ L0, S a = s := by simpa using hs
    simp only [g]
    split
    · next h' => exact h'.choose_spec
    · contradiction
  refine ⟨(L0.image S).image g, fun x hx => ?_, fun x hx y hy e => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
    exact (gspec s hs).1
  · obtain ⟨s, hs, rfl⟩ := mem_image.mp (mem_coe.mp hx)
    obtain ⟨t, ht, rfl⟩ := mem_image.mp (mem_coe.mp hy)
    rw [(gspec s hs).2, (gspec t ht).2] at e
    rw [e]
  · refine card_image_of_injOn (fun s hs t ht e => ?_)
    have := congrArg S e
    rwa [(gspec s hs).2, (gspec t ht).2] at this

/-- **The high-class count.** -/
theorem high_class (free : QFree D V q) {k r c d p : ℕ} (hk : 2 * k ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = r) {H : Finset ℕ} (HV : H ⊆ V) (P : ℕ → Finset ℕ)
    (low : ∀ a ∈ H, c ≤ (seen D V H k a).card)
    (PH : ∀ u ∈ V \ H, P u ⊆ H) (Pc : ∀ u ∈ V \ H, c ≤ (P u).card)
    (Pball : ∀ u ∈ V \ H, ∀ a ∈ H, D a u = true → P u ⊆ ball D V a k ∧ a ∉ P u)
    (indeg : ∀ v ∈ H, (inN D V v).card ≤ d)
    (heads : ∀ u ∈ V \ H, p ≤ (H.filter (fun v => D u v = true)).card) :
    2 * ∑ a ∈ H, (seen D V H k a).card + ∑ a ∈ H, (blind D V H k a).card =
        H.card * (H.card - 1) ∧
      (H.Nonempty → 2 * c + 1 ≤ H.card) ∧
      ∃ L ⊆ H, (∀ a ∈ L, (seen D V H k a).card = c) ∧ Set.InjOn (seen D V H k) L ∧
        2 * (H.card * (c + 1)) ≤ 2 * L.card + H.card * (H.card - 1) ∧
        (∀ u ∈ V \ H, (L.filter (fun a => D a u = true)).card ≤ 1) ∧
        L.card * r + (V \ H).card * p ≤ (V \ H).card + H.card * d := by
  classical
  set T := V \ H with hT
  set S := seen D V H k with hS
  have TV : T ⊆ V := sdiff_subset
  have pc : 2 * ∑ a ∈ H, (S a).card + ∑ a ∈ H, (blind D V H k a).card =
      H.card * (H.card - 1) := pair_count free hk HV
  have sumS : ∑ _a ∈ H, c ≤ ∑ a ∈ H, (S a).card := sum_le_sum low
  rw [sum_const, smul_eq_mul] at sumS
  refine ⟨pc, fun ne => ?_, ?_⟩
  · have hpos : 0 < H.card := card_pos.mpr ne
    have key : H.card * (2 * c) ≤ H.card * (H.card - 1) := by
      rw [show H.card * (2 * c) = 2 * (H.card * c) by ring]
      omega
    have := Nat.le_of_mul_le_mul_left key hpos
    omega
  -- the rows seeing exactly `c`, and representatives
  set L0 := H.filter (fun a => (S a).card = c) with hL0
  have L0H : L0 ⊆ H := filter_subset _ _
  have Lb : H.card * (c + 1) ≤ ∑ a ∈ H, (S a).card + L0.card := by
    have := sum_le_sum (s := H) (f := fun _ => c + 1)
      (g := fun a => (S a).card + if (S a).card = c then 1 else 0)
      (fun a aH => by have := low a aH; split_ifs <;> omega)
    rw [sum_const, smul_eq_mul, sum_add_distrib, ← card_filter] at this
    exact this
  have dup : 2 * L0.card ≤ 2 * (L0.image S).card + ∑ a ∈ L0, (blind D V H k a).card :=
    duplicates_blind (D := D) (V := V) (k := k) L0H
  have dupH : ∑ a ∈ L0, (blind D V H k a).card ≤ ∑ a ∈ H, (blind D V H k a).card :=
    sum_le_sum_of_subset L0H
  obtain ⟨L, LL0, inj, Lc⟩ := representatives (L0 := L0) S
  have LH : L ⊆ H := LL0.trans L0H
  have LS : ∀ a ∈ L, (S a).card = c := fun a aL => (mem_filter.mp (LL0 aL)).2
  -- (3) at most one parent in `L`
  have oneL : ∀ u ∈ T, (L.filter (fun a => D a u = true)).card ≤ 1 := by
    intro u uT
    refine card_le_one.mpr (fun a ha b hb => ?_)
    obtain ⟨aL, au⟩ := mem_filter.mp ha
    obtain ⟨bL, bu⟩ := mem_filter.mp hb
    have sub : ∀ x ∈ L, D x u = true → P u ⊆ S x := by
      intro x xL xu y hy
      obtain ⟨yb, xn⟩ := Pball u uT x (LH xL) xu
      exact mem_filter.mpr ⟨PH u uT hy, fun e => xn (e ▸ hy), yb hy⟩
    have ea := eq_of_subset_of_card_le (sub a aL au) (by rw [LS a aL]; exact Pc u uT)
    have eb := eq_of_subset_of_card_le (sub b bL bu) (by rw [LS b bL]; exact Pc u uT)
    exact inj (mem_coe.mpr aL) (mem_coe.mpr bL) (ea.symm.trans eb)
  refine ⟨L, LH, LS, inj, by omega, oneL, ?_⟩
  -- (4) the arc count
  have outSplit : ∀ a ∈ V, (T.filter (fun v => D a v = true)).card +
      (H.filter (fun v => D a v = true)).card = r := by
    intro a aV
    have split := card_filter_add_card_filter_not (s := outN D V a) (fun v => v ∈ T)
    have e1 : (outN D V a).filter (fun v => v ∈ T) = T.filter (fun v => D a v = true) := by
      ext v
      simp only [mem_filter, mem_outN]
      exact ⟨fun ⟨⟨_, x⟩, y⟩ => ⟨y, x⟩, fun ⟨y, x⟩ => ⟨⟨TV y, x⟩, y⟩⟩
    have e2 : (outN D V a).filter (fun v => v ∉ T) = H.filter (fun v => D a v = true) := by
      ext v
      simp only [mem_filter, mem_outN, hT, mem_sdiff]
      constructor
      · rintro ⟨⟨vV, x⟩, y⟩
        exact ⟨by by_contra h; exact y ⟨vV, h⟩, x⟩
      · rintro ⟨vH, x⟩
        exact ⟨⟨HV vH, x⟩, fun ⟨_, h⟩ => h vH⟩
    rw [e1, e2, reg a aV] at split
    exact split
  have outL : ∑ a ∈ L, (T.filter (fun v => D a v = true)).card +
      ∑ a ∈ L, (H.filter (fun v => D a v = true)).card = L.card * r := by
    rw [← sum_add_distrib, sum_congr rfl (fun a aL => outSplit a (HV (LH aL))), sum_const,
      smul_eq_mul]
  have LT : ∑ a ∈ L, (T.filter (fun v => D a v = true)).card ≤ T.card := by
    rw [HostTwo.arcs_between (D := D) L T]
    have := sum_le_sum oneL
    simpa using this
  have LHH : ∑ a ∈ L, (H.filter (fun v => D a v = true)).card ≤
      ∑ v ∈ H, (H.filter (fun u => D u v = true)).card := by
    rw [← HostTwo.arcs_between (D := D) H H]
    exact sum_le_sum_of_subset LH
  have TH : T.card * p ≤ ∑ v ∈ H, (T.filter (fun u => D u v = true)).card := by
    rw [← HostTwo.arcs_between (D := D) T H]
    have := sum_le_sum heads
    rw [sum_const, smul_eq_mul] at this
    exact this
  have inH : ∀ v ∈ H, (H.filter (fun u => D u v = true)).card +
      (T.filter (fun u => D u v = true)).card ≤ d := by
    intro v vH
    have disj : Disjoint (H.filter (fun u => D u v = true)) (T.filter (fun u => D u v = true)) :=
      disjoint_filter_filter (disjoint_sdiff : Disjoint H (V \ H))
    have sub : H.filter (fun u => D u v = true) ∪ T.filter (fun u => D u v = true) ⊆
        inN D V v := by
      intro u hu
      rcases mem_union.mp hu with hu | hu
      · exact mem_filter.mpr ⟨HV (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
      · exact mem_filter.mpr ⟨TV (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
    have c' := card_le_card sub
    rw [card_union_of_disjoint disj] at c'
    have := indeg v vH
    omega
  have sumIn := sum_le_sum inH
  rw [sum_add_distrib, sum_const, smul_eq_mul] at sumIn
  omega

/-! ### Order 36 again, from the high-class count -/

open DotTwoPassShellTransport (layer) in
/-- `ThirtySixClose.no36_regular`, re-derived from `high_class` at `k = 2`, `c = p = 8`,
`d = 11`. -/
theorem no36_regular' (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) : False := by
  classical
  have lawA : ThirtySix.LawA D V := fun u hu h => LawA.law_A_4_9 free reg hu h
  have eight := ThirtySix.no_seven free reg n lawA
  have b8 := ThirtySix.budget8 free reg n eight
  have high := ThirtySix.high_count free reg n lawA
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  set H := V \ T with hH
  have TV : T ⊆ V := filter_subset _ _
  have HV : H ⊆ V := sdiff_subset
  have Hc' : (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card = H.card := by
    rw [hH, hT, ThirtySix.high_eq]
  have VH : V \ H = T := by rw [hH, Finset.sdiff_sdiff_eq_self TV]
  have Tc : H.card + T.card = 36 := by
    have := card_sdiff_add_card_eq_card TV
    rw [← hH, n] at this
    exact this
  have sup : ∀ t ∈ T, 8 ≤ (H.filter (fun v => D t v = true)).card :=
    fun t ht => ThirtySix.supply free reg lawA (mem_filter.mp ht).1 (mem_filter.mp ht).2
  have S8 : ∀ a ∈ H, 8 ≤ (seen D V H 2 a).card := by
    intro a aH
    have aV := HV aH
    by_cases ex : ∃ t ∈ T, D a t = true
    · obtain ⟨t, tT, hat⟩ := ex
      exact (sup t tT).trans
        (card_le_card (heads_seen free (by norm_num) le_rfl HV aV (TV tT) hat))
    · have sub : outN D V a ⊆ H.filter (fun b => D a b = true) := by
        intro b hb
        obtain ⟨bV, ab⟩ := mem_outN.mp hb
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨bV, fun bT => ex ⟨b, bT, ab⟩⟩, ab⟩
      have := (card_le_card sub).trans
        (card_le_card (out_seen (k := 2) free (by norm_num) (by norm_num) HV aV))
      rw [reg a aV] at this
      omega
  obtain ⟨-, big, L, -, -, -, two, -, arcs⟩ := high_class (k := 2) (c := 8) (d := 11) (p := 8)
    free (by norm_num) reg HV (fun u => H.filter (fun v => D u v = true)) S8
    (fun u _ => filter_subset _ _)
    (fun u uT => sup u (by rw [← VH]; exact uT))
    (fun u uT a aH au => by
      have uV : u ∈ V := (mem_sdiff.mp uT).1
      have s := heads_seen (k := 2) free (by norm_num) le_rfl HV (HV aH) uV au
      exact ⟨fun y hy => (mem_filter.mp (s hy)).2.2,
        fun hy => (mem_filter.mp (s hy)).2.1 rfl⟩)
    (fun v vH => ThirtySix.indeg_wide free reg n (HV vH) ((mem_filter.mp
      (by rw [← ThirtySix.high_eq]; exact vH : v ∈ V.filter (fun v => 9 ≤ (layer D V 2 v).card))).2))
    (fun u uT => sup u (by rw [← VH]; exact uT))
  have h17 := big (card_pos.mp (by omega))
  rw [VH] at arcs
  have h18 : H.card ≤ 18 := by omega
  rcases (show H.card = 17 ∨ H.card = 18 by omega) with e | e
  · rw [e] at two arcs
    omega
  · rw [e] at two arcs
    omega

#print axioms through_layer
#print axioms equal_layer_near
#print axioms equal_layer_ball
#print axioms equal_layer_far
#print axioms equal_layer_gap
#print axioms equal_layer_pair
#print axioms duplicates_blind
#print axioms representatives
#print axioms high_class
#print axioms no36_regular'
end LeanCH.BR.EqualLayers
