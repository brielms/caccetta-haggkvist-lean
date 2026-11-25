import checkpoints.shen_extension.Profile54

/-!
# The fragment budget and the layer floors on the row `r = q + 3`

Generic in `D`, `q`, the fragment `F`, the slack `t`, the degree `r` and the radii `i`, `j`.

* `ordinary_floor` (`1 ≤ i ≤ q`, every row of `F` keeps `2 + t` heads in `F`): every row reaches
  at least `2i + t` other labels within `i` steps. Delete `t` of its heads; the rest keeps minimum
  out-degree two (`BRq2.ball_growth`).
* `full_floor` (`3 ≤ i ≤ q`, `r + 2 ≤ 2q`, `r + 1 + t ≤ |F|`): a row with exactly `r` heads in
  `F` reaches at least `r + 3 + t`. Delete `t` labels away from the row and its heads, all inside
  its `i`-ball if there are `t` such, else covering them; `Profile54.head_reach` in the rest.
* `mixed_budget` (`i + j ≤ q`): `∑ (reach_i + reach_j) ≤ |F| (|F| - 1)` (`ReachLedger.ledger`).
* `fragment_budget`: `|F| (2(i + j) + 2t) + 2 |Fs| (r + 3 - (i + j)) ≤ |F| (|F| - 1)`.

Corollaries on the row `r = q + 3`, `6 ≤ q`, radii `(3, q - 3)`:

* `exterior_floor_sets` / `exterior_floor` (C1): `|Z| = r - 1`, rows of `Z` inside `Z ∪ W`,
  rows of `W` inside `Z ∪ W ∪ J`: `2 (r - 1) ≤ |W| + |J|`.
* `thin_floor_sets` / `thin_floor` (C2): `|Y| = r - 1`, `|Z| = r`, rows of `Y` inside `Y ∪ Z`,
  rows of `Z` inside `Y ∪ Z ∪ W`: `r - 1 ≤ |W|`.
* `profile_bound` (C3): `|B_3 u| = 3r` gives `|Y| ≤ r`. At `q = 6` this implies
  `Profile54.no_wide_27` (`profile_bound_six`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FragmentBudget
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Profile54 (reach)

variable {D : CH.Digraph} {q : ℕ}

/-! ### Helpers -/

theorem ball_mono_set {F F' : Finset ℕ} (h : F ⊆ F') {x k : ℕ} :
    ball D F x k ⊆ ball D F' x k := by
  intro v hv
  obtain ⟨vW, j, hj, w⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨h vW, j, hj, w.mono h⟩

theorem reach_mono {F : Finset ℕ} {x i i' : ℕ} (h : i ≤ i') : reach D F i x ≤ reach D F i' x :=
  card_le_card (erase_subset_erase x (ball_mono_radius h))

/-- Deleting at most `t` labels costs every remaining row at most `t` heads. -/
theorem delete_deg {F T : Finset ℕ} {a t : ℕ} (hT : T.card ≤ t)
    (deg : ∀ v ∈ F, a + t ≤ (outN D F v).card) : ∀ v ∈ F \ T, a ≤ (outN D (F \ T) v).card := by
  intro v hv
  have sub : outN D F v \ T ⊆ outN D (F \ T) v := by
    intro w hw
    obtain ⟨hw1, hwT⟩ := mem_sdiff.mp hw
    obtain ⟨wF, vw⟩ := mem_outN.mp hw1
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨wF, hwT⟩, vw⟩
  have := le_card_sdiff T (outN D F v)
  have := card_le_card sub
  have := deg v (mem_sdiff.mp hv).1
  omega

/-- Heads outside `F` are covered by `E`. -/
theorem keep_le {V F E : Finset ℕ} {v : ℕ} (cover : outN D V v ⊆ F ∪ E) :
    (outN D V v).card ≤ (outN D F v).card + E.card := by
  have sub : outN D V v ⊆ outN D F v ∪ E := by
    intro w hw
    rcases mem_union.mp (cover hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ h
  exact (card_le_card sub).trans (card_union_le _ _)

theorem layer_disj {V : Finset ℕ} {u i j : ℕ} (h : i < j) :
    Disjoint (layer D V i u) (layer D V j u) := by
  rw [disjoint_left]
  intro v hi hj
  exact (mem_layer.mp hj).2 (ball_mono_radius (by omega) (mem_layer.mp hi).1)

/-! ### Row floors -/

/-- **Ordinary floor.** -/
theorem ordinary_floor {F : Finset ℕ} {t i : ℕ} (free : QFree D F q) (hi1 : 1 ≤ i) (hi : i ≤ q)
    (deg : ∀ v ∈ F, 2 + t ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F) :
    2 * i + t ≤ reach D F i x := by
  classical
  obtain ⟨T, TH, Tc⟩ := exists_subset_card_eq (s := outN D F x) (n := t)
    (by have := deg x hx; omega)
  have xT : x ∉ T := fun h => loopfree free (by omega) hx (mem_outN.mp (TH h)).2
  have d2 := delete_deg (a := 2) Tc.le deg
  have g := ball_growth q (by omega) D (F \ T) (free.mono_set sdiff_subset) d2 x
    (mem_sdiff.mpr ⟨hx, xT⟩) i hi
  have sub : ball D (F \ T) x i ∪ T ⊆ ball D F x i :=
    union_subset (ball_mono_set sdiff_subset)
      (fun w hw => ball_mono_radius hi1 ((mem_ball_one hx).mpr (Or.inr (TH hw))))
  have dis : Disjoint (ball D (F \ T) x i) T :=
    disjoint_left.mpr (fun w hw hwT => (mem_sdiff.mp (ball_subset hw)).2 hwT)
  have c := card_le_card sub
  rw [card_union_of_disjoint dis] at c
  have := Profile54.card_ball_erase (D := D) (W := F) (k := i) hx
  unfold reach
  omega

/-- **Full floor.** -/
theorem full_floor {F : Finset ℕ} {t r i : ℕ} (free : QFree D F q) (hi3 : 3 ≤ i) (hi : i ≤ q)
    (hr : r + 2 ≤ 2 * q) (hN : r + 1 + t ≤ F.card)
    (deg : ∀ v ∈ F, 2 + t ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F)
    (full : (outN D F x).card = r) : r + 3 + t ≤ reach D F i x := by
  classical
  set H := outN D F x with hH
  set E := insert x H with hE
  set U := ((ball D F x i).erase x) \ H with hU
  have xH : x ∉ H := fun h => loopfree free (by omega) hx (mem_outN.mp h).2
  have EF : E ⊆ F := insert_subset hx outN_subset
  have Ec : E.card = r + 1 := by rw [hE, card_insert_of_notMem xH, full]
  have UE : U ⊆ F \ E := by
    intro w hw
    obtain ⟨hw1, wH⟩ := mem_sdiff.mp hw
    obtain ⟨wx, wb⟩ := mem_erase.mp hw1
    refine mem_sdiff.mpr ⟨ball_subset wb, fun h => ?_⟩
    rcases mem_insert.mp h with e | e
    · exact wx e
    · exact wH e
  have FE : t ≤ (F \ E).card := by rw [card_sdiff_of_subset EF]; omega
  obtain ⟨T, TF, Tc, hT⟩ : ∃ T, T ⊆ F \ E ∧ T.card = t ∧ (T ⊆ U ∨ U ⊆ T) := by
    by_cases hUc : t ≤ U.card
    · obtain ⟨T, TU, Tc⟩ := exists_subset_card_eq hUc
      exact ⟨T, TU.trans UE, Tc, Or.inl TU⟩
    · obtain ⟨T, UT, TF, Tc⟩ := exists_subsuperset_card_eq UE (by omega) FE
      exact ⟨T, TF, Tc, Or.inr UT⟩
  have offT : ∀ w ∈ E, w ∉ T := fun w hw h => (mem_sdiff.mp (TF h)).2 hw
  have xF' : x ∈ F \ T := mem_sdiff.mpr ⟨hx, offT x (mem_insert_self x H)⟩
  have keepH : outN D (F \ T) x = H := Profile54.out_restrict sdiff_subset (fun w hw =>
    mem_sdiff.mpr ⟨(mem_outN.mp hw).1, offT w (mem_insert_of_mem hw)⟩)
  have d2 := delete_deg (a := 2) Tc.le deg
  have hrch := Profile54.head_reach (free.mono_set sdiff_subset) (by omega) xF'
    (by rw [keepH, full]; omega) d2
  rw [keepH, full] at hrch
  have mono := reach_mono (D := D) (F := F \ T) (x := x) hi3
  have sub : (ball D (F \ T) x i).erase x ⊆ ((ball D F x i).erase x) \ T := by
    intro w hw
    obtain ⟨wx, wb⟩ := mem_erase.mp hw
    exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨wx, ball_mono_set sdiff_subset wb⟩,
      (mem_sdiff.mp (ball_subset wb)).2⟩
  have c1 := card_le_card sub
  unfold reach at mono hrch ⊢
  rcases hT with TU | UT
  · have TB : T ⊆ (ball D F x i).erase x := fun w hw => (mem_sdiff.mp (TU hw)).1
    have := card_sdiff_of_subset TB
    have := card_le_card TB
    omega
  · have sH : ((ball D F x i).erase x) \ T ⊆ H := by
      intro w hw
      obtain ⟨wb, wT⟩ := mem_sdiff.mp hw
      by_contra wH
      exact wT (UT (mem_sdiff.mpr ⟨wb, wH⟩))
    have := card_le_card sH
    rw [full] at this
    omega

/-- **Mixed pair budget.** -/
theorem mixed_budget {F : Finset ℕ} {i j : ℕ} (free : QFree D F q) (hij : i + j ≤ q) :
    ∑ x ∈ F, (reach D F i x + reach D F j x) ≤ F.card * (F.card - 1) := by
  have led := ReachLedger.ledger (D := D) (V := F) (q := q) (i := i) (j := j) free hij
  have ei : ∑ x ∈ F, (ball D F x i).card = ∑ x ∈ F, (reach D F i x + 1) :=
    sum_congr rfl (fun x hx => (Profile54.card_ball_erase (D := D) (k := i) hx).symm)
  have ej : ∑ x ∈ F, (ball D F x j).card = ∑ x ∈ F, (reach D F j x + 1) :=
    sum_congr rfl (fun x hx => (Profile54.card_ball_erase (D := D) (k := j) hx).symm)
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at ei ej
  rw [ei, ej] at led
  rw [sum_add_distrib, Nat.mul_sub_one]
  have : F.card * (F.card + 1) = F.card * F.card + F.card := by ring
  have : F.card ≤ F.card * F.card := Nat.le_mul_self _
  omega

/-- Floors summed: `base` everywhere, `base + e` on `S`. -/
theorem floor_sum {F S : Finset ℕ} {c : ℕ → ℕ} {base e M : ℕ} (SF : S ⊆ F)
    (low : ∀ v ∈ F, base ≤ c v) (high : ∀ v ∈ S, base + e ≤ c v) (top : ∑ v ∈ F, c v ≤ M) :
    F.card * base + S.card * e ≤ M := by
  have ex := ReachLedger.sum_excess low
  have s1 : ∑ v ∈ S, (c v - base) ≤ ∑ v ∈ F, (c v - base) := sum_le_sum_of_subset SF
  have s2 : ∑ _v ∈ S, e ≤ ∑ v ∈ S, (c v - base) :=
    sum_le_sum (fun v hv => by have := high v hv; omega)
  rw [sum_const, smul_eq_mul] at s2
  omega

/-- **Fragment budget.** -/
theorem fragment_budget {F Fs : Finset ℕ} {t r i j : ℕ} (free : QFree D F q)
    (deg : ∀ v ∈ F, 2 + t ≤ (outN D F v).card) (FsF : Fs ⊆ F)
    (full : ∀ x ∈ Fs, (outN D F x).card = r) (hr : r + 2 ≤ 2 * q) (hN : r + 1 + t ≤ F.card)
    (hi : 3 ≤ i) (hj : 3 ≤ j) (hij : i + j ≤ q) :
    F.card * (2 * (i + j) + 2 * t) + 2 * Fs.card * (r + 3 - (i + j)) ≤
      F.card * (F.card - 1) := by
  have fs := floor_sum (c := fun x => reach D F i x + reach D F j x)
    (base := 2 * (i + j) + 2 * t) (e := 2 * (r + 3 - (i + j))) FsF
    (fun v hv => by
      have a := ordinary_floor free (by omega) (by omega) deg hv (i := i)
      have b := ordinary_floor free (by omega) (by omega) deg hv (i := j)
      omega)
    (fun v hv => by
      have a := ordinary_floor free (by omega) (by omega) deg (FsF hv) (i := i)
      have b := ordinary_floor free (by omega) (by omega) deg (FsF hv) (i := j)
      have a' := full_floor free hi (by omega) hr hN deg (FsF hv) (full v hv)
      have b' := full_floor free hj (by omega) hr hN deg (FsF hv) (full v hv)
      omega)
    (mixed_budget free hij)
  have e : 2 * Fs.card * (r + 3 - (i + j)) = Fs.card * (2 * (r + 3 - (i + j))) := by ring
  omega

/-! ### C1: the exterior floor -/

/-- **C1, sets.** -/
theorem exterior_floor_sets {V Z Wl J : Finset ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) (ZV : Z ⊆ V) (WV : Wl ⊆ V)
    (dZW : Disjoint Z Wl) (hZc : Z.card = q + 2) (hZ : ∀ z ∈ Z, outN D V z ⊆ Z ∪ Wl)
    (hW : ∀ w ∈ Wl, outN D V w ⊆ Z ∪ Wl ∪ J) : 2 * (q + 2) ≤ Wl.card + J.card := by
  have w1 : q + 2 ≤ Wl.card := by
    by_contra h
    have deg : ∀ z ∈ Z, 2 ≤ (outN D Z z).card := fun z hz => by
      have := keep_le (hZ z hz)
      rw [reg z (ZV hz)] at this
      omega
    have := Profile54.two_order (free.mono_set ZV) (by omega) (card_pos.mp (by omega)) deg
    omega
  by_contra h
  set t := Wl.card - (q + 2) with ht
  set F := Z ∪ Wl with hF
  have FV : F ⊆ V := union_subset ZV WV
  have Fc : F.card = 2 * q + 4 + t := by rw [hF, card_union_of_disjoint dZW]; omega
  have outZ : ∀ z ∈ Z, outN D F z = outN D V z := fun z hz =>
    Profile54.out_restrict FV (hZ z hz)
  have deg : ∀ v ∈ F, 2 + t ≤ (outN D F v).card := by
    intro v hv
    rcases mem_union.mp hv with hz | hw
    · rw [outZ v hz, reg v (ZV hz)]; omega
    · have := keep_le (hW v hw); rw [reg v (WV hw)] at this; omega
  have fb := fragment_budget (i := 3) (j := q - 3) (r := q + 3) (t := t) (Fs := Z)
    (free.mono_set FV) deg subset_union_left
    (fun z hz => by rw [outZ z hz, reg z (ZV hz)]) (by omega) (by omega) le_rfl (by omega)
    (by omega)
  have e1 : 3 + (q - 3) = q := by omega
  have e2 : q + 3 + 3 - q = 6 := by omega
  rw [e1, e2, hZc] at fb
  obtain ⟨N, hN⟩ : ∃ N, F.card = N := ⟨_, rfl⟩
  rw [hN] at fb
  have hN' : N = 2 * q + 4 + t := by rw [← hN, Fc]
  have e3 : N - 1 = 2 * q + 3 + t := by omega
  rw [e3] at fb
  rcases Nat.lt_or_ge t 3 with tl | tl
  · subst hN'
    interval_cases t <;> nlinarith [fb]
  · have := Nat.mul_le_mul_left N (show 2 * q + 3 + t ≤ 2 * q + 2 * t by omega)
    omega

/-- **C1.** Third layer of `r - 1` labels: `2 (r - 1) ≤ |W| + |J|`. -/
theorem exterior_floor {V : Finset ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) {u : ℕ}
    (hZc : (layer D V 3 u).card = q + 2)
    (hZ : ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u)
    (hW : ∀ w ∈ layer D V 4 u, outN D V w ⊆ layer D V 3 u ∪ layer D V 4 u ∪ layer D V 5 u) :
    2 * (q + 2) ≤ (layer D V 4 u).card + (layer D V 5 u).card :=
  exterior_floor_sets free hq reg layer_subset layer_subset (layer_disj (by norm_num)) hZc hZ hW

/-! ### C2: the thin floor -/

/-- **C2, sets.** -/
theorem thin_floor_sets {V Y Z Wl : Finset ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) (YV : Y ⊆ V) (ZV : Z ⊆ V)
    (dYZ : Disjoint Y Z) (hYc : Y.card = q + 2) (hZc : Z.card = q + 3)
    (hY : ∀ y ∈ Y, outN D V y ⊆ Y ∪ Z) (hZ : ∀ z ∈ Z, outN D V z ⊆ Y ∪ Z ∪ Wl) :
    q + 2 ≤ Wl.card := by
  by_contra h
  set F := Y ∪ Z with hF
  have FV : F ⊆ V := union_subset YV ZV
  have Fc : F.card = 2 * q + 5 := by rw [hF, card_union_of_disjoint dYZ]; omega
  have outY : ∀ y ∈ Y, outN D F y = outN D V y := fun y hy =>
    Profile54.out_restrict FV (hY y hy)
  have deg : ∀ v ∈ F, 2 + 0 ≤ (outN D F v).card := by
    intro v hv
    rcases mem_union.mp hv with hy | hz
    · rw [outY v hy, reg v (YV hy)]; omega
    · have := keep_le (hZ v hz); rw [reg v (ZV hz)] at this; omega
  have fb := fragment_budget (i := 3) (j := q - 3) (r := q + 3) (t := 0) (Fs := Y)
    (free.mono_set FV) deg subset_union_left
    (fun y hy => by rw [outY y hy, reg y (YV hy)]) (by omega) (by omega) le_rfl (by omega)
    (by omega)
  have e1 : 3 + (q - 3) = q := by omega
  have e2 : q + 3 + 3 - q = 6 := by omega
  rw [e1, e2, hYc, Fc, show 2 * q + 5 - 1 = 2 * q + 4 by omega] at fb
  nlinarith [fb]

/-- **C2.** Thin root with third layer `r`: `r - 1 ≤ |W|`. -/
theorem thin_floor {V : Finset ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) {u : ℕ}
    (hYc : (layer D V 2 u).card = q + 2) (hZc : (layer D V 3 u).card = q + 3)
    (hY : ∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u)
    (hZ : ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) :
    q + 2 ≤ (layer D V 4 u).card :=
  thin_floor_sets free hq reg layer_subset layer_subset (layer_disj (by norm_num)) hYc hZc hY hZ

/-! ### C3: the profile bound -/

/-- **C3.** `|B_3 u| = 3r` gives `|Y| ≤ r`. -/
theorem profile_bound {V : Finset ℕ} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) {u : ℕ} (hu : u ∈ V)
    (b3 : (ball D V u 3).card = 3 * (q + 3)) : (layer D V 2 u).card ≤ q + 3 := by
  classical
  by_contra hY
  have L := (ThinSuppliers.balls_by_layers free (by omega) reg hu).2.2
  set X := outN D V u with hX
  set Y := layer D V 2 u with hYdef
  set Z := layer D V 3 u with hZdef
  set t := Y.card - (q + 4) with ht
  have Zc : Z.card + t = q + 1 := by omega
  have Yc : Y.card = q + 4 + t := by omega
  have Xc : X.card = q + 3 := reg u hu
  set F := Profile54.inner D V u with hF
  have FV : F ⊆ V := Profile54.inner_subset
  have Fc : F.card = 2 * q + 7 + t := by
    have h1 : F.card = q + 3 + Y.card := Profile54.inner_card hu reg
    omega
  have XF : X ⊆ F := fun _ h => mem_union_left _ h
  have YF : Y ⊆ F := fun _ h => mem_union_right _ h
  have xk : ∀ x ∈ X, outN D F x = outN D V x := fun x hx =>
    Profile54.x_keep free (by omega) hu hx
  have yk : ∀ y ∈ Y, q + 3 ≤ (outN D F y).card + Z.card := fun y hy =>
    Profile54.y_keep free (by omega) reg hu hy
  have frF : QFree D F q := free.mono_set FV
  have deg : ∀ v ∈ F, 2 + t ≤ (outN D F v).card := by
    intro v hv
    rcases mem_union.mp hv with hx | hy
    · rw [xk v hx, reg v (outN_subset hx)]; omega
    · have := yk v hy; omega
  have fullX : ∀ x ∈ X, (outN D F x).card = q + 3 := fun x hx => by
    rw [xk x hx, reg x (outN_subset hx)]
  rcases Nat.eq_zero_or_pos t with t0 | tpos
  · -- `t = 0`: no row of `Y` points into `X`
    have deg2 : ∀ v ∈ F, 2 ≤ (outN D F v).card := fun v hv => by have := deg v hv; omega
    have deg0 : ∀ v ∈ F, 2 + 0 ≤ (outN D F v).card := fun v hv => by have := deg2 v hv; omega
    have noXY : ∀ y ∈ Y, ∀ x ∈ X, D y x ≠ true := by
      intro y0 hy0 x0 hx0 arc
      have bb := Profile54.back_ball frF (by omega) (XF hx0) (YF hy0) arc
      have hs := Profile54.head_second frF (by omega) (XF hx0) (by rw [fullX x0 hx0]; omega) deg2
      rw [fullX x0 hx0] at hs
      have r3 : q + 5 ≤ reach D F 3 y0 := by
        have := Profile54.card_ball_erase (D := D) (k := 3) (YF hy0)
        unfold reach
        omega
      have rj := reach_mono (D := D) (F := F) (x := y0) (show 3 ≤ q - 3 by omega)
      have oj := ordinary_floor frF (i := q - 3) (by omega) (by omega) deg0 (YF hy0)
      have hy : 2 * q + 10 ≤ reach D F 3 y0 + reach D F (q - 3) y0 := by omega
      have low : ∀ v ∈ F, 2 * q ≤ reach D F 3 v + reach D F (q - 3) v := fun v hv => by
        have a := ordinary_floor frF (i := 3) (by omega) (by omega) deg0 hv
        have b := ordinary_floor frF (i := q - 3) (by omega) (by omega) deg0 hv
        omega
      have highX : ∀ x ∈ X, 2 * q + 12 ≤ reach D F 3 x + reach D F (q - 3) x := fun x hx => by
        have a := full_floor frF (i := 3) le_rfl (by omega) (by omega) (by omega) deg0 (XF hx)
          (fullX x hx)
        have b := full_floor frF (i := q - 3) (by omega) (by omega) (by omega) (by omega) deg0
          (XF hx) (fullX x hx)
        omega
      have y0X : y0 ∉ X := fun h => (mem_layer.mp hy0).2 ((mem_ball_one hu).mpr (Or.inr h))
      have mb := mixed_budget (i := 3) (j := q - 3) frF (by omega)
      have ex := ReachLedger.sum_excess (c := fun v => reach D F 3 v + reach D F (q - 3) v) low
      have s1 := sum_le_sum_of_subset (f := fun v => reach D F 3 v + reach D F (q - 3) v - 2 * q)
        (insert_subset (YF hy0) XF)
      rw [sum_insert y0X] at s1
      have s2 : ∑ _x ∈ X, 12 ≤ ∑ x ∈ X, (reach D F 3 x + reach D F (q - 3) x - 2 * q) :=
        sum_le_sum (fun x hx => by have := highX x hx; omega)
      rw [sum_const, smul_eq_mul, Xc] at s2
      obtain ⟨N, hN⟩ : ∃ N, F.card = N := ⟨_, rfl⟩
      rw [hN] at ex mb
      have hN' : N = 2 * q + 7 := by rw [← hN, Fc, t0]
      have e3 : N * (N - 1) = N * (2 * q) + 6 * N := by
        rw [show N - 1 = 2 * q + 6 by omega]; ring
      omega
    have degY : ∀ y ∈ Y, 2 ≤ (outN D Y y).card := by
      intro y hy
      have sub : outN D F y ⊆ outN D Y y := by
        intro w hw
        obtain ⟨wF, yw⟩ := mem_outN.mp hw
        rcases mem_union.mp wF with wx | wy
        · exact absurd yw (noXY y hy w wx)
        · exact mem_outN.mpr ⟨wy, yw⟩
      have := card_le_card sub
      have := yk y hy
      omega
    have h2 : 2 * q + 1 ≤ Y.card := Profile54.two_order (free.mono_set layer_subset) (by omega)
      (card_pos.mp (by omega : 0 < Y.card)) degY
    omega
  · -- `t ≥ 1`: the fragment budget
    have fb := fragment_budget (i := 3) (j := q - 3) (r := q + 3) (t := t) (Fs := X) frF deg XF
      fullX (by omega) (by omega) le_rfl (by omega) (by omega)
    have e1 : 3 + (q - 3) = q := by omega
    have e2 : q + 3 + 3 - q = 6 := by omega
    rw [e1, e2, Xc] at fb
    obtain ⟨N, hN⟩ : ∃ N, F.card = N := ⟨_, rfl⟩
    rw [hN] at fb
    have hN' : N = 2 * q + 7 + t := by rw [← hN, Fc]
    have e3 : N - 1 = 2 * q + 6 + t := by omega
    rw [e3] at fb
    rcases Nat.lt_or_ge t 6 with tl | tl
    · subst hN'
      interval_cases t <;> nlinarith [fb]
    · have := Nat.mul_le_mul_left N (show 2 * q + 6 + t ≤ 2 * q + 2 * t by omega)
      omega

/-- C3 at `q = 6` is `Profile54.no_wide_27`. -/
theorem profile_bound_six {V : Finset ℕ} (free : QFree D V 6)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ} (hu : u ∈ V)
    (b3 : (ball D V u 3).card = 27) (wide : 10 ≤ (layer D V 2 u).card) : False := by
  have := profile_bound (q := 6) free le_rfl reg hu b3
  omega

#print axioms ordinary_floor
#print axioms full_floor
#print axioms mixed_budget
#print axioms floor_sum
#print axioms fragment_budget
#print axioms exterior_floor_sets
#print axioms exterior_floor
#print axioms thin_floor_sets
#print axioms thin_floor
#print axioms profile_bound
#print axioms profile_bound_six

end LeanCH.BR.FragmentBudget
