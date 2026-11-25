import checkpoints.shen_extension.ThinSuppliers
import checkpoints.shen_extension.ShapeClimbX

/-!
# Fat short roots: a second layer of at least `r` labels forces `|B₃| ≥ 3r` (at `r = 9`, `q = 5`)

Every row has out-degree at least `r`, the root `u` exactly `r`, and there is no closed walk of
length at most `q`. `X`, `Y`, `Z` are the first three layers of `u`, and `F = X ∪ Y` is its
punctured two-ball. Rows of `X` keep all their heads in `F`; rows of `Y` keep all but at most
`|Z|` of theirs.

Generic tools (any `q`):
* `order_deg`: a nonempty `q`-free set of minimum out-degree `c ≥ 2` has at least `2q + c - 1`
  labels (`BRq2.ball_growth` at `c = 2`, then delete one label per extra degree).
* `grow_min`: in a `q`-free set of minimum out-degree `d ≥ 2`, `1 ≤ j`, `j + 1 ≤ q`:
  `|B (j+1)| ≥ min (|B j| + d - 1) (2q + d)`. (The punctured `j`-ball keeps at least
  `d - k` heads per row, where `k` labels are new at radius `j + 1`.)
* `two_sink`: a row with at most `q` heads, each of out-degree at least `d`, has
  `|B 2| ≥ (heads) + 1 + d` (a sink among its heads).
* `succ_card`: an arc `a → b` gives `|B (j+1) a| ≥ |B j b| + 1` for `j + 1 ≤ q`.
* `frag`, `x_in_frag`, `y_in_frag`: the punctured two-ball `F` of a root and the degrees of its
  rows in `F`.

The theorem at `(q, r) = (5, 9)` (`fat_short_nine`): `|Y| ≥ 9` forces `|Y| + |Z| ≥ 17`.
Proof by the mixed `(2, 3)` ledger on `F` (`ReachLedger.ledger`).
* `|Y| ≥ 10`: all rows of `F` have out-degree at least `d = |Y| - 7 ≥ 3` in `F`; the row
  bounds of `grow_min`/`two_sink` already exceed the ledger.
* `|Y| = 9`: rows of `X` score at least `23`, rows of `Y` at least `12`; a row of `Y` with a
  head in `X` (a returner) scores `23`, a row of `Y` heading a returner `17`; the slack is `27`.
  No returner: `Y` keeps minimum degree two on nine labels. One returner: the lone rows of the
  rest of `Y` (at least four, `ThinSuppliers.lone_count`) all head it. Two returners: at most one
  row `p` of `Y` heads them; without `p` the other seven keep degree two, with `p` the other six
  are lone and all head `p`, and then the target `x` of a returner headed by `p` has its
  two-ball in the ten labels `X ∪ Y` minus those six, `p` and that returner — below the bound
  `11` for rows of `X`. Three returners exceed the slack.

Generic `(q, r)` (`fat_short`): the same proof with free ledger radii `(i, j)` and all numbers
replaced by computable bounds: `xB` (rows with `r` heads), `yB` (all rows), `retC`, `ptrC`
(`chainB` iterates `grow_min`). `fatCheck q r i j` is exactly the arithmetic the proof needs
(`wideOK`: each `|Y| = r + e`, `1 ≤ e ≤ r - 2`; `evenOK`: `|Y| = r` with the returner cases; in
the two-returner case with one pointer the target's `(q-3)`-ball is used). `fatCheck_5_9`: the
check at `(5, 9)`, radii `(2, 3)`. `fatOK q r` tries all radii; `fatShortGX q r` is the width
pattern wherever `fatOK q r` holds (`fatShortGX_sound`). Evaluated: `fatOK` holds for
`4 ≤ r ≤ 6, 9, 10, 12, 13, 15, 16, 18, 19` at `q = 4, …, 12` respectively (upper ends), e.g. at
`(5, 9)`, `(6, 10)`, `(7, 12)`; it fails at `(5, 10)`, `(6, 11)`, `(6, 12)`, `(7, 13)`, where the
ledger has too much slack (nothing is claimed there).

Departure from the paper (degree-nine dossier, Appendix 30, "At cutoff five, an 18-label
two-ball with seven exits has exactly one returning row" and "Cutoff five: f3=25 forces f2=17";
Appendix 5, "Sharper three-step floor for f2>=19"): the same ledger, but the sole-returner case
is closed by `lone_count` directly (four lone rows each pay five), and the two-returner case with
one pointer is closed by the two-ball of the returner's target, not by `g₃(p) ≥ 12`; the cases
`|Y| ≥ 10` use one generic row bound (`grow_min`, `two_sink`) for every `|Y|`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FatShort
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ThinSuppliers (lone mem_lone lone_subset lone_count)

variable {D : CH.Digraph} {q : ℕ}

/-! ### Generic ball bounds -/

/-- A nonempty `q`-free set of minimum out-degree `c ≥ 2` has at least `2q + c - 1` labels. -/
theorem order_deg {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q) :
    ∀ c, 2 ≤ c → (∀ v ∈ S, c ≤ (outN D S v).card) → S.Nonempty → 2 * q + c - 1 ≤ S.card := by
  intro c
  induction c generalizing S with
  | zero => intro h; omega
  | succ c ih =>
    intro hc deg ne
    rcases Nat.lt_or_ge c 2 with h | h
    · obtain rfl : c = 1 := by omega
      obtain ⟨u, hu⟩ := ne
      have := ball_growth q hq D S free (fun v hv => deg v hv) u hu q le_rfl
      have := card_le_card (ball_subset (D := D) (W := S) (u := u) (k := q))
      omega
    · obtain ⟨w, hw⟩ := ne
      have sub : S.erase w ⊆ S := erase_subset _ _
      have deg' : ∀ v ∈ S.erase w, c ≤ (outN D (S.erase w) v).card := by
        intro v hv
        have h1 := deg v (sub hv)
        have cover : outN D S v ⊆ insert w (outN D (S.erase w) v) := by
          intro z hz
          obtain ⟨zS, vz⟩ := mem_outN.mp hz
          by_cases e : z = w
          · exact e ▸ mem_insert_self _ _
          · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, zS⟩, vz⟩)
        have := (card_le_card cover).trans (card_insert_le _ _)
        omega
      have hsub : outN D S w ⊆ S.erase w := by
        intro z hz
        obtain ⟨zS, wz⟩ := mem_outN.mp hz
        exact mem_erase.mpr ⟨fun e => loopfree free hq hw (e ▸ wz), zS⟩
      have c1 := card_le_card hsub
      have c2 := deg w hw
      have ne' : (S.erase w).Nonempty := card_pos.mp (by omega)
      have := ih (free.mono_set sub) h deg' ne'
      rw [card_erase_of_mem hw] at this
      omega

/-- **Growth or a large closed ball.** In a `q`-free set of minimum out-degree `d ≥ 2`, for
`1 ≤ j` and `j + 1 ≤ q`: `|B (j+1)| ≥ min (|B j| + d - 1) (2q + d)`. -/
theorem grow_min {S : Finset ℕ} {d j j' v : ℕ} (free : QFree D S q) (hq : 1 ≤ q) (hd : 2 ≤ d)
    (deg : ∀ w ∈ S, d ≤ (outN D S w).card) (hv : v ∈ S) (hj : 1 ≤ j) (hjq : j + 1 ≤ q)
    (hjj : j' = j + 1) :
    min ((ball D S v j).card + d - 1) (2 * q + d) ≤ (ball D S v j').card := by
  classical
  subst hjj
  have mono := card_le_card (ball_mono_radius (D := D) (W := S) (u := v) (show j ≤ j + 1 by omega))
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  obtain ⟨hlt1, hlt2⟩ := hlt
  obtain ⟨k, hk⟩ : ∃ k, (ball D S v (j + 1)).card = (ball D S v j).card + k :=
    ⟨_, (Nat.add_sub_cancel' mono).symm⟩
  set P := (ball D S v j).erase v with hP
  have inP : ∀ p ∈ P, d - k ≤ (outN D P p).card := by
    intro p hp
    obtain ⟨pv, pb⟩ := mem_erase.mp hp
    have cover : outN D S p ⊆ outN D P p ∪ (ball D S v (j + 1) \ ball D S v j) := by
      intro z hz
      obtain ⟨zS, pz⟩ := mem_outN.mp hz
      have zb := ball_step pb zS pz
      have zv : z ≠ v := fun e => no_back_arc free hv pb hjq (e ▸ pz)
      by_cases zj : z ∈ ball D S v j
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_erase.mpr ⟨zv, zj⟩, pz⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨zb, zj⟩)
    have c1 := (card_le_card cover).trans (card_union_le _ _)
    rw [card_sdiff_of_subset (ball_mono_radius (D := D) (W := S) (u := v)
      (show j ≤ j + 1 by omega))] at c1
    have := deg p (ball_subset pb)
    omega
  obtain ⟨h, hh⟩ : (outN D S v).Nonempty := card_pos.mp (by have := deg v hv; omega)
  obtain ⟨hS, vh⟩ := mem_outN.mp hh
  have hP' : h ∈ P := mem_erase.mpr ⟨fun e => loopfree free hq hv (e ▸ vh),
    ball_mono_radius hj (mem_ball.mpr ⟨hS, 1, le_rfl, .step hS vh (.refl h)⟩)⟩
  have PS : P ⊆ S := (erase_subset _ _).trans ball_subset
  have Pc : P.card + 1 = (ball D S v j).card := card_erase_add_one (self_mem_ball hv)
  have big := order_deg (free.mono_set PS) hq (d - k) (by omega) inP ⟨h, hP'⟩
  omega

/-- **A sink among the heads.** A row with between one and `q` heads, in a `q`-free set where
every row has at least `d` heads: `|B 2| ≥ (heads) + 1 + d`. -/
theorem two_sink {S : Finset ℕ} {d v : ℕ} (free : QFree D S q) (hq : 2 ≤ q)
    (deg : ∀ w ∈ S, d ≤ (outN D S w).card) (hv : v ∈ S) (pos : 1 ≤ (outN D S v).card)
    (small : (outN D S v).card ≤ q) :
    (outN D S v).card + 1 + d ≤ (ball D S v 2).card := by
  classical
  obtain ⟨s, sN, sink⟩ := exists_sink (free.mono_set outN_subset) (card_pos.mp (by omega)) small
  obtain ⟨sS, vs⟩ := mem_outN.mp sN
  have s1 : s ∈ ball D S v 1 := (mem_ball_one hv).mpr (Or.inr sN)
  have sub : outN D S s ⊆ ball D S v 2 \ ball D S v 1 := by
    intro z hz
    obtain ⟨zS, sz⟩ := mem_outN.mp hz
    refine mem_sdiff.mpr ⟨ball_step s1 zS sz, fun h1 => ?_⟩
    rcases (mem_ball_one hv).mp h1 with rfl | zN
    · exact digonfree free hq hv sS vs sz
    · exact sink z zN sz
  have c := card_le_card sub
  rw [card_sdiff_of_subset (ball_mono_radius (D := D) (W := S) (u := v) (show 1 ≤ 2 by norm_num))] at c
  have b1 := ReachLedger.ball_one free (by omega) hv
  have := deg s sS
  have := card_le_card (ball_mono_radius (D := D) (W := S) (u := v) (show 1 ≤ 2 by norm_num))
  omega

/-- An arc `a → b` puts the `j`-ball of `b` and `a` itself in the `(j+1)`-ball of `a`. -/
theorem succ_card {S : Finset ℕ} {a b j j' : ℕ} (free : QFree D S q) (aS : a ∈ S) (bS : b ∈ S)
    (ab : D a b = true) (hj : j + 1 ≤ q) (hjj : j' = j + 1) :
    (ball D S b j).card + 1 ≤ (ball D S a j').card := by
  subst hjj
  have sub : insert a (ball D S b j) ⊆ ball D S a (j + 1) :=
    insert_subset (self_mem_ball aS) (ReachLedger.ball_succ bS ab)
  have off : a ∉ ball D S b j := by
    intro h
    obtain ⟨-, m, hm, w⟩ := mem_ball.mp h
    exact free a (m + 1) (by omega) (by omega) (.step bS ab w)
  have := card_le_card sub
  rw [card_insert_of_notMem off] at this
  exact this

/-! ### The punctured two-ball of a root -/

section frag
variable {V : Finset ℕ} {u r : ℕ}

/-- The punctured two-ball: heads and second layer. -/
noncomputable def frag (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  outN D V u ∪ layer D V 2 u

theorem frag_subset : frag D V u ⊆ V := union_subset outN_subset layer_subset

theorem frag_disj (hu : u ∈ V) : Disjoint (outN D V u) (layer D V 2 u) := by
  rw [disjoint_left]
  intro x hx hy
  exact (mem_layer.mp hy).2 ((mem_ball_one hu).mpr (Or.inr hx))

theorem frag_card (hu : u ∈ V) :
    (frag D V u).card = (outN D V u).card + (layer D V 2 u).card :=
  card_union_of_disjoint (frag_disj hu)

/-- Rows of `X` keep all their heads in `F`. -/
theorem x_in_frag (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V) {x : ℕ}
    (hx : x ∈ outN D V u) : outN D (frag D V u) x = outN D V x := by
  ext w
  constructor
  · intro hw
    exact mem_outN.mpr ⟨frag_subset (mem_outN.mp hw).1, (mem_outN.mp hw).2⟩
  · intro hw
    exact mem_outN.mpr ⟨LoopCollar.head_keep free hq hu x hx hw, (mem_outN.mp hw).2⟩

/-- Rows of `Y` keep all but at most `|Z|` heads in `F`. -/
theorem y_in_frag (free : QFree D V q) (hq : 3 ≤ q) (hu : u ∈ V) {y : ℕ}
    (hy : y ∈ layer D V 2 u) :
    (outN D V y).card ≤ (outN D (frag D V u) y).card + (layer D V 3 u).card := by
  classical
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have cover : outN D V y ⊆ outN D (frag D V u) y ∪ layer D V 3 u := by
    intro w hw
    obtain ⟨wV, yw⟩ := mem_outN.mp hw
    have wb : w ∈ ball D V u 3 := ball_step yb wV yw
    by_cases w2 : w ∈ ball D V u 2
    · refine mem_union_left _ (mem_outN.mpr ⟨?_, yw⟩)
      by_cases w1 : w ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp w1 with rfl | wX
        · exact (no_back_arc free hu yb (by omega) yw).elim
        · exact mem_union_left _ wX
      · exact mem_union_right _ (mem_layer.mpr ⟨w2, w1⟩)
    · exact mem_union_right _ (mem_layer.mpr ⟨wb, w2⟩)
  exact (card_le_card cover).trans (card_union_le _ _)

end frag

/-! ### Degree nine, cutoff five -/

section nine
variable {V : Finset ℕ} {u : ℕ}

/-- **Fat short roots at `r = 9`, `q = 5`.** Minimum out-degree nine, root of out-degree exactly
nine, no closed walk of length at most five: a second layer of at least nine labels forces
`|Y| + |Z| ≥ 17`, i.e. `|B 3 u| ≥ 27`. -/
theorem fat_short_nine (free : QFree D V 5) (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card)
    (hu : u ∈ V) (root : (outN D V u).card = 9) (fat : 9 ≤ (layer D V 2 u).card) :
    17 ≤ (layer D V 2 u).card + (layer D V 3 u).card := by
  classical
  by_contra small
  push Not at small
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set F := frag D V u with hF
  have FV : F ⊆ V := frag_subset
  have fr : QFree D F 5 := free.mono_set FV
  have XF : X ⊆ F := subset_union_left
  have YF : Y ⊆ F := subset_union_right
  have Fc : F.card = 9 + Y.card := by
    have := frag_card (D := D) hu
    rw [← hF, ← hX, ← hY] at this
    omega
  have xdeg : ∀ x ∈ X, 9 ≤ (outN D F x).card := fun x hx => by
    rw [hF, x_in_frag free (by norm_num) hu hx]; exact deg x (outN_subset hx)
  have ydeg : ∀ y ∈ Y, Y.card - 7 ≤ (outN D F y).card := fun y hy => by
    have h1 := y_in_frag free (by norm_num) hu hy
    have h2 := deg y (layer_subset hy)
    rw [← hF] at h1
    omega
  have memF : ∀ v ∈ F, v ∈ X ∨ v ∈ Y := fun v hv => mem_union.mp hv
  have disj : Disjoint X Y := frag_disj hu
  -- the ledger on `F`
  have led := ReachLedger.ledger (D := D) (V := F) (i := 2) (j := 3) fr (by norm_num)
  have sumF : ∑ v ∈ F, ((ball D F v 2).card + (ball D F v 3).card) =
      ∑ v ∈ X, ((ball D F v 2).card + (ball D F v 3).card) +
        ∑ v ∈ Y, ((ball D F v 2).card + (ball D F v 3).card) := sum_union disj
  rw [← sum_add_distrib] at led
  rw [sumF, Fc] at led
  have m2 : MinOut2 D F := by
    intro v hv
    change 2 ≤ (outN D F v).card
    rcases memF v hv with h | h
    · have := xdeg v h; omega
    · have := ydeg v h; omega
  -- every row of `X` reaches at least `11` and `12` labels within two and three
  have xb1 : ∀ x ∈ X, 10 ≤ (ball D F x 1).card := fun x hx => by
    rw [ReachLedger.ball_one fr (by norm_num) (XF hx)]; have := xdeg x hx; omega
  rcases Nat.lt_or_ge 9 Y.card with wide | nine
  · ---- `|Y| ≥ 10`: minimum degree `d = |Y| - 7 ≥ 3` everywhere
    obtain ⟨d, hd⟩ : ∃ d, Y.card = d + 7 := ⟨Y.card - 7, by omega⟩
    have fdeg : ∀ v ∈ F, d ≤ (outN D F v).card := fun v hv => by
      rcases memF v hv with h | h
      · have := xdeg v h; omega
      · have := ydeg v h; omega
    have xrow : ∀ x ∈ X, 19 + 2 * d ≤ (ball D F x 2).card + (ball D F x 3).card := by
      intro x hx
      have g2 := grow_min fr (by norm_num) (by omega) fdeg (XF hx) (j := 1) (j' := 2) le_rfl (by norm_num) rfl
      have g3 := grow_min fr (by norm_num) (by omega) fdeg (XF hx) (j := 2) (j' := 3) (by norm_num) (by norm_num) rfl
      have := xb1 x hx
      omega
    have yrow : ∀ y ∈ Y, min (2 * d + 1) (6 + d) + min (min (2 * d + 1) (6 + d) + d - 1) (10 + d) ≤
        (ball D F y 2).card + (ball D F y 3).card := by
      intro y hy
      have b2 : min (2 * d + 1) (6 + d) ≤ (ball D F y 2).card := by
        have yd := fdeg y (YF hy)
        have b1 := ReachLedger.ball_one fr (by norm_num) (YF hy)
        rcases Nat.lt_or_ge 5 (outN D F y).card with h | h
        · have g2 := grow_min fr (by norm_num) (by omega) fdeg (YF hy) (j := 1) (j' := 2) le_rfl (by norm_num) rfl
          omega
        · have := two_sink fr (by norm_num) fdeg (YF hy) (by omega) h
          omega
      have g3 := grow_min fr (by norm_num) (by omega) fdeg (YF hy) (j := 2) (j' := 3) (by norm_num) (by norm_num) rfl
      omega
    have sx := sum_le_sum xrow
    have sy := sum_le_sum yrow
    rw [sum_const, smul_eq_mul, root] at sx
    rw [sum_const, smul_eq_mul] at sy
    rw [hd] at sy led
    have d9 : d ≤ 9 := by omega
    have d3 : 3 ≤ d := by omega
    interval_cases d <;> norm_num at sy led <;> omega
  · ---- `|Y| = 9`: returners
    have Y9 : Y.card = 9 := by omega
    set R := Y.filter (fun y => ∃ x ∈ X, D y x = true) with hR
    set Pt := (Y \ R).filter (fun c => ∃ y ∈ R, D c y = true) with hPt
    have RY : R ⊆ Y := filter_subset _ _
    have PtY : Pt ⊆ Y := (filter_subset _ _).trans sdiff_subset
    have xb2 : ∀ x ∈ X, 11 ≤ (ball D F x 2).card := fun x hx => by
      have g2 := grow_min fr (by norm_num) le_rfl
        (fun v hv => (m2 v hv : 2 ≤ (outN D F v).card)) (XF hx) (j := 1) (j' := 2) le_rfl (by norm_num) rfl
      have := xb1 x hx
      omega
    have xb3 : ∀ x ∈ X, 12 ≤ (ball D F x 3).card := fun x hx => by
      have g3 := grow_min fr (by norm_num) le_rfl
        (fun v hv => (m2 v hv : 2 ≤ (outN D F v).card)) (XF hx) (j := 2) (j' := 3) (by norm_num) (by norm_num) rfl
      have := xb2 x hx
      omega
    have xrow : ∀ x ∈ X, 23 ≤ (ball D F x 2).card + (ball D F x 3).card := fun x hx => by
      have := xb2 x hx; have := xb3 x hx; omega
    have retb : ∀ y ∈ R, 11 ≤ (ball D F y 2).card ∧ 12 ≤ (ball D F y 3).card := by
      intro y hy
      obtain ⟨yY, x, hx, yx⟩ := mem_filter.mp hy
      have a := succ_card fr (YF yY) (XF hx) yx (j := 1) (j' := 2) (by norm_num) rfl
      have b := succ_card fr (YF yY) (XF hx) yx (j := 2) (j' := 3) (by norm_num) rfl
      have := xb1 x hx
      have := xb2 x hx
      exact ⟨by omega, by omega⟩
    have yrow : ∀ y ∈ Y, 12 + (if y ∈ R then 11 else 0) + (if y ∈ Pt then 5 else 0) ≤
        (ball D F y 2).card + (ball D F y 3).card := by
      intro y hy
      have b2 := ball_growth 5 (by norm_num) D F fr m2 y (YF hy) 2 (by norm_num)
      have b3 := ball_growth 5 (by norm_num) D F fr m2 y (YF hy) 3 (by norm_num)
      by_cases yR : y ∈ R
      · have yP : y ∉ Pt := fun h => (mem_sdiff.mp (mem_filter.mp h).1).2 yR
        have := retb y yR
        simp only [yR, yP, ↓reduceIte]
        omega
      · by_cases yP : y ∈ Pt
        · obtain ⟨-, y', hy', yy'⟩ := mem_filter.mp yP
          have := succ_card fr (YF hy) (YF (RY hy')) yy' (j := 2) (j' := 3) (by norm_num) rfl
          have := (retb y' hy').1
          simp only [yR, yP, ↓reduceIte]
          omega
        · simp only [yR, yP, ↓reduceIte]
          omega
    have sx := sum_le_sum xrow
    have sy := sum_le_sum yrow
    rw [sum_const, smul_eq_mul, root] at sx
    have e0 : ∑ y ∈ Y, (12 : ℕ) = 12 * Y.card := by rw [sum_const, smul_eq_mul, mul_comm]
    have e1 : ∑ y ∈ Y, (if y ∈ R then 11 else 0) = 11 * R.card := by
      rw [sum_ite_mem, inter_eq_right.mpr RY, sum_const, smul_eq_mul, mul_comm]
    have e2 : ∑ y ∈ Y, (if y ∈ Pt then 5 else 0) = 5 * Pt.card := by
      rw [sum_ite_mem, inter_eq_right.mpr PtY, sum_const, smul_eq_mul, mul_comm]
    rw [sum_add_distrib, sum_add_distrib, e0, e1, e2] at sy
    rw [Y9] at sy led
    have budget : 11 * R.card + 5 * Pt.card ≤ 27 := by omega
    -- rows of `Y` outside `R` keep their heads in `Y`
    have keepY : ∀ c ∈ Y, c ∉ R → outN D F c ⊆ outN D Y c := by
      intro c hc cR w hw
      obtain ⟨wF, cw⟩ := mem_outN.mp hw
      rcases memF w wF with wX | wY
      · exact (cR (mem_filter.mpr ⟨hc, w, wX, cw⟩)).elim
      · exact mem_outN.mpr ⟨wY, cw⟩
    have ydeg2 : ∀ c ∈ Y, 2 ≤ (outN D F c).card := fun c hc => by have := ydeg c hc; omega
    have frY : QFree D Y 5 := fr.mono_set YF
    rcases Nat.lt_or_ge R.card 1 with r0 | r1
    · -- no returner: `Y` keeps minimum degree two on nine labels
      have R0 : R = ∅ := card_eq_zero.mp (by omega)
      have m2Y : MinOut2 D Y := by
        intro c hc
        change 2 ≤ (outN D Y c).card
        exact (ydeg2 c hc).trans (card_le_card (keepY c hc (by rw [R0]; exact notMem_empty c)))
      obtain ⟨c, hc⟩ : Y.Nonempty := card_pos.mp (by omega)
      have := order_deg frY (by norm_num) 2 le_rfl (fun v hv => m2Y v hv) ⟨c, hc⟩
      omega
    rcases Nat.lt_or_ge R.card 2 with r1' | r2
    · -- one returner `y0`: the lone rows of `Y - y0` all head it
      obtain ⟨y0, hR1⟩ := card_eq_one.mp (show R.card = 1 by omega)
      have y0R : y0 ∈ R := by rw [hR1]; exact mem_singleton_self _
      have y0Y := RY y0R
      set Y' := Y.erase y0 with hY'
      have Y'Y : Y' ⊆ Y := erase_subset _ _
      have notR : ∀ c ∈ Y', c ∉ R := fun c hc cR => by
        rw [hR1, mem_singleton] at cR; exact (mem_erase.mp hc).1 cR
      have deg1 : ∀ c ∈ Y', 1 ≤ (outN D Y' c).card := by
        intro c hc
        have h2 := (ydeg2 c (Y'Y hc)).trans (card_le_card (keepY c (Y'Y hc) (notR c hc)))
        have cover : outN D Y c ⊆ insert y0 (outN D Y' c) := by
          intro w hw
          obtain ⟨wY, cw⟩ := mem_outN.mp hw
          by_cases e : w = y0
          · exact e ▸ mem_insert_self _ _
          · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, wY⟩, cw⟩)
        have := (card_le_card cover).trans (card_insert_le _ _)
        omega
      have Y'c : Y'.card = 8 := by rw [hY', card_erase_of_mem y0Y, Y9]
      have lc := lone_count (fr.mono_set (Y'Y.trans YF)) (by norm_num) deg1
        (card_pos.mp (by omega)) (by omega)
      have loneP : lone D Y' ⊆ Pt := by
        intro c hc
        obtain ⟨cY', one⟩ := mem_lone.mp hc
        have h2 := (ydeg2 c (Y'Y cY')).trans (card_le_card (keepY c (Y'Y cY') (notR c cY')))
        have cy0 : D c y0 = true := by
          by_contra n
          have sub : outN D Y c ⊆ outN D Y' c := by
            intro w hw
            obtain ⟨wY, cw⟩ := mem_outN.mp hw
            exact mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => n (e ▸ cw), wY⟩, cw⟩
          have := card_le_card sub
          omega
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨Y'Y cY', notR c cY'⟩, y0, y0R, cy0⟩
      have := card_le_card loneP
      omega
    · -- two returners and at most one row heading them
      have R2 : R.card = 2 := by omega
      have Pt1 : Pt.card ≤ 1 := by omega
      set Y'' := (Y \ R) \ Pt with hY''
      have Y''Y : Y'' ⊆ Y := sdiff_subset.trans sdiff_subset
      have Y''c : Y''.card + Pt.card = 7 := by
        have e1 : (Y \ R).card = 7 := by rw [card_sdiff_of_subset RY, Y9, R2]
        have e2 := card_sdiff_add_card_eq_card (show Pt ⊆ Y \ R from filter_subset _ _)
        rw [hY'']
        omega
      have outside : ∀ c ∈ Y'', ∀ w ∈ outN D F c, w ∈ Y'' ∨ w ∈ Pt := by
        intro c hc w hw
        obtain ⟨c1, cP⟩ := mem_sdiff.mp hc
        obtain ⟨cY, cR⟩ := mem_sdiff.mp c1
        obtain ⟨wF, cw⟩ := mem_outN.mp hw
        have wY : w ∈ Y := (mem_outN.mp (keepY c cY cR hw)).1
        have wR : w ∉ R := fun wR => cP (mem_filter.mpr ⟨c1, w, wR, cw⟩)
        by_cases wP : w ∈ Pt
        · exact Or.inr wP
        · exact Or.inl (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨wY, wR⟩, wP⟩)
      rcases Nat.lt_or_ge Pt.card 1 with p0 | p1
      · -- no row heads a returner: the other seven keep degree two
        have P0 : Pt = ∅ := card_eq_zero.mp (by omega)
        have m2Y : ∀ c ∈ Y'', 2 ≤ (outN D Y'' c).card := by
          intro c hc
          refine (ydeg2 c (Y''Y hc)).trans (card_le_card fun w hw => ?_)
          rcases outside c hc w hw with h | h
          · exact mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩
          · rw [P0] at h; exact absurd h (notMem_empty w)
        have := order_deg (fr.mono_set (Y''Y.trans YF)) (by norm_num) 2 le_rfl m2Y
          (card_pos.mp (by omega))
        omega
      · -- one row `p` heads the returners: the other six are lone and head `p`
        obtain ⟨p, hP1⟩ := card_eq_one.mp (show Pt.card = 1 by omega)
        have pP : p ∈ Pt := by rw [hP1]; exact mem_singleton_self _
        have Y6 : Y''.card = 6 := by omega
        have deg1 : ∀ c ∈ Y'', 1 ≤ (outN D Y'' c).card := by
          intro c hc
          have h2 := ydeg2 c (Y''Y hc)
          have cover : outN D F c ⊆ insert p (outN D Y'' c) := by
            intro w hw
            rcases outside c hc w hw with h | h
            · exact mem_insert_of_mem (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
            · rw [hP1, mem_singleton] at h; exact h ▸ mem_insert_self _ _
          have := (card_le_card cover).trans (card_insert_le _ _)
          omega
        have lc := lone_count (fr.mono_set (Y''Y.trans YF)) (by norm_num) deg1
          (card_pos.mp (by omega)) (by omega)
        have allLone : lone D Y'' = Y'' :=
          eq_of_subset_of_card_le lone_subset (by omega)
        have headp : ∀ c ∈ Y'', D c p = true := by
          intro c hc
          have cl : c ∈ lone D Y'' := by rw [allLone]; exact hc
          have one := (mem_lone.mp cl).2
          have h2 := ydeg2 c (Y''Y hc)
          by_contra n
          have sub : outN D F c ⊆ outN D Y'' c := by
            intro w hw
            rcases outside c hc w hw with h | h
            · exact mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩
            · rw [hP1, mem_singleton] at h; exact (n (h ▸ (mem_outN.mp hw).2)).elim
          have := card_le_card sub
          omega
        obtain ⟨pYR, y1, y1R, py1⟩ := mem_filter.mp pP
        obtain ⟨y1Y, x1, x1X, y1x1⟩ := mem_filter.mp y1R
        have pY := PtY pP
        -- the two-ball of `x1` avoids `Y''`, `p` and `y1`
        set Out := insert y1 (insert p Y'') with hOut
        have pY'' : p ∉ Y'' := fun h => (mem_sdiff.mp h).2 pP
        have y1Y'' : y1 ∉ insert p Y'' := by
          intro h
          rcases mem_insert.mp h with e | h
          · exact (mem_sdiff.mp pYR).2 (e ▸ y1R)
          · exact (mem_sdiff.mp (mem_sdiff.mp h).1).2 y1R
        have Outc : Out.card = 8 := by
          rw [hOut, card_insert_of_notMem y1Y'', card_insert_of_notMem pY'', Y6]
        have OutF : Out ⊆ F := insert_subset (YF y1Y) (insert_subset (YF pY) (Y''Y.trans YF))
        have avoid : ball D F x1 2 ⊆ F \ Out := by
          intro w hw
          obtain ⟨wF, m, hm, walk⟩ := mem_ball.mp hw
          refine mem_sdiff.mpr ⟨wF, fun wO => ?_⟩
          have x1F := XF x1X
          rcases mem_insert.mp wO with rfl | wO
          · exact fr x1 (m + 1) (by omega) (by omega) (walk.snoc x1F y1x1)
          rcases mem_insert.mp wO with rfl | wO
          · exact fr x1 (m + 1 + 1) (by omega) (by omega)
              ((walk.snoc (YF y1Y) py1).snoc x1F y1x1)
          · exact fr x1 (m + 1 + 1 + 1) (by omega) (by omega)
              (((walk.snoc (YF pY) (headp w wO)).snoc (YF y1Y) py1).snoc x1F y1x1)
        have := card_le_card avoid
        rw [card_sdiff_of_subset OutF, Fc, Y9, Outc] at this
        have := xb2 x1 x1X
        omega

/-- The statement consumed by `ThinSuppliers.no_44_of_fatShort` and `ThinSuppliers.profile_45`. -/
theorem fatShort_nine (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    ∀ v ∈ V, 9 ≤ (layer D V 2 v).card → 27 ≤ (ball D V v 3).card := by
  intro v hv fat
  have := fat_short_nine free (fun w hw => (reg w hw).ge) hv (reg v hv) fat
  have L := ThinSuppliers.balls_by_layers free (by norm_num) reg hv
  omega

/-- **No `5`-free `9`-out-regular digraph on `44` labels.** -/
theorem no_44 (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 44) :
    False :=
  ThinSuppliers.no_44_of_fatShort free reg n (fatShort_nine free reg)

/-- **What remains at `45`**, with `fatShort` discharged: if thin roots that are not tight have
four-ball at least `33`, every root has second layer `9` and third layer `8`. -/
theorem profile_45 (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 45)
    (f4 : ∀ v ∈ V, ThinSuppliers.Thin D V 9 v → ¬ ThinSuppliers.TightR D V 9 v →
      33 ≤ (ball D V v 4).card) :
    ∀ v ∈ V, (layer D V 2 v).card = 9 ∧ (layer D V 3 v).card = 8 :=
  ThinSuppliers.profile_45 free reg n f4 (fatShort_nine free reg)

end nine

/-! ### Generic `(q, r)`: the same proof under an arithmetic check -/

/-- Lower bounds for the balls of a row: `1`, `b1`, `b2`, then `grow_min`. -/
def chainB (q d b1 b2 : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => b1
  | 2 => b2
  | k + 3 => min (chainB q d b1 b2 (k + 2) + d - 1) (2 * q + d)

theorem chainB_sound {S : Finset ℕ} {d b1 b2 v : ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (hd : 2 ≤ d) (deg : ∀ w ∈ S, d ≤ (outN D S w).card) (hv : v ∈ S)
    (h1 : b1 ≤ (ball D S v 1).card) (h2 : b2 ≤ (ball D S v 2).card) :
    ∀ k, k ≤ q → chainB q d b1 b2 k ≤ (ball D S v k).card
  | 0, _ => card_pos.mpr ⟨v, self_mem_ball hv⟩
  | 1, _ => h1
  | 2, _ => h2
  | k + 3, hk => by
    have ih := chainB_sound free hq hd deg hv h1 h2 (k + 2) (by omega)
    have g := grow_min free hq hd deg hv (j := k + 2) (j' := k + 3) (by omega) (by omega) rfl
    simp only [chainB]
    omega

/-- Ball bounds for a row with at least `r` heads. -/
def xB (q r d k : ℕ) : ℕ := chainB q d (r + 1) (min (r + d) (2 * q + d)) k

/-- Ball bounds for any row. -/
def yB (q d k : ℕ) : ℕ := max (2 * k + 1) (chainB q d (d + 1) (min (2 * d + 1) (q + 1 + d)) k)

theorem xB_sound {S : Finset ℕ} {d r x : ℕ} (free : QFree D S q) (hq : 2 ≤ q) (hd : 2 ≤ d)
    (deg : ∀ w ∈ S, d ≤ (outN D S w).card) (hx : x ∈ S) (big : r ≤ (outN D S x).card) :
    ∀ k, k ≤ q → xB q r d k ≤ (ball D S x k).card := by
  have b1 := ReachLedger.ball_one free (by omega) hx
  have g := grow_min free (by omega) hd deg hx (j := 1) (j' := 2) le_rfl (by omega) rfl
  exact chainB_sound free (by omega) hd deg hx (by omega) (by omega)

theorem yB_sound {S : Finset ℕ} {d y : ℕ} (free : QFree D S q) (hq : 2 ≤ q) (hd : 2 ≤ d)
    (deg : ∀ w ∈ S, d ≤ (outN D S w).card) (hy : y ∈ S) :
    ∀ k, k ≤ q → yB q d k ≤ (ball D S y k).card := by
  intro k hk
  have m2 : MinOut2 D S := fun v hv => (show 2 ≤ (outN D S v).card by have := deg v hv; omega)
  have grow := ball_growth q (by omega) D S free m2 y hy k hk
  have b1 := ReachLedger.ball_one free (by omega) hy
  have yd := deg y hy
  have b2 : min (2 * d + 1) (q + 1 + d) ≤ (ball D S y 2).card := by
    rcases Nat.lt_or_ge q (outN D S y).card with h | h
    · have g := grow_min free (by omega) hd deg hy (j := 1) (j' := 2) le_rfl (by omega) rfl
      omega
    · have := two_sink free hq deg hy (by omega) h
      omega
  have ch := chainB_sound free (by omega) hd deg hy (b1 := d + 1) (by omega) b2 k hk
  exact max_le grow ch

/-- The wide cases `|Y| = r + e`, `1 ≤ e ≤ r - 2`: the ledger fails at minimum degree `e + 2`. -/
def wideOK (q r i j : ℕ) : Bool :=
  (List.range (r - 2)).all fun e' =>
    decide ((r + (r + (e' + 1))) * (r + (r + (e' + 1)) + 1) <
      r * (xB q r (e' + 1 + 2) i + xB q r (e' + 1 + 2) j) +
        (r + (e' + 1)) * (yB q (e' + 1 + 2) i + yB q (e' + 1 + 2) j))

/-- Extra score of a returner. -/
def retC (q r i j : ℕ) : ℕ :=
  (max (yB q 2 i) (xB q r 2 (i - 1) + 1) - yB q 2 i) +
    (max (yB q 2 j) (xB q r 2 (j - 1) + 1) - yB q 2 j)

/-- Extra score of a row heading a returner. -/
def ptrC (q r i j : ℕ) : ℕ :=
  (max (yB q 2 i) (xB q r 2 (i - 2) + 2) - yB q 2 i) +
    (max (yB q 2 j) (xB q r 2 (j - 2) + 2) - yB q 2 j)

/-- The base score at `|Y| = r`. -/
def baseC (q r i j : ℕ) : ℕ := r * (xB q r 2 i + xB q r 2 j) + r * (yB q 2 i + yB q 2 j)

/-- The case `|Y| = r`: no returner (rank two on `r ≤ 2q` labels), one returner (its lone
pointers), two returners (at most one pointer; its lone rows and the target's ball), three. -/
def evenOK (q r i j : ℕ) : Bool :=
  decide (r ≤ 2 * q ∧
    (r + r) * (r + r + 1) < baseC q r i j + retC q r i j + (2 * q + 3 - r) * ptrC q r i j ∧
    (r + r) * (r + r + 1) < baseC q r i j + 3 * retC q r i j ∧
    ((r + r) * (r + r + 1) < baseC q r i j + 2 * retC q r i j + ptrC q r i j ∨
      ((r + r) * (r + r + 1) < baseC q r i j + 2 * retC q r i j + 2 * ptrC q r i j ∧
        3 * r < xB q r 2 (q - 3) + 2 * q + 7)))

/-- The arithmetic check for the radii `(i, j)`. -/
def fatCheck (q r i j : ℕ) : Bool :=
  decide (2 ≤ i ∧ 2 ≤ j ∧ i + j ≤ q ∧ 4 ≤ r) && wideOK q r i j && evenOK q r i j

/-- Some radii pass the check. -/
def fatOK (q r : ℕ) : Bool := (List.range (q + 1)).any fun i => fatCheck q r i (q - i)

section gen
variable {V : Finset ℕ} {u r : ℕ}

/-- **Fat short roots, generic.** Minimum out-degree `r`, root of out-degree exactly `r`, no
closed walk of length at most `q`, and `fatCheck q r i j`: a second layer of at least `r`
labels forces `|Y| + |Z| ≥ 2r - 1`. -/
theorem fat_short {i j : ℕ} (check : fatCheck q r i j = true) (free : QFree D V q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V) (root : (outN D V u).card = r)
    (fat : r ≤ (layer D V 2 u).card) :
    2 * r ≤ (layer D V 2 u).card + (layer D V 3 u).card + 1 := by
  classical
  simp only [fatCheck, Bool.and_eq_true, decide_eq_true_eq] at check
  obtain ⟨⟨⟨hi, hj, hij, hr4⟩, wide⟩, even⟩ := check
  have hq : 4 ≤ q := by omega
  by_contra small
  push Not at small
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set F := frag D V u with hF
  have FV : F ⊆ V := frag_subset
  have fr : QFree D F q := free.mono_set FV
  have XF : X ⊆ F := subset_union_left
  have YF : Y ⊆ F := subset_union_right
  obtain ⟨e, he⟩ : ∃ e, Y.card = r + e := ⟨Y.card - r, by omega⟩
  have Fc : F.card = r + (r + e) := by
    have := frag_card (D := D) hu
    rw [← hF, ← hX, ← hY] at this
    omega
  have xdeg : ∀ x ∈ X, r ≤ (outN D F x).card := fun x hx => by
    rw [hF, x_in_frag free (by omega) hu hx]; exact deg x (outN_subset hx)
  have ydeg : ∀ y ∈ Y, e + 2 ≤ (outN D F y).card := fun y hy => by
    have h1 := y_in_frag free (by omega) hu hy
    have h2 := deg y (layer_subset hy)
    rw [← hF] at h1
    omega
  have memF : ∀ v ∈ F, v ∈ X ∨ v ∈ Y := fun v hv => mem_union.mp hv
  have disj : Disjoint X Y := frag_disj hu
  have fdeg : ∀ v ∈ F, e + 2 ≤ (outN D F v).card := fun v hv => by
    rcases memF v hv with h | h
    · have := xdeg v h; omega
    · exact ydeg v h
  have led := ReachLedger.ledger (D := D) (V := F) (i := i) (j := j) fr hij
  have sumF : ∑ v ∈ F, ((ball D F v i).card + (ball D F v j).card) =
      ∑ v ∈ X, ((ball D F v i).card + (ball D F v j).card) +
        ∑ v ∈ Y, ((ball D F v i).card + (ball D F v j).card) := sum_union disj
  rw [← sum_add_distrib, sumF, Fc] at led
  have xrow : ∀ x ∈ X, xB q r (e + 2) i + xB q r (e + 2) j ≤
      (ball D F x i).card + (ball D F x j).card := fun x hx => by
    have a := xB_sound fr (by omega) (by omega) fdeg (XF hx) (xdeg x hx) i (by omega)
    have b := xB_sound fr (by omega) (by omega) fdeg (XF hx) (xdeg x hx) j (by omega)
    omega
  have sx := sum_le_sum xrow
  rw [sum_const, smul_eq_mul, root] at sx
  rcases Nat.lt_or_ge 0 e with wideE | zero
  · ---- `|Y| = r + e`, `e ≥ 1`
    have yrow : ∀ y ∈ Y, yB q (e + 2) i + yB q (e + 2) j ≤
        (ball D F y i).card + (ball D F y j).card := fun y hy => by
      have a := yB_sound fr (by omega) (by omega) fdeg (YF hy) i (by omega)
      have b := yB_sound fr (by omega) (by omega) fdeg (YF hy) j (by omega)
      omega
    have sy := sum_le_sum yrow
    rw [sum_const, smul_eq_mul, he] at sy
    have w := List.all_eq_true.mp wide (e - 1) (List.mem_range.mpr (by omega))
    rw [show e - 1 + 1 = e by omega] at w
    have w' := of_decide_eq_true w
    omega
  · ---- `|Y| = r`
    obtain rfl : e = 0 := by omega
    have Yr : Y.card = r := by omega
    rw [show (0 : ℕ) + 2 = 2 from rfl] at sx
    set R := Y.filter (fun y => ∃ x ∈ X, D y x = true) with hR
    set Pt := (Y \ R).filter (fun c => ∃ y ∈ R, D c y = true) with hPt
    have RY : R ⊆ Y := filter_subset _ _
    have PtY : Pt ⊆ Y := (filter_subset _ _).trans sdiff_subset
    have xball : ∀ x ∈ X, ∀ k, k ≤ q → xB q r 2 k ≤ (ball D F x k).card := fun x hx =>
      xB_sound fr (by omega) le_rfl fdeg (XF hx) (xdeg x hx)
    have yball : ∀ y ∈ Y, ∀ k, k ≤ q → yB q 2 k ≤ (ball D F y k).card := fun y hy =>
      yB_sound fr (by omega) le_rfl fdeg (YF hy)
    -- a returner `y → x` and a row `c → y`
    have retk : ∀ y ∈ R, ∀ k, 1 ≤ k → k ≤ q → xB q r 2 (k - 1) + 1 ≤ (ball D F y k).card := by
      intro y hy k hk1 hkq
      obtain ⟨yY, x, hx, yx⟩ := mem_filter.mp hy
      have a := succ_card fr (YF yY) (XF hx) yx (j := k - 1) (j' := k) (by omega) (by omega)
      have := xball x hx (k - 1) (by omega)
      omega
    have ptrk : ∀ c ∈ Y, ∀ y ∈ R, D c y = true → ∀ k, 2 ≤ k → k ≤ q →
        xB q r 2 (k - 2) + 2 ≤ (ball D F c k).card := by
      intro c hc y hy cy k hk2 hkq
      have a := succ_card fr (YF hc) (YF (RY hy)) cy (j := k - 1) (j' := k) (by omega) (by omega)
      have b := retk y hy (k - 1) (by omega) (by omega)
      rw [show k - 1 - 1 = k - 2 by omega] at b
      omega
    have yrow : ∀ y ∈ Y, yB q 2 i + yB q 2 j + (if y ∈ R then retC q r i j else 0) +
        (if y ∈ Pt then ptrC q r i j else 0) ≤ (ball D F y i).card + (ball D F y j).card := by
      intro y hy
      have bi := yball y hy i (by omega)
      have bj := yball y hy j (by omega)
      by_cases yR : y ∈ R
      · have yP : y ∉ Pt := fun h => (mem_sdiff.mp (mem_filter.mp h).1).2 yR
        have ri := retk y yR i (by omega) (by omega)
        have rj := retk y yR j (by omega) (by omega)
        simp only [yR, yP, ↓reduceIte, retC]
        omega
      · by_cases yP : y ∈ Pt
        · obtain ⟨-, y', hy', yy'⟩ := mem_filter.mp yP
          have pi := ptrk y hy y' hy' yy' i hi (by omega)
          have pj := ptrk y hy y' hy' yy' j hj (by omega)
          simp only [yR, yP, ↓reduceIte, ptrC]
          omega
        · simp only [yR, yP, ↓reduceIte]
          omega
    have sy := sum_le_sum yrow
    have e1 : ∑ y ∈ Y, (if y ∈ R then retC q r i j else 0) = R.card * retC q r i j := by
      rw [sum_ite_mem, inter_eq_right.mpr RY, sum_const, smul_eq_mul]
    have e2 : ∑ y ∈ Y, (if y ∈ Pt then ptrC q r i j else 0) = Pt.card * ptrC q r i j := by
      rw [sum_ite_mem, inter_eq_right.mpr PtY, sum_const, smul_eq_mul]
    rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, e1, e2, Yr] at sy
    have budget : baseC q r i j + R.card * retC q r i j + Pt.card * ptrC q r i j ≤
        (r + r) * (r + r + 1) := by
      simp only [baseC]
      rw [show r + (r + 0) = r + r by omega] at led
      omega
    simp only [evenOK, decide_eq_true_eq] at even
    obtain ⟨c0, c1, c3, c2⟩ := even
    have keepY : ∀ c ∈ Y, c ∉ R → outN D F c ⊆ outN D Y c := by
      intro c hc cR w hw
      obtain ⟨wF, cw⟩ := mem_outN.mp hw
      rcases memF w wF with wX | wY
      · exact (cR (mem_filter.mpr ⟨hc, w, wX, cw⟩)).elim
      · exact mem_outN.mpr ⟨wY, cw⟩
    have ydeg2 : ∀ c ∈ Y, 2 ≤ (outN D F c).card := ydeg
    have frY : QFree D Y q := fr.mono_set YF
    rcases Nat.lt_or_ge R.card 1 with r0 | r1
    · -- no returner
      have R0 : R = ∅ := card_eq_zero.mp (by omega)
      have m2Y : ∀ c ∈ Y, 2 ≤ (outN D Y c).card := fun c hc =>
        (ydeg2 c hc).trans (card_le_card (keepY c hc (by rw [R0]; exact notMem_empty c)))
      have := order_deg frY (by omega) 2 le_rfl m2Y (card_pos.mp (by omega))
      omega
    rcases Nat.lt_or_ge R.card 2 with r1' | r2
    · -- one returner
      obtain ⟨y0, hR1⟩ := card_eq_one.mp (show R.card = 1 by omega)
      have y0R : y0 ∈ R := by rw [hR1]; exact mem_singleton_self _
      have y0Y := RY y0R
      set Y' := Y.erase y0 with hY'
      have Y'Y : Y' ⊆ Y := erase_subset _ _
      have notR : ∀ c ∈ Y', c ∉ R := fun c hc cR => by
        rw [hR1, mem_singleton] at cR; exact (mem_erase.mp hc).1 cR
      have deg1 : ∀ c ∈ Y', 1 ≤ (outN D Y' c).card := by
        intro c hc
        have h2 := (ydeg2 c (Y'Y hc)).trans (card_le_card (keepY c (Y'Y hc) (notR c hc)))
        have cover : outN D Y c ⊆ insert y0 (outN D Y' c) := by
          intro w hw
          obtain ⟨wY, cw⟩ := mem_outN.mp hw
          by_cases e : w = y0
          · exact e ▸ mem_insert_self _ _
          · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, wY⟩, cw⟩)
        have := (card_le_card cover).trans (card_insert_le _ _)
        omega
      have Y'c : Y'.card + 1 = r := by rw [hY', card_erase_add_one y0Y, Yr]
      have lc := lone_count (fr.mono_set (Y'Y.trans YF)) (by omega) deg1
        (card_pos.mp (by omega)) (by omega)
      have loneP : lone D Y' ⊆ Pt := by
        intro c hc
        obtain ⟨cY', one⟩ := mem_lone.mp hc
        have h2 := (ydeg2 c (Y'Y cY')).trans (card_le_card (keepY c (Y'Y cY') (notR c cY')))
        have cy0 : D c y0 = true := by
          by_contra n
          have sub : outN D Y c ⊆ outN D Y' c := by
            intro w hw
            obtain ⟨wY, cw⟩ := mem_outN.mp hw
            exact mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => n (e ▸ cw), wY⟩, cw⟩
          have := card_le_card sub
          omega
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨Y'Y cY', notR c cY'⟩, y0, y0R, cy0⟩
      have pc := card_le_card loneP
      have R1 : R.card = 1 := by omega
      rw [R1, one_mul] at budget
      have := Nat.mul_le_mul_right (ptrC q r i j) (show 2 * q + 3 - r ≤ Pt.card by omega)
      omega
    rcases Nat.lt_or_ge R.card 3 with r2' | r3
    · -- two returners
      have R2 : R.card = 2 := by omega
      rw [R2] at budget
      set Y'' := (Y \ R) \ Pt with hY''
      have Y''Y : Y'' ⊆ Y := sdiff_subset.trans sdiff_subset
      have Y''c : Y''.card + Pt.card + 2 = r := by
        have e1 : (Y \ R).card + 2 = r := by rw [card_sdiff_of_subset RY, R2]; omega
        have e2 := card_sdiff_add_card_eq_card (show Pt ⊆ Y \ R from filter_subset _ _)
        rw [hY'']
        omega
      have outside : ∀ c ∈ Y'', ∀ w ∈ outN D F c, w ∈ Y'' ∨ w ∈ Pt := by
        intro c hc w hw
        obtain ⟨c1, cP⟩ := mem_sdiff.mp hc
        obtain ⟨cY, cR⟩ := mem_sdiff.mp c1
        obtain ⟨wF, cw⟩ := mem_outN.mp hw
        have wY : w ∈ Y := (mem_outN.mp (keepY c cY cR hw)).1
        have wR : w ∉ R := fun wR => cP (mem_filter.mpr ⟨c1, w, wR, cw⟩)
        by_cases wP : w ∈ Pt
        · exact Or.inr wP
        · exact Or.inl (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨wY, wR⟩, wP⟩)
      rcases Nat.lt_or_ge Pt.card 1 with p0 | p1
      · have P0 : Pt = ∅ := card_eq_zero.mp (by omega)
        have m2Y : ∀ c ∈ Y'', 2 ≤ (outN D Y'' c).card := by
          intro c hc
          refine (ydeg2 c (Y''Y hc)).trans (card_le_card fun w hw => ?_)
          rcases outside c hc w hw with h | h
          · exact mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩
          · rw [P0] at h; exact absurd h (notMem_empty w)
        have := order_deg (fr.mono_set (Y''Y.trans YF)) (by omega) 2 le_rfl m2Y
          (card_pos.mp (by omega))
        omega
      rcases Nat.lt_or_ge Pt.card 2 with p1' | p2
      · obtain ⟨p, hP1⟩ := card_eq_one.mp (show Pt.card = 1 by omega)
        rw [show Pt.card = 1 by omega, one_mul] at budget
        rcases c2 with c2 | ⟨-, c2⟩
        · omega
        have pP : p ∈ Pt := by rw [hP1]; exact mem_singleton_self _
        have deg1 : ∀ c ∈ Y'', 1 ≤ (outN D Y'' c).card := by
          intro c hc
          have h2 := ydeg2 c (Y''Y hc)
          have cover : outN D F c ⊆ insert p (outN D Y'' c) := by
            intro w hw
            rcases outside c hc w hw with h | h
            · exact mem_insert_of_mem (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
            · rw [hP1, mem_singleton] at h; exact h ▸ mem_insert_self _ _
          have := (card_le_card cover).trans (card_insert_le _ _)
          omega
        have lc := lone_count (fr.mono_set (Y''Y.trans YF)) (by omega) deg1
          (card_pos.mp (by omega)) (by omega)
        have headp : ∀ c ∈ lone D Y'', D c p = true := by
          intro c cl
          obtain ⟨hc, one⟩ := mem_lone.mp cl
          have h2 := ydeg2 c (Y''Y hc)
          by_contra n
          have sub : outN D F c ⊆ outN D Y'' c := by
            intro w hw
            rcases outside c hc w hw with h | h
            · exact mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩
            · rw [hP1, mem_singleton] at h; exact (n (h ▸ (mem_outN.mp hw).2)).elim
          have := card_le_card sub
          omega
        obtain ⟨pYR, y1, y1R, py1⟩ := mem_filter.mp pP
        obtain ⟨y1Y, x1, x1X, y1x1⟩ := mem_filter.mp y1R
        have pY := PtY pP
        set L := lone D Y'' with hL
        set Out := insert y1 (insert p L) with hOut
        have pL : p ∉ L := fun h => (mem_sdiff.mp (lone_subset h)).2 pP
        have y1L : y1 ∉ insert p L := by
          intro h
          rcases mem_insert.mp h with e | h
          · exact (mem_sdiff.mp pYR).2 (e ▸ y1R)
          · exact (mem_sdiff.mp (mem_sdiff.mp (lone_subset h)).1).2 y1R
        have Outc : Out.card = L.card + 2 := by
          rw [hOut, card_insert_of_notMem y1L, card_insert_of_notMem pL]
        have OutF : Out ⊆ F :=
          insert_subset (YF y1Y) (insert_subset (YF pY) (lone_subset.trans (Y''Y.trans YF)))
        have avoid : ball D F x1 (q - 3) ⊆ F \ Out := by
          intro w hw
          obtain ⟨wF, m, hm, walk⟩ := mem_ball.mp hw
          refine mem_sdiff.mpr ⟨wF, fun wO => ?_⟩
          have x1F := XF x1X
          rcases mem_insert.mp wO with rfl | wO
          · exact fr x1 (m + 1) (by omega) (by omega) (walk.snoc x1F y1x1)
          rcases mem_insert.mp wO with rfl | wO
          · exact fr x1 (m + 1 + 1) (by omega) (by omega)
              ((walk.snoc (YF y1Y) py1).snoc x1F y1x1)
          · exact fr x1 (m + 1 + 1 + 1) (by omega) (by omega)
              (((walk.snoc (YF pY) (headp w wO)).snoc (YF y1Y) py1).snoc x1F y1x1)
        have := card_le_card avoid
        rw [card_sdiff_of_subset OutF, Fc, Outc] at this
        have := xball x1 x1X (q - 3) (by omega)
        have := card_le_card OutF
        rw [Fc, Outc] at this
        omega
      · have := Nat.mul_le_mul_right (ptrC q r i j) p2
        rcases c2 with c2 | ⟨c2, -⟩ <;> omega
    · have := Nat.mul_le_mul_right (retC q r i j) r3
      omega

/-- The instance `(q, r) = (5, 9)` of the generic check. -/
theorem fatCheck_5_9 : fatCheck 5 9 2 3 = true := by decide

end gen

/-- The generic pattern: wherever some radii pass `fatCheck`, `[r, r + e, ≤ r - 2 - e]` is dead. -/
def fatShortGX (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  fatOK q r && decide (2 ≤ ws.length ∧ r ≤ ws.getD 1 0 ∧
    ws.getD 1 0 + (if 3 ≤ ws.length then ws.getD 2 0 else last) + 2 ≤ 2 * r)

theorem fatShortGX_sound (q r : ℕ) : ShapeClimbX.SoundX q r (fatShortGX q r) := by
  intro D V u ws last free deg hu root exact bound h
  simp only [fatShortGX, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ok, len, w2, w3⟩ := h
  obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ok
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have main := fat_short hi free deg hu root (by omega)
  by_cases long : 3 ≤ ws.length
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    simp only [long, ↓reduceIte] at w3
    omega
  · simp only [long, ↓reduceIte] at w3
    have e : ws.length + 1 = 3 := by omega
    rw [e] at bound
    omega

/-! ### The width pattern -/

/-- The fat short pattern at `(q, r) = (5, 9)`: second width at least `9`, second plus third
width at most `16` (`[9, 9 + e, ≤ 7 - e]`). Slot convention of `ShapeClimbX.collarDip`. -/
def fatShortX (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (q = 5 ∧ r = 9 ∧ 2 ≤ ws.length ∧ 9 ≤ ws.getD 1 0 ∧
    ws.getD 1 0 + (if 3 ≤ ws.length then ws.getD 2 0 else last) ≤ 16)

theorem fatShortX_sound (q r : ℕ) : ShapeClimbX.SoundX q r (fatShortX q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨rfl, rfl, len, w2, w3⟩ := of_decide_eq_true h
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have main := fat_short_nine free deg hu root (by omega)
  by_cases long : 3 ≤ ws.length
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    simp only [long, ↓reduceIte] at w3
    omega
  · simp only [long, ↓reduceIte] at w3
    have e : ws.length + 1 = 3 := by omega
    rw [e] at bound
    omega

#print axioms order_deg
#print axioms grow_min
#print axioms two_sink
#print axioms succ_card
#print axioms fat_short_nine
#print axioms fatShort_nine
#print axioms no_44
#print axioms profile_45
#print axioms fatShortX_sound
#print axioms chainB_sound
#print axioms fat_short
#print axioms fatCheck_5_9
#print axioms fatShortGX_sound
end LeanCH.BR.FatShort
