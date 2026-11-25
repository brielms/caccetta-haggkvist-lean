import checkpoints.shen_extension.BankPrice
import checkpoints.shen_extension.AncestorRow

/-!
# Pointwise ball floors at cutoff `7`, degree `9`, from fragment budgets

Setting: `free : QFree D V 7`, every out-degree `9`, a root `u`. Balls are inclusive:
`b_k = |B_k(u)|`; layers `X, Y, Z, W, L5` are the layers `1 … 5` of `u`, so `b_1 = 10`,
`b_2 = 10 + |Y|`, `b_3 = b_2 + |Z|`, `b_4 = b_3 + |W|`, `b_5 = b_4 + |L5|` (the paper's
`f_k = b_k - 1`). No evaluated table: every floor is a fragment budget
(`ReachLedger.ledger` through `FragmentBudget.mixed_budget` / `fragment_budget`) with row floors
from `FragmentBudget.ordinary_floor`, `full_floor`, `FullRow.full_row`, `FullRow.ordinary_rows`.

## Generic (any `q`, any regular degree)

* `pb D V u m = B_m(u) \ {u}` (the punctured ball). `pb_heads`: heads of a row of `pb m` lie in
  `pb (m + 1)` (`m + 1 ≤ q`); `pb_full`: rows of `pb m` keep all heads in `pb m'`, `m < m'`;
  `pb_keep`: a row of `pb m` keeps at least `deg - (b_{m+1} - b_m)` heads in `pb m`.
* `lift`, `lift_succ`: a ball of `V` lying in `A` is a ball of `A`; one step further, its part
  in `A` is in the ball of `A`.
* `ball_in_pb`, `pb_reach_in`, `pb_reach`: a row of `pb a` and `a + j ≤ q`: its `j`-ball lies in
  `pb (a + j)`; inside the fragment `pb m` it keeps all of its global `j`-ball when
  `a + j ≤ m`, and all but the exits `b_{m+1} - b_m` when `a + j ≤ m + 1`.
* `near_full` (`q = 7` numbers, any fragment): rows one or two arcs before a full row.

## Instances (`q = 7`, `r = 9`), the paper's F-a … F-h

* F-a `f2_floor`: `18 ≤ b_2` (`ThinSuppliers.second_wide`).
* F-b `fat_three` (budget on `pb 2` at radii `(3, 4)`: `N (14 + 2t) + 90 ≤ N (N - 1)` with
  `t = 7 - |Z|`, `18 ≤ N ≤ 19 + t` is false, `ar_fat3`), `fat3_floor` (not thin: `27 ≤ b_3`),
  `f3_floor` (`26 ≤ b_3`), `b3_26` (`b_3 = 26` is thin with `|Z| = 8`).
* F-c `thin_return`: `BankPrice.thin_no_return` (no arc from layers `2 … 5` into `B_1(u)`).
* F-d `four_of_26`: `b_3 = 26 ⇒ 34 ≤ b_4` (`ThinSuppliers.tight_ball_four`).
* `p_three` (the fragment `pb 3`, exits `e = b_4 - b_3 ≤ 6`, every row keeps `3 + k`,
  `k = 6 - e`; floors `20 + 2k` ordinary, `28 + 2k` on `Y`, `2 (25 - e)` on `X`; budget
  `N (20 + 2k) + 226 ≤ N (N - 1)` with `N ≤ 28 + k`, false, `ar_three`):
  `b_4 ≤ 35 ⇒ b_3 + 7 ≤ b_4`.
* F-e `four_of_27`: `b_3 = 27 ⇒ 35 ≤ b_4` (thin `(8, 9)`: `chain_next`, the budget on `Y ∪ Z`;
  not thin `(9, 8)`: lower cutoff `SupplierFat54.w_big`).
* F-f `four_of_28`: `b_3 = 28 ⇒ 36 ≤ b_4` (thin `(8, 10)`: `chain_next`; not thin:
  `p_three` gives `e = 7`; budget on `pb 3`, `27` labels, floors `36` (`X`), `26` (`Y`),
  `14` (`Z`), `24` for a row of `Z` pointing to a full row, `23` for a row of `Z` pointing to
  that one: `324 + 26|Y| + 14(|Z| - 2) + 47 ≤ 702` is false, `ar_ff`).
* F-g `four_of_29`: `29 ≤ b_3 ⇒ 36 ≤ b_4` (`p_three`).
* `f4_floor`: `34 ≤ b_4`.
* F-h `p_four` / `f5_floor`: `41 ≤ b_5` (fragment `pb 4`, `k = 6 - (b_5 - b_4)`; floors
  `20 + 2k`, `28 + 2k` on layers `≤ 3`, `2 (25 - e)` on `Y`, `25 + 33 - e` on `X`; budget
  `N (20 + 2k) + 496 - 9k ≤ N (N - 1)` with `33 ≤ N ≤ 33 + k`, false, `ar_four`).
* `floors7 : TopRow.Floors7 D V`.
* Classification: `low_score` (`b_3 + b_4 ≤ 63`: either `b_3 = 26`, thin, `|Z| = 8`, `|W| ≥ 8`;
  or `b_3 = 27`, `b_4 ∈ {35, 36}`, thin `(8, 9)` or not thin `(9, 8)`), and
  `fat_saver_layers` (not thin, `b_3 + b_4 ≤ 62`: `(|Y|, |Z|, |W|) = (9, 8, 8)`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Floors7Row
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Profile54 (reach)
open ThinSuppliers (Thin)

variable {D : CH.Digraph} {q : ℕ} {V : Finset ℕ}

/-! ### Generic: punctured balls of a root as fragments -/

/-- The punctured `m`-ball of `u`. -/
noncomputable abbrev pb (D : CH.Digraph) (V : Finset ℕ) (u m : ℕ) : Finset ℕ :=
  (ball D V u m).erase u

theorem pb_sub {u m : ℕ} : pb D V u m ⊆ V := (erase_subset _ _).trans ball_subset

theorem pb_card {u m : ℕ} (hu : u ∈ V) : (pb D V u m).card + 1 = (ball D V u m).card :=
  Profile54.card_ball_erase hu

theorem pb_mono {u m m' : ℕ} (h : m ≤ m') : pb D V u m ⊆ pb D V u m' :=
  erase_subset_erase u (ball_mono_radius h)

/-- Heads of a row of `pb m` lie in `pb (m + 1)` (`m + 1 ≤ q`). -/
theorem pb_heads (free : QFree D V q) {u m m' : ℕ} (hu : u ∈ V) (hm' : m + 1 = m')
    (hm : m + 1 ≤ q) {v : ℕ} (hv : v ∈ pb D V u m) : outN D V v ⊆ pb D V u m' := by
  intro w hw
  subst hm'
  exact Profile54.step_erase free hu hm (mem_of_mem_erase hv) hw

/-- Rows of `pb m` keep all their heads in `pb m'`, `m < m'`, `m + 1 ≤ q`. -/
theorem pb_full (free : QFree D V q) {u m m' : ℕ} (hu : u ∈ V) (hmm : m + 1 ≤ m')
    (hm : m + 1 ≤ q) {v : ℕ} (hv : v ∈ pb D V u m) : outN D (pb D V u m') v = outN D V v :=
  Profile54.out_restrict pb_sub (fun _ hw => pb_mono hmm (pb_heads free hu rfl hm hv hw))

/-- A row of `pb m` keeps all but `b_{m+1} - b_m` of its heads in `pb m` (`m + 1 ≤ q`). -/
theorem pb_keep (free : QFree D V q) {u m m' : ℕ} (hu : u ∈ V) (hm' : m + 1 = m')
    (hm : m + 1 ≤ q) {v : ℕ} (hv : v ∈ pb D V u m) :
    (outN D V v).card ≤ (outN D (pb D V u m) v).card +
      ((ball D V u m').card - (ball D V u m).card) := by
  have sub : pb D V u m ⊆ pb D V u m' := pb_mono (by omega)
  have cover : outN D V v ⊆ pb D V u m ∪ (pb D V u m' \ pb D V u m) := by
    intro w hw
    by_cases h : w ∈ pb D V u m
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨pb_heads free hu hm' hm hv hw, h⟩)
  have k := FragmentBudget.keep_le cover
  rw [card_sdiff_of_subset sub] at k
  have c1 := pb_card (D := D) (u := u) (m := m) hu
  have c2 := pb_card (D := D) (u := u) (m := m') hu
  omega

/-- A ball of `V` inside `A` is a ball of `A`. -/
theorem lift {A : Finset ℕ} {v : ℕ} (hv : v ∈ V) :
    ∀ j, ball D V v j ⊆ A → ball D V v j ⊆ ball D A v j := by
  intro j
  induction j with
  | zero =>
    intro hA w hw
    rw [ShapeClimbRoot.ball_zero_eq hv] at hw
    rw [mem_singleton.mp hw]
    exact self_mem_ball (hA (self_mem_ball hv))
  | succ j ih =>
    intro hA w hw
    have sub : ball D V v j ⊆ A := (ball_mono_radius (Nat.le_succ j)).trans hA
    by_cases old : w ∈ ball D V v j
    · exact ball_mono_radius (Nat.le_succ j) (ih sub old)
    · obtain ⟨y, yb, yw⟩ := ball_succ_pred hv hw old
      exact ball_step (ih sub yb) (hA hw) yw

/-- One step past a ball of `V` inside `A`: the part in `A` is in the ball of `A`. -/
theorem lift_succ {A : Finset ℕ} {v j : ℕ} (hv : v ∈ V) (hA : ball D V v j ⊆ A) :
    ball D V v (j + 1) ∩ A ⊆ ball D A v (j + 1) := by
  intro w hw
  obtain ⟨wb, wA⟩ := mem_inter.mp hw
  by_cases old : w ∈ ball D V v j
  · exact ball_mono_radius (Nat.le_succ j) (lift hv j hA old)
  · obtain ⟨y, yb, yw⟩ := ball_succ_pred hv wb old
    exact ball_step (lift hv j hA yb) wA yw

/-- The `j`-ball of a row of `pb a` lies in `pb (a + j)` (`a + j ≤ q`). -/
theorem ball_in_pb (free : QFree D V q) {u a j v : ℕ} (hv : v ∈ pb D V u a) (haj : a + j ≤ q) :
    ball D V v j ⊆ pb D V u (a + j) := by
  obtain ⟨vu, vb⟩ := mem_erase.mp hv
  obtain ⟨-, i, hi, wi⟩ := mem_ball.mp vb
  intro w hw
  obtain ⟨wV, k, hk, wk⟩ := mem_ball.mp hw
  refine mem_erase.mpr ⟨fun e => ?_, mem_ball.mpr ⟨wV, i + k, by omega, wi.append wk⟩⟩
  rw [e] at wk
  rcases Nat.eq_zero_or_pos i with rfl | ipos
  · exact vu (FlatAtCutoff.walk_zero wi).symm
  · exact free u (i + k) (by omega) (by omega) (wi.append wk)

/-- A row of `pb a`, `a + j ≤ m`, `a + j ≤ q`: inside `pb m` it keeps its global `j`-ball. -/
theorem pb_reach_in (free : QFree D V q) {u a j m v : ℕ} (hu : u ∈ V) (hv : v ∈ pb D V u a)
    (haj : a + j ≤ m) (hq : a + j ≤ q) :
    (ball D V v j).card ≤ reach D (pb D V u m) j v + 1 := by
  have vV : v ∈ V := pb_sub hv
  have vm : v ∈ pb D V u m := pb_mono (by omega) hv
  have h : ball D V v j ⊆ pb D V u m := (ball_in_pb free hv hq).trans (pb_mono haj)
  have c := card_le_card (lift vV j h)
  have e1 := Profile54.card_ball_erase (D := D) (W := pb D V u m) (k := j) vm
  unfold reach
  omega

/-- A row of `pb a`, `a + j ≤ m + 1`, `a + j ≤ q`, `1 ≤ j`: inside `pb m` it keeps its global
`j`-ball except for the exits `b_{m+1} - b_m`. -/
theorem pb_reach (free : QFree D V q) {u a j m m' v : ℕ} (hu : u ∈ V) (hm' : m + 1 = m')
    (hv : v ∈ pb D V u a) (haj : a + j ≤ m + 1) (hq : a + j ≤ q) (hj : 1 ≤ j) :
    (ball D V v j).card ≤ reach D (pb D V u m) j v + 1 +
      ((ball D V u m').card - (ball D V u m).card) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have vV : v ∈ V := pb_sub hv
  have vm : v ∈ pb D V u m := pb_mono (by omega) hv
  have h1 : ball D V v j' ⊆ pb D V u m :=
    (ball_in_pb free hv (j := j') (by omega)).trans (pb_mono (by omega))
  have h2 : ball D V v (j' + 1) ⊆ pb D V u m' :=
    (ball_in_pb free hv (j := j' + 1) hq).trans (pb_mono (by omega))
  have cover : ball D V v (j' + 1) ⊆
      ball D (pb D V u m) v (j' + 1) ∪ (pb D V u m' \ pb D V u m) := by
    intro w hw
    by_cases wm : w ∈ pb D V u m
    · exact mem_union_left _ (lift_succ vV h1 (mem_inter.mpr ⟨hw, wm⟩))
    · exact mem_union_right _ (mem_sdiff.mpr ⟨h2 hw, wm⟩)
  have c := (card_le_card cover).trans (card_union_le _ _)
  rw [card_sdiff_of_subset (pb_mono (by omega))] at c
  have e1 := Profile54.card_ball_erase (D := D) (W := pb D V u m) (k := j' + 1) vm
  have c1 := pb_card (D := D) (V := V) (u := u) (m := m) hu
  have c2 := pb_card (D := D) (V := V) (u := u) (m := m') hu
  unfold reach
  omega

/-- A lower bound on a sum by a constant floor. -/
theorem low_sum {S : Finset ℕ} {c : ℕ → ℕ} {a : ℕ} (h : ∀ v ∈ S, a ≤ c v) :
    S.card * a ≤ ∑ v ∈ S, c v := by
  have := card_nsmul_le_sum S c a h
  rwa [smul_eq_mul] at this

/-- The pair-sum over `A` split at `B ⊆ A`. -/
theorem sum_split {F A B : Finset ℕ} (h : B ⊆ A) :
    ∑ v ∈ A, (reach D F 3 v + reach D F 4 v) =
      ∑ v ∈ A \ B, (reach D F 3 v + reach D F 4 v) + ∑ v ∈ B, (reach D F 3 v + reach D F 4 v) :=
  (sum_sdiff h).symm

/-- One row taken out of the pair-sum. -/
theorem sum_pick {F A : Finset ℕ} {a : ℕ} (h : a ∈ A) :
    ∑ v ∈ A, (reach D F 3 v + reach D F 4 v) =
      (reach D F 3 a + reach D F 4 a) + ∑ v ∈ A.erase a, (reach D F 3 v + reach D F 4 v) :=
  (add_sum_erase A (fun v => reach D F 3 v + reach D F 4 v) h).symm

/-- A floor on the pair-sum. -/
theorem low3 {F S : Finset ℕ} {a : ℕ} (h : ∀ v ∈ S, a ≤ reach D F 3 v + reach D F 4 v) :
    S.card * a ≤ ∑ v ∈ S, (reach D F 3 v + reach D F 4 v) :=
  low_sum h

/-- **Rows before a full row** (`q = 7` numbers, any fragment). In a `7`-free fragment of
minimum out-degree two, let `y0` have nine heads and `12 ≤ reach 3`. A row pointing to `y0` has
`24 ≤ reach 3 + reach 4` (`|B_2(y0)| ≥ 11`, `|B_3(y0)| ≥ 13`, one more each); a row pointing to
such a row has `23 ≤ reach 3 + reach 4`. -/
theorem near_full {F : Finset ℕ} (fr : QFree D F 7) (deg : ∀ v ∈ F, 2 ≤ (outN D F v).card)
    {y0 : ℕ} (hy : y0 ∈ F) (n9 : (outN D F y0).card = 9) (r3 : 12 ≤ reach D F 3 y0)
    {z0 : ℕ} (hz0 : z0 ∈ F) (a0 : D z0 y0 = true) :
    24 ≤ reach D F 3 z0 + reach D F 4 z0 ∧
      ∀ z1 ∈ F, D z1 z0 = true → 23 ≤ reach D F 3 z1 + reach D F 4 z1 := by
  have s2 := Profile54.head_second fr (by norm_num) hy (by rw [n9]; norm_num) deg
  rw [n9] at s2
  have b1 : (ball D F y0 1).card = (outN D F y0).card + 1 := ReachLedger.ball_one fr (by norm_num) hy
  rw [n9] at b1
  have e3 := Profile54.card_ball_erase (D := D) (W := F) (k := 3) hy
  have l1 : (ball D F y0 1).card + 1 ≤ (ball D F z0 2).card :=
    ReachLedger.head_ball_lt fr hz0 hy a0 (by norm_num)
  have l2 : (ball D F y0 2).card + 1 ≤ (ball D F z0 3).card :=
    ReachLedger.head_ball_lt fr hz0 hy a0 (by norm_num)
  have l3 : (ball D F y0 3).card + 1 ≤ (ball D F z0 4).card :=
    ReachLedger.head_ball_lt fr hz0 hy a0 (by norm_num)
  have z3 := Profile54.card_ball_erase (D := D) (W := F) (k := 3) hz0
  have z4 := Profile54.card_ball_erase (D := D) (W := F) (k := 4) hz0
  unfold reach at r3 ⊢
  refine ⟨by omega, fun z1 hz1 a1 => ?_⟩
  have m2 : (ball D F z0 2).card + 1 ≤ (ball D F z1 3).card :=
    ReachLedger.head_ball_lt fr hz1 hz0 a1 (by norm_num)
  have m3 : (ball D F z0 3).card + 1 ≤ (ball D F z1 4).card :=
    ReachLedger.head_ball_lt fr hz1 hz0 a1 (by norm_num)
  have w3 := Profile54.card_ball_erase (D := D) (W := F) (k := 3) hz1
  have w4 := Profile54.card_ball_erase (D := D) (W := F) (k := 4) hz1
  omega

/-! ### Arithmetic of the budgets (all numbers are here) -/

/-- F-b: `N (14 + 2t) + 90 ≤ N (N - 1)`, `t = 7 - e`, `18 ≤ N`, `N + e ≤ 26`: false. -/
theorem ar_fat3 (N e : ℕ) (lo : 18 ≤ N) (hi : N + e ≤ 26) (he : e ≤ 7)
    (fb : N * (2 * (3 + 4) + 2 * (7 - e)) + 2 * 9 * (9 + 3 - (3 + 4)) ≤ N * (N - 1)) :
    False := by
  have hN : N ≤ 26 := by omega
  interval_cases e <;> interval_cases N <;> omega

/-- `chain_next`: `|A ∪ B| = 8 + b`, `b ∈ {9, 10}`, `t = 7 - c`:
`(8 + b)(14 + 2t) + 80 ≤ (8 + b)(7 + b)` is false. -/
theorem ar_chain (b c : ℕ) (hb9 : 9 ≤ b) (hb10 : b ≤ 10) (hc : c ≤ 7)
    (fb : (8 + b) * (2 * (3 + 4) + 2 * (7 - c)) + 2 * 8 * (9 + 3 - (3 + 4)) ≤
      (8 + b) * (8 + b - 1)) : False := by
  interval_cases b <;> interval_cases c <;> omega

/-- `p_three`: `N = c1 + c2 + 9`, `k = 6 - e`:
`c1 (20 + 2k) + c2 (28 + 2k) + 18 (25 - e) ≤ N (N - 1)` with `c2 ≥ 8`, `25 ≤ N`, `N + e ≤ 34`
is false (`N (20 + 2k) + 226` against at most `N (N - 1)`, `(28 + k)(7 - k) ≤ 196`). -/
theorem ar_three (c1 c2 e : ℕ) (h2 : 8 ≤ c2) (lo : 25 ≤ c1 + c2 + 9) (hi : c1 + c2 + 9 + e ≤ 34)
    (he : e ≤ 6)
    (fb : c1 * (20 + 2 * (6 - e)) + c2 * (28 + 2 * (6 - e)) + 9 * (2 * (25 - e)) ≤
      (c1 + c2 + 9) * (c1 + c2 + 9 - 1)) : False := by
  obtain ⟨N, hN⟩ : ∃ N, N = c1 + c2 + 9 := ⟨_, rfl⟩
  rw [← hN] at fb lo hi
  have hN' : N ≤ 34 := by omega
  interval_cases e <;> interval_cases N <;> omega

/-- `p_four`: `N = c1 + c2 + c3 + 9`, `k = 6 - e`:
`c1 (20 + 2k) + c2 (28 + 2k) + c3 · 2(25 - e) + 9 (58 - e) ≤ N (N - 1)` with `c3 ≥ 8`,
`c2 + c3 + 9 ≥ 25`, `33 ≤ N`, `N + e ≤ 39` is false (`N (20 + 2k) + 496 - 9k` against at most
`N (N - 1)`, `(33 + k)(12 - k) ≤ 396`). -/
theorem ar_four (c1 c2 c3 e : ℕ) (h3 : 8 ≤ c3) (h23 : 25 ≤ c2 + c3 + 9)
    (lo : 33 ≤ c1 + c2 + c3 + 9) (hi : c1 + c2 + c3 + 9 + e ≤ 39) (he : e ≤ 6)
    (fb : c1 * (20 + 2 * (6 - e)) + c2 * (28 + 2 * (6 - e)) + c3 * (2 * (25 - e)) +
      9 * (58 - e) ≤ (c1 + c2 + c3 + 9) * (c1 + c2 + c3 + 9 - 1)) : False := by
  obtain ⟨N, hN⟩ : ∃ N, N = c1 + c2 + c3 + 9 := ⟨_, rfl⟩
  rw [← hN] at fb lo hi
  have hN' : N ≤ 39 := by omega
  interval_cases e <;> interval_cases N <;> omega

/-! ### F-a, F-b: the second and third balls -/

section floors
variable (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)

include free reg in
/-- Ball sizes by layers at `r = 9`. -/
theorem balls9 {u : ℕ} (hu : u ∈ V) :
    (ball D V u 1).card = 10 ∧ (ball D V u 2).card = (layer D V 2 u).card + 10 ∧
      (ball D V u 3).card = (layer D V 3 u).card + (layer D V 2 u).card + 10 ∧
      (ball D V u 4).card = (layer D V 4 u).card + (ball D V u 3).card ∧
      (ball D V u 5).card = (layer D V 5 u).card + (ball D V u 4).card := by
  have L := ThinSuppliers.balls_by_layers free (by norm_num) reg hu
  have h4 : (ball D V u 4).card = (layer D V 4 u).card + (ball D V u 3).card :=
    ShapeClimbRoot.card_ball_succ 3
  have h5 : (ball D V u 5).card = (layer D V 5 u).card + (ball D V u 4).card :=
    ShapeClimbRoot.card_ball_succ 4
  refine ⟨by omega, by omega, by omega, h4, h5⟩

include free reg in
/-- **F-a.** `18 ≤ |B_2(u)|`; thin iff equality. -/
theorem f2_floor {u : ℕ} (hu : u ∈ V) :
    18 ≤ (ball D V u 2).card ∧ (Thin D V 9 u ↔ (ball D V u 2).card = 18) := by
  have L := balls9 free reg hu
  have w := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  unfold Thin
  exact ⟨by omega, fun h => by omega, fun h => by omega⟩

include free reg in
/-- **F-b, the budget.** A root with `|B_2| ≥ 19` and `|B_3| ≤ 27` has `|B_2| = 19`,
`|B_3| = 27`. Fragment `pb 2 = X ∪ Y` (`N = b_2 - 1`), the nine full rows of `X`, every row
keeps `9 - |Z| = 2 + t`; `fragment_budget` at `(3, 4)`, then `ar_fat3`. -/
theorem fat_three {u : ℕ} (hu : u ∈ V) (b2 : 19 ≤ (ball D V u 2).card)
    (b3 : (ball D V u 3).card ≤ 27) :
    (ball D V u 3).card = 27 ∧ (ball D V u 2).card = 19 := by
  have L := balls9 free reg hu
  by_contra hne
  obtain ⟨e, he⟩ : ∃ e, e = (ball D V u 3).card - (ball D V u 2).card := ⟨_, rfl⟩
  have e7 : e ≤ 7 := by omega
  have c1 := pb_card (D := D) (u := u) (m := 1) hu
  have c2 := pb_card (D := D) (u := u) (m := 2) hu
  have deg : ∀ v ∈ pb D V u 2, 2 + (7 - e) ≤ (outN D (pb D V u 2) v).card := fun v hv => by
    have := pb_keep free hu (m := 2) (m' := 3) rfl (by norm_num) hv
    rw [reg v (pb_sub hv)] at this
    omega
  have full : ∀ x ∈ pb D V u 1, (outN D (pb D V u 2) x).card = 9 := fun x hx => by
    rw [pb_full free hu (m := 1) (m' := 2) (by norm_num) (by norm_num) hx, reg x (pb_sub hx)]
  have fb := FragmentBudget.fragment_budget (i := 3) (j := 4) (r := 9) (t := 7 - e)
    (Fs := pb D V u 1) (free.mono_set pb_sub) deg (pb_mono (by norm_num)) full (by norm_num)
    (by omega) le_rfl (by norm_num) (by norm_num)
  have p1 : (pb D V u 1).card = 9 := by omega
  rw [p1] at fb
  exact ar_fat3 _ e (by omega) (by omega) e7 fb

include free reg in
/-- **F-b.** A root that is not thin has `|B_3| ≥ 27`, and `|B_3| = 27` forces `|Y| = 9`,
`|Z| = 8`. -/
theorem fat3_floor {u : ℕ} (hu : u ∈ V) (nt : ¬ Thin D V 9 u) :
    27 ≤ (ball D V u 3).card ∧ ((ball D V u 3).card = 27 →
      (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8) := by
  have L := balls9 free reg hu
  obtain ⟨f2, iff⟩ := f2_floor free reg hu
  have b2 : 19 ≤ (ball D V u 2).card := by
    by_contra h
    exact nt (iff.mpr (by omega))
  refine ⟨?_, fun e => ?_⟩
  · by_contra h
    have := fat_three free reg hu b2 (by omega)
    omega
  · have := fat_three free reg hu b2 (by omega)
    omega

include free reg in
/-- **F-b.** `26 ≤ |B_3|` at every root. -/
theorem f3_floor {u : ℕ} (hu : u ∈ V) : 26 ≤ (ball D V u 3).card := by
  have L := balls9 free reg hu
  by_cases th : Thin D V 9 u
  · have := ThinSuppliers.third_wide free (by norm_num) reg hu th (by norm_num)
    unfold Thin at th
    omega
  · have := (fat3_floor free reg hu th).1
    omega

include free reg in
/-- **F-b.** `|B_3| = 26` is a thin root with `|Z| = 8`. -/
theorem b3_26 {u : ℕ} (hu : u ∈ V) (h : (ball D V u 3).card = 26) :
    Thin D V 9 u ∧ (layer D V 3 u).card = 8 := by
  have L := balls9 free reg hu
  have th : Thin D V 9 u := by
    by_contra nt
    have := (fat3_floor free reg hu nt).1
    omega
  refine ⟨th, ?_⟩
  unfold Thin at th
  omega

/-! ### F-c, F-d -/

include free reg in
/-- **F-c.** At a thin root no row of layers `2 … 5` points into `B_1(u)` (`BankPrice`). -/
theorem thin_return {u : ℕ} (hu : u ∈ V) (thin : Thin D V 9 u) {j : ℕ} (hj2 : 2 ≤ j)
    (hj5 : j ≤ 5) {v : ℕ} (hv : v ∈ layer D V j u) {w : ℕ} (hw : w ∈ ball D V u 1) :
    ¬ D v w = true :=
  BankPrice.thin_no_return free reg hu (by unfold Thin at thin; omega) hj2 hj5 hv hw

include free reg in
/-- **F-d.** `|B_3| = 26 ⇒ |B_4| ≥ 34`, and `|W| ≥ 8` (`ThinSuppliers.tight_ball_four`). -/
theorem four_of_26 {u : ℕ} (hu : u ∈ V) (h : (ball D V u 3).card = 26) :
    8 ≤ (layer D V 4 u).card ∧ 34 ≤ (ball D V u 4).card := by
  have L := balls9 free reg hu
  obtain ⟨th, z8⟩ := b3_26 free reg hu h
  have t := ThinSuppliers.tight_ball_four free (by norm_num) reg hu
    (show ThinSuppliers.TightR D V 9 u from ⟨th, by omega⟩) (by norm_num) (by norm_num)
  omega

/-! ### The chain step and the budget on `pb 3` -/

/-- **Chain step** (`q = 7`, `r = 9`). In a chain `A, B, C, E` with `|A| = 8` and
`9 ≤ |B| ≤ 10`: `8 ≤ |C|`. Budget on `A ∪ B`: the eight full rows of `A`, every row keeps
`9 - |C| = 2 + t` (`ar_chain`). -/
theorem chain_next {A B C E : Finset ℕ} (free : QFree D V 7)
    (ch : BankPrice.Chain D V 9 A B C E) (hA : A.card = 8) (hB9 : 9 ≤ B.card)
    (hB10 : B.card ≤ 10) : 8 ≤ C.card := by
  by_contra hC
  have FV : A ∪ B ⊆ V := union_subset ch.AV ch.BV
  have Fc : (A ∪ B).card = 8 + B.card := by rw [card_union_of_disjoint ch.dAB, hA]
  have fullA : ∀ v ∈ A, (outN D (A ∪ B) v).card = 9 := fun v hv => by
    rw [BankPrice.keep_out FV (ch.kA v hv), ch.degA v hv]
  have deg : ∀ v ∈ A ∪ B, 2 + (7 - C.card) ≤ (outN D (A ∪ B) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [fullA v h]; omega
    · have := FragmentBudget.keep_le (ch.kB v h)
      rw [ch.degB v h] at this
      omega
  have fb := FragmentBudget.fragment_budget (i := 3) (j := 4) (r := 9) (t := 7 - C.card)
    (Fs := A) (free.mono_set FV) deg subset_union_left fullA (by norm_num) (by rw [Fc]; omega)
    le_rfl (by norm_num) (by norm_num)
  rw [Fc, hA] at fb
  exact ar_chain B.card C.card hB9 hB10 (by omega) fb

include free reg in
/-- **The budget on `pb 3`.** If every row has `|B_3| ≥ 26` and `|B_4(u)| ≤ 35`, then
`|B_3(u)| + 7 ≤ |B_4(u)|`. Fragment `pb 3 = X ∪ Y ∪ Z`, exits `e = b_4 - b_3`; if `e ≤ 6` every
row keeps `3 + k` heads, `k = 6 - e`; floors on `reach 3 + reach 4`: `20 + 2k` (`ordinary_rows`),
`28 + 2k` on `Y` (`full_floor`, `full_row` with slack `1 + k`), `2 (25 - e)` on `X` (the global
three-ball of a row of `X` minus the exits); `ar_three`. -/
theorem p_three (f3 : ∀ v ∈ V, 26 ≤ (ball D V v 3).card) {u : ℕ} (hu : u ∈ V)
    (b4 : (ball D V u 4).card ≤ 35) : (ball D V u 3).card + 7 ≤ (ball D V u 4).card := by
  classical
  have L := balls9 free reg hu
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  have f3u := f3 u hu
  by_contra hlt
  obtain ⟨e, he⟩ : ∃ e, e = (ball D V u 4).card - (ball D V u 3).card := ⟨_, rfl⟩
  have e6 : e ≤ 6 := by omega
  have c1 := pb_card (D := D) (u := u) (m := 1) hu
  have c2 := pb_card (D := D) (u := u) (m := 2) hu
  have c3 := pb_card (D := D) (u := u) (m := 3) hu
  have fr : QFree D (pb D V u 3) 7 := free.mono_set pb_sub
  have deg : ∀ v ∈ pb D V u 3, 3 + (6 - e) ≤ (outN D (pb D V u 3) v).card := fun v hv => by
    have := pb_keep free hu (m := 3) (m' := 4) rfl (by norm_num) hv
    rw [reg v (pb_sub hv)] at this
    omega
  have deg' : ∀ v ∈ pb D V u 3, 2 + (1 + (6 - e)) ≤ (outN D (pb D V u 3) v).card :=
    fun v hv => by have := deg v hv; omega
  have s12 : pb D V u 1 ⊆ pb D V u 2 := pb_mono (by norm_num)
  have s23 : pb D V u 2 ⊆ pb D V u 3 := pb_mono (by norm_num)
  -- floors
  have fC1 : ∀ v ∈ pb D V u 3 \ pb D V u 2,
      20 + 2 * (6 - e) ≤ reach D (pb D V u 3) 3 v + reach D (pb D V u 3) 4 v := by
    intro v hv
    have := FullRow.ordinary_rows fr (by norm_num) deg (mem_sdiff.mp hv).1
    omega
  have fC2 : ∀ v ∈ pb D V u 2 \ pb D V u 1,
      28 + 2 * (6 - e) ≤ reach D (pb D V u 3) 3 v + reach D (pb D V u 3) 4 v := by
    intro v hv
    have v2 := (mem_sdiff.mp hv).1
    have full : (outN D (pb D V u 3) v).card = 9 := by
      rw [pb_full free hu (m := 2) (m' := 3) (by norm_num) (by norm_num) v2, reg v (pb_sub v2)]
    have a := FragmentBudget.full_floor fr (i := 3) (t := 1 + (6 - e)) le_rfl (by norm_num)
      (by norm_num) (by omega) deg' (s23 v2) full
    have b := FullRow.full_row fr (i := 4) (t := 1 + (6 - e)) le_rfl (by norm_num) (by omega)
      deg' (s23 v2) full
    omega
  have fC3 : ∀ x ∈ pb D V u 1,
      2 * (25 - e) ≤ reach D (pb D V u 3) 3 x + reach D (pb D V u 3) 4 x := by
    intro x hx
    have r := pb_reach free hu (a := 1) (j := 3) (m := 3) (m' := 4) rfl hx (by norm_num)
      (by norm_num) (by norm_num)
    have f := f3 x (pb_sub hx)
    have mono := FragmentBudget.reach_mono (D := D) (F := pb D V u 3) (x := x)
      (show 3 ≤ 4 by norm_num)
    omega
  -- the budget
  have mb := FragmentBudget.mixed_budget fr (i := 3) (j := 4) (by norm_num)
  have sA := sum_split (D := D) (F := pb D V u 3) s23
  have sB := sum_split (D := D) (F := pb D V u 3) s12
  have l1 := low3 fC1
  have l2 := low3 fC2
  have l3 := low3 fC3
  rw [card_sdiff_of_subset s23] at l1
  rw [card_sdiff_of_subset s12] at l2
  have p1 : (pb D V u 1).card = 9 := by omega
  rw [p1] at l2 l3
  obtain ⟨a1, ha1⟩ : ∃ a, a = (pb D V u 3).card - (pb D V u 2).card := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a, a = (pb D V u 2).card - 9 := ⟨_, rfl⟩
  have N : (pb D V u 3).card = a1 + a2 + 9 := by omega
  rw [← ha1] at l1
  rw [← ha2] at l2
  rw [N] at mb
  exact ar_three a1 a2 e (by omega) (by omega) (by omega) e6 (by omega)

include free reg in
/-- **F-e.** `|B_3| = 27 ⇒ |W| ≥ 8`, `|B_4| ≥ 35`. Thin `(8, 9)`: `chain_next` on the layers
`2 … 5` (`BankPrice.thin_chain`). Not thin `(9, 8)`: the lower cutoff `6` (`r = 6 + 3`),
`SupplierFat54.w_big` with `AncestorRow.lemma5_six`. -/
theorem four_of_27 {u : ℕ} (hu : u ∈ V) (h : (ball D V u 3).card = 27) :
    8 ≤ (layer D V 4 u).card ∧ 35 ≤ (ball D V u 4).card := by
  have L := balls9 free reg hu
  by_cases th : Thin D V 9 u
  · have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
    have w := chain_next free (BankPrice.thin_chain free reg hu y8) y8 (by omega) (by omega)
    omega
  · obtain ⟨y9, z8⟩ := (fat3_floor free reg hu th).2 h
    have free6 : QFree D V 6 := free.mono_bound (by norm_num)
    have ne := SupplierFat54.a_nonempty (AncestorRow.lemma5_six free6 reg hu y9)
    have w := SupplierFat54.w_big free6 hu le_rfl reg y9 z8 ne
    omega

include free reg in
/-- **F-g.** `29 ≤ |B_3| ⇒ 36 ≤ |B_4|` (`p_three`). -/
theorem four_of_29 {u : ℕ} (hu : u ∈ V) (h : 29 ≤ (ball D V u 3).card) :
    36 ≤ (ball D V u 4).card := by
  by_contra hlt
  have := p_three free reg (fun v hv => f3_floor free reg hv) hu (by omega)
  omega

include free reg in
/-- **F-d … F-g, the floor.** `34 ≤ |B_4|` at every root. -/
theorem f4_floor {u : ℕ} (hu : u ∈ V) : 34 ≤ (ball D V u 4).card := by
  have f3 := f3_floor free reg hu
  by_cases h26 : (ball D V u 3).card = 26
  · exact (four_of_26 free reg hu h26).2
  · by_contra hlt
    have := p_three free reg (fun v hv => f3_floor free reg hv) hu (by omega)
    omega

include free reg in
/-- **F-f.** `|B_3| = 28 ⇒ 36 ≤ |B_4|`. Thin `(8, 10)`: `chain_next`. Not thin: by `p_three`
the exits are exactly `7`; the fragment `pb 3` has `27` labels, every row keeps `2`; floors on
`reach 3 + reach 4`: `36` on `X` (`2 (26 - 1 - 7)`), `26` on `Y` (`12 + 14`), `14` on `Z`
(`6 + 8`). Some row `z0` of `Z` points into `X ∪ Y` (else `Z` keeps `2` heads in `Z`,
`BankPrice.keep_two`), and some other row `z1` of `Z` points into `X ∪ Y` or to `z0` (same
reason); `near_full` gives them `24` and `23`. Then `324 + 26|Y| + 14(|Z| - 2) + 47 ≤ 702`
contradicts `|Y| ≥ 9`. -/
theorem four_of_28 {u : ℕ} (hu : u ∈ V) (h : (ball D V u 3).card = 28) :
    36 ≤ (ball D V u 4).card := by
  classical
  have L := balls9 free reg hu
  by_cases th : Thin D V 9 u
  · have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
    have w := chain_next free (BankPrice.thin_chain free reg hu y8) y8 (by omega) (by omega)
    omega
  by_contra hlt
  have p3 := p_three free reg (fun v hv => f3_floor free reg hv) hu (by omega)
  have b4 : (ball D V u 4).card = 35 := by omega
  obtain ⟨f2, iff⟩ := f2_floor free reg hu
  have b2 : 19 ≤ (ball D V u 2).card := by
    by_contra h'
    exact th (iff.mpr (by omega))
  have c1 := pb_card (D := D) (u := u) (m := 1) hu
  have c2 := pb_card (D := D) (u := u) (m := 2) hu
  have c3 := pb_card (D := D) (u := u) (m := 3) hu
  have c4 := pb_card (D := D) (u := u) (m := 4) hu
  have fr : QFree D (pb D V u 3) 7 := free.mono_set pb_sub
  have Fc : (pb D V u 3).card = 27 := by omega
  have deg : ∀ v ∈ pb D V u 3, 2 ≤ (outN D (pb D V u 3) v).card := fun v hv => by
    have := pb_keep free hu (m := 3) (m' := 4) rfl (by norm_num) hv
    rw [reg v (pb_sub hv)] at this
    omega
  have deg0 : ∀ v ∈ pb D V u 3, 2 + 0 ≤ (outN D (pb D V u 3) v).card := fun v hv => deg v hv
  have s12 : pb D V u 1 ⊆ pb D V u 2 := pb_mono (by norm_num)
  have s23 : pb D V u 2 ⊆ pb D V u 3 := pb_mono (by norm_num)
  have s34 : pb D V u 3 ⊆ pb D V u 4 := pb_mono (by norm_num)
  have fullv : ∀ v ∈ pb D V u 2, (outN D (pb D V u 3) v).card = 9 := fun v hv => by
    rw [pb_full free hu (m := 2) (m' := 3) (by norm_num) (by norm_num) hv, reg v (pb_sub hv)]
  have r3full : ∀ v ∈ pb D V u 2, 12 ≤ reach D (pb D V u 3) 3 v := fun v hv =>
    FragmentBudget.full_floor fr (i := 3) (t := 0) le_rfl (by norm_num) (by norm_num)
      (by omega) deg0 (s23 hv) (fullv v hv)
  -- floors
  have fZ : ∀ v ∈ pb D V u 3 \ pb D V u 2,
      14 ≤ reach D (pb D V u 3) 3 v + reach D (pb D V u 3) 4 v := by
    intro v hv
    have a := FragmentBudget.ordinary_floor fr (i := 3) (t := 0) (by norm_num) (by norm_num)
      deg0 (mem_sdiff.mp hv).1
    have b := FragmentBudget.ordinary_floor fr (i := 4) (t := 0) (by norm_num) (by norm_num)
      deg0 (mem_sdiff.mp hv).1
    omega
  have fY : ∀ v ∈ pb D V u 2 \ pb D V u 1,
      26 ≤ reach D (pb D V u 3) 3 v + reach D (pb D V u 3) 4 v := by
    intro v hv
    have v2 := (mem_sdiff.mp hv).1
    have a := r3full v v2
    have b := FullRow.full_row fr (i := 4) (t := 0) le_rfl (by norm_num) (by omega)
      deg0 (s23 v2) (fullv v v2)
    omega
  have fX : ∀ x ∈ pb D V u 1,
      36 ≤ reach D (pb D V u 3) 3 x + reach D (pb D V u 3) 4 x := by
    intro x hx
    have r := pb_reach free hu (a := 1) (j := 3) (m := 3) (m' := 4) rfl hx (by norm_num)
      (by norm_num) (by norm_num)
    have f := f3_floor free reg (pb_sub hx)
    have mono := FragmentBudget.reach_mono (D := D) (F := pb D V u 3) (x := x)
      (show 3 ≤ 4 by norm_num)
    omega
  have Zc : (pb D V u 3 \ pb D V u 2).card = 28 - (ball D V u 2).card := by
    rw [card_sdiff_of_subset s23]; omega
  have Yc : (pb D V u 2 \ pb D V u 1).card = (ball D V u 2).card - 10 := by
    rw [card_sdiff_of_subset s12]; omega
  have p1 : (pb D V u 1).card = 9 := by omega
  -- the sums
  have mb := FragmentBudget.mixed_budget fr (i := 3) (j := 4) (by norm_num)
  rw [Fc] at mb
  have sA := sum_split (D := D) (F := pb D V u 3) s23
  have sB := sum_split (D := D) (F := pb D V u 3) s12
  have lX := low3 fX
  have lY := low3 fY
  have lZ := low3 fZ
  rw [p1] at lX
  rw [Yc] at lY
  rw [Zc] at lZ
  have y10 : (ball D V u 2).card ≤ 20 := by omega
  -- a row of `Z` pointing into `pb 2`
  have Zkeep : ∀ z ∈ pb D V u 3 \ pb D V u 2, ∀ w ∈ outN D V z,
      w ∈ pb D V u 2 ∨ w ∈ pb D V u 3 \ pb D V u 2 ∨ w ∈ pb D V u 4 \ pb D V u 3 := by
    intro z hz w hw
    have w4 := pb_heads free hu (m := 3) (m' := 4) rfl (by norm_num) (mem_sdiff.mp hz).1 hw
    by_cases wF : w ∈ pb D V u 3
    · by_cases w2 : w ∈ pb D V u 2
      · exact Or.inl w2
      · exact Or.inr (Or.inl (mem_sdiff.mpr ⟨wF, w2⟩))
    · exact Or.inr (Or.inr (mem_sdiff.mpr ⟨w4, wF⟩))
  have Wc : (pb D V u 4 \ pb D V u 3).card = 7 := by
    rw [card_sdiff_of_subset s34]; omega
  have ZV : pb D V u 3 \ pb D V u 2 ⊆ V := fun z hz => pb_sub (mem_sdiff.mp hz).1
  have Zne : (pb D V u 3 \ pb D V u 2).Nonempty := card_pos.mp (by omega)
  obtain ⟨z0, hz0, y0, hy0, a0⟩ : ∃ z0 ∈ pb D V u 3 \ pb D V u 2, ∃ y0 ∈ pb D V u 2,
      D z0 y0 = true := by
    by_contra none
    have := BankPrice.keep_two free (by norm_num) ZV Zne (fun v hv => reg v (ZV hv))
      (T := pb D V u 4 \ pb D V u 3) (fun z hz w hw => by
        rcases Zkeep z hz w hw with h1 | h1 | h1
        · exact (none ⟨z, hz, w, h1, (mem_outN.mp hw).2⟩).elim
        · exact mem_union_left _ h1
        · exact mem_union_right _ h1) (by omega)
    omega
  have Z'ne : ((pb D V u 3 \ pb D V u 2).erase z0).Nonempty :=
    card_pos.mp (by rw [card_erase_of_mem hz0]; omega)
  obtain ⟨z1, hz1, k1⟩ : ∃ z1 ∈ (pb D V u 3 \ pb D V u 2).erase z0,
      D z1 z0 = true ∨ ∃ y ∈ pb D V u 2, D z1 y = true := by
    by_contra none
    have := BankPrice.keep_two free (by norm_num) ((erase_subset _ _).trans ZV) Z'ne
      (fun v hv => reg v (ZV (mem_of_mem_erase hv))) (T := pb D V u 4 \ pb D V u 3)
      (fun z hz w hw => by
        rcases Zkeep z (mem_of_mem_erase hz) w hw with h1 | h1 | h1
        · exact (none ⟨z, hz, Or.inr ⟨w, h1, (mem_outN.mp hw).2⟩⟩).elim
        · refine mem_union_left _ (mem_erase.mpr ⟨fun e => ?_, h1⟩)
          rw [e] at hw
          exact (none ⟨z, hz, Or.inl (mem_outN.mp hw).2⟩).elim
        · exact mem_union_right _ h1) (by omega)
    rw [card_erase_of_mem hz0] at this
    omega
  have z0F : z0 ∈ pb D V u 3 := (mem_sdiff.mp hz0).1
  have z1Z : z1 ∈ pb D V u 3 \ pb D V u 2 := mem_of_mem_erase hz1
  have z1F : z1 ∈ pb D V u 3 := (mem_sdiff.mp z1Z).1
  have g0 := (near_full fr deg (s23 hy0) (fullv y0 hy0) (r3full y0 hy0) z0F a0).1
  have g1 : 23 ≤ reach D (pb D V u 3) 3 z1 + reach D (pb D V u 3) 4 z1 := by
    rcases k1 with a1 | ⟨y1, hy1, a1⟩
    · exact (near_full fr deg (s23 hy0) (fullv y0 hy0) (r3full y0 hy0) z0F a0).2 z1 z1F a1
    · have := (near_full fr deg (s23 hy1) (fullv y1 hy1) (r3full y1 hy1) z1F a1).1
      omega
  -- refine the sum over `Z`
  have e0 := sum_pick (D := D) (F := pb D V u 3) hz0
  have e1 := sum_pick (D := D) (F := pb D V u 3) hz1
  have lR := low3 (F := pb D V u 3) (S := ((pb D V u 3 \ pb D V u 2).erase z0).erase z1)
    (a := 14) (fun v hv => fZ v (mem_of_mem_erase (mem_of_mem_erase hv)))
  rw [card_erase_of_mem hz1, card_erase_of_mem hz0, Zc] at lR
  have : 2 ≤ 28 - (ball D V u 2).card := by omega
  omega


include free reg in
/-- **F-h, the budget on `pb 4`.** `41 ≤ |B_5|` at every root. Exits `e = b_5 - b_4`; if
`e ≤ 6`, `k = 6 - e`: floors `20 + 2k` (ordinary), `28 + 2k` (layers `≤ 3`, full),
`2 (25 - e)` on `Y` (global three-ball minus exits), `25 + 33 - e` on `X` (whole global
three-ball, global four-ball minus exits); `ar_four`. -/
theorem f5_floor {u : ℕ} (hu : u ∈ V) : 41 ≤ (ball D V u 5).card := by
  classical
  have L := balls9 free reg hu
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  have f3u := f3_floor free reg hu
  have f4u := f4_floor free reg hu
  by_contra hlt
  obtain ⟨e, he⟩ : ∃ e, e = (ball D V u 5).card - (ball D V u 4).card := ⟨_, rfl⟩
  have e6 : e ≤ 6 := by omega
  have c1 := pb_card (D := D) (u := u) (m := 1) hu
  have c2 := pb_card (D := D) (u := u) (m := 2) hu
  have c3 := pb_card (D := D) (u := u) (m := 3) hu
  have c4 := pb_card (D := D) (u := u) (m := 4) hu
  have fr : QFree D (pb D V u 4) 7 := free.mono_set pb_sub
  have deg : ∀ v ∈ pb D V u 4, 3 + (6 - e) ≤ (outN D (pb D V u 4) v).card := fun v hv => by
    have := pb_keep free hu (m := 4) (m' := 5) rfl (by norm_num) hv
    rw [reg v (pb_sub hv)] at this
    omega
  have deg' : ∀ v ∈ pb D V u 4, 2 + (1 + (6 - e)) ≤ (outN D (pb D V u 4) v).card :=
    fun v hv => by have := deg v hv; omega
  have s12 : pb D V u 1 ⊆ pb D V u 2 := pb_mono (by norm_num)
  have s23 : pb D V u 2 ⊆ pb D V u 3 := pb_mono (by norm_num)
  have s34 : pb D V u 3 ⊆ pb D V u 4 := pb_mono (by norm_num)
  have fC1 : ∀ v ∈ pb D V u 4 \ pb D V u 3,
      20 + 2 * (6 - e) ≤ reach D (pb D V u 4) 3 v + reach D (pb D V u 4) 4 v := by
    intro v hv
    have := FullRow.ordinary_rows fr (by norm_num) deg (mem_sdiff.mp hv).1
    omega
  have fC2 : ∀ v ∈ pb D V u 3 \ pb D V u 2,
      28 + 2 * (6 - e) ≤ reach D (pb D V u 4) 3 v + reach D (pb D V u 4) 4 v := by
    intro v hv
    have v3 := (mem_sdiff.mp hv).1
    have full : (outN D (pb D V u 4) v).card = 9 := by
      rw [pb_full free hu (m := 3) (m' := 4) (by norm_num) (by norm_num) v3, reg v (pb_sub v3)]
    have a := FragmentBudget.full_floor fr (i := 3) (t := 1 + (6 - e)) le_rfl (by norm_num)
      (by norm_num) (by omega) deg' (s34 v3) full
    have b := FullRow.full_row fr (i := 4) (t := 1 + (6 - e)) le_rfl (by norm_num) (by omega)
      deg' (s34 v3) full
    omega
  have fC3 : ∀ v ∈ pb D V u 2 \ pb D V u 1,
      2 * (25 - e) ≤ reach D (pb D V u 4) 3 v + reach D (pb D V u 4) 4 v := by
    intro v hv
    have v2 := (mem_sdiff.mp hv).1
    have r := pb_reach free hu (a := 2) (j := 3) (m := 4) (m' := 5) rfl v2 (by norm_num)
      (by norm_num) (by norm_num)
    have f := f3_floor free reg (pb_sub v2)
    have mono := FragmentBudget.reach_mono (D := D) (F := pb D V u 4) (x := v)
      (show 3 ≤ 4 by norm_num)
    omega
  have fC4 : ∀ x ∈ pb D V u 1,
      58 - e ≤ reach D (pb D V u 4) 3 x + reach D (pb D V u 4) 4 x := by
    intro x hx
    have r3 := pb_reach_in free hu (a := 1) (j := 3) (m := 4) hx (by norm_num) (by norm_num)
    have r4 := pb_reach free hu (a := 1) (j := 4) (m := 4) (m' := 5) rfl hx (by norm_num)
      (by norm_num) (by norm_num)
    have f3x := f3_floor free reg (pb_sub hx)
    have f4x := f4_floor free reg (pb_sub hx)
    omega
  have mb := FragmentBudget.mixed_budget fr (i := 3) (j := 4) (by norm_num)
  have sA := sum_split (D := D) (F := pb D V u 4) s34
  have sB := sum_split (D := D) (F := pb D V u 4) s23
  have sC := sum_split (D := D) (F := pb D V u 4) s12
  have l1 := low3 fC1
  have l2 := low3 fC2
  have l3 := low3 fC3
  have l4 := low3 fC4
  rw [card_sdiff_of_subset s34] at l1
  rw [card_sdiff_of_subset s23] at l2
  rw [card_sdiff_of_subset s12] at l3
  have p1 : (pb D V u 1).card = 9 := by omega
  rw [p1] at l3 l4
  obtain ⟨a1, ha1⟩ : ∃ a, a = (pb D V u 4).card - (pb D V u 3).card := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a, a = (pb D V u 3).card - (pb D V u 2).card := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a, a = (pb D V u 2).card - 9 := ⟨_, rfl⟩
  have N : (pb D V u 4).card = a1 + a2 + a3 + 9 := by omega
  rw [← ha1] at l1
  rw [← ha2] at l2
  rw [← ha3] at l3
  rw [N] at mb
  exact ar_four a1 a2 a3 e (by omega) (by omega) (by omega) (by omega) e6 (by omega)

/-! ### The floors and the classification -/

include free reg in
/-- **The floors at `q = 7`, `r = 9`.** -/
theorem floors7 : TopRow.Floors7 D V where
  f2 := fun _ hv => (f2_floor free reg hv).1
  f3 := fun _ hv => f3_floor free reg hv
  f4 := fun _ hv => f4_floor free reg hv
  f5 := fun _ hv => f5_floor free reg hv
  thin45 := fun _ hv th => BankPrice.a3_thin free reg hv (by unfold Thin at th; omega)
  fat3 := fun _ hv nt => (fat3_floor free reg hv nt).1

include free reg in
/-- **Classification.** `|B_3| + |B_4| ≤ 63` forces `|B_3| = 26` (thin, `|Z| = 8`,
`|W| ≥ 8`) or `|B_3| = 27`, `|B_4| ∈ {35, 36}`, thin with `|Z| = 9` or not thin with
`(|Y|, |Z|) = (9, 8)`. -/
theorem low_score {u : ℕ} (hu : u ∈ V)
    (S : (ball D V u 3).card + (ball D V u 4).card ≤ 63) :
    ((ball D V u 3).card = 26 ∧ Thin D V 9 u ∧ (layer D V 3 u).card = 8 ∧
        8 ≤ (layer D V 4 u).card) ∨
      ((ball D V u 3).card = 27 ∧ 35 ≤ (ball D V u 4).card ∧ (ball D V u 4).card ≤ 36 ∧
        ((Thin D V 9 u ∧ (layer D V 3 u).card = 9) ∨
          (¬ Thin D V 9 u ∧ (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8))) := by
  have L := balls9 free reg hu
  have f3 := f3_floor free reg hu
  have f4 := f4_floor free reg hu
  by_cases h26 : (ball D V u 3).card = 26
  · obtain ⟨th, z8⟩ := b3_26 free reg hu h26
    exact Or.inl ⟨h26, th, z8, (four_of_26 free reg hu h26).1⟩
  by_cases h27 : (ball D V u 3).card = 27
  · have f := (four_of_27 free reg hu h27).2
    refine Or.inr ⟨h27, f, by omega, ?_⟩
    by_cases th : Thin D V 9 u
    · refine Or.inl ⟨th, ?_⟩
      unfold Thin at th
      omega
    · exact Or.inr ⟨th, (fat3_floor free reg hu th).2 h27⟩
  by_cases h28 : (ball D V u 3).card = 28
  · have := four_of_28 free reg hu h28
    omega
  · have := four_of_29 free reg hu (by omega)
    omega

include free reg in
/-- **The fat savers at order `62`.** A root that is not thin with `|B_3| + |B_4| ≤ 62` has
layers `(|Y|, |Z|, |W|) = (9, 8, 8)` (so `|B_3| = 27`, `|B_4| = 35`). -/
theorem fat_saver_layers {u : ℕ} (hu : u ∈ V) (nt : ¬ Thin D V 9 u)
    (S : (ball D V u 3).card + (ball D V u 4).card ≤ 62) :
    (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8 ∧ (layer D V 4 u).card = 8 := by
  have L := balls9 free reg hu
  have f3 := (fat3_floor free reg hu nt).1
  have f4 := f4_floor free reg hu
  by_cases h27 : (ball D V u 3).card = 27
  · obtain ⟨y9, z8⟩ := (fat3_floor free reg hu nt).2 h27
    have w := (four_of_27 free reg hu h27).1
    omega
  · have := p_three free reg (fun v hv => f3_floor free reg hv) hu (by omega)
    omega

end floors

#print axioms pb_heads
#print axioms pb_full
#print axioms pb_keep
#print axioms lift
#print axioms lift_succ
#print axioms ball_in_pb
#print axioms pb_reach_in
#print axioms pb_reach
#print axioms near_full
#print axioms ar_fat3
#print axioms ar_chain
#print axioms ar_three
#print axioms ar_four
#print axioms f2_floor
#print axioms fat_three
#print axioms fat3_floor
#print axioms f3_floor
#print axioms b3_26
#print axioms thin_return
#print axioms four_of_26
#print axioms chain_next
#print axioms p_three
#print axioms four_of_27
#print axioms four_of_28
#print axioms four_of_29
#print axioms f4_floor
#print axioms f5_floor
#print axioms floors7
#print axioms low_score
#print axioms fat_saver_layers

end LeanCH.BR.Floors7Row
