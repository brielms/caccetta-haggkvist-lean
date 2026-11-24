import checkpoints.shen_extension.ReachLedgerCatalog
import checkpoints.shen_extension.ShortfallBridge

/-!
# The regular first layer and the third-layer floor

Lean 4.35.0. Every statement is generic in the graph `D`, the label set `V`, the cutoff `q`, the
degree `r`, the quotas `t`, `t'`, `d` and the bounds `σ`, `a`, `b`, `z`. No order, cutoff or degree
is fixed in this file.

Notation in the comments, for a root `v`: `X = (ball v 1).erase v` (first layer),
`Y = ball v 2 \ ball v 1` (second layer), `Z = ball v 3 \ ball v 2` (third layer),
`F = (ball v 2).erase v`. `lack v x = Y \ outN x` are the second-layer labels a row misses, and
`priv v A` are the third-layer labels all of whose second-layer parents lie in `A`.

## Boundary hosts
* `host_in`, `host_out`: a set of `q t + 1` labels, `q`-free, keeping `t` heads inside on every
  row, is in-regular (by the supplied boundary law) and therefore out-regular of degree `t`.

## Minimum outdegree and the second ball
* `sparse_row`: a `q`-free set has a row with at most `|N| - m` heads inside, for `m ≤ min(|N|, q)`.
* `second_ball_floor`: minimum outdegree `d ≤ q` gives every closed two-ball `2 d + 1` labels.

## Layers
* `layer_parent`, `first_parent`: a label of shell `k + 2` has a parent in shell `k + 1`.
* `lack_card`: `|lack v x| + deg x = |Y| + (heads of x inside X)` for every first-layer row.
* `transition`: if some first-layer row misses `y`, then (lower quota `t`, all rows of the first
  layer keeping `t` heads inside, `|X| ≤ q t + 1`) some such row has a first-layer head that heads `y`.
* `transition_ball`: such a row sees its internal two-ball, all of `Y`, and all of `Z` except the
  labels private to what it misses.
* `ordinary_bound`: rows of `Y` headed by every first-layer row head only `Y` and the non-private
  part of `Z`; with lower quota `t'` this bounds the private labels.
* `priv_sum`: private classes of distinct second-layer labels are disjoint.

## The regular first layer law
* `regular_witness`: a root whose first layer is a boundary host (order `q t + 1`, every row keeping
  `t` heads inside), with `|Y| + t = r + 1`, has a first head whose two-ball exceeds `σ` whenever
  `σ < 2t + 1 + |Y| + |Z|`, `|Z| < |Y| (2t + 1 + |Y| + |Z| - σ)` and
  `|Z| + t' + 1 < 2 (2t + 1 + |Y| + |Z| - σ) + r`, with `|Y| ≤ q t' + 2` and lower quota `t'`.

## The third-layer count
* `local_capacity`: closed two-balls of a `q`-free set (`q ≥ 4`) sum to at most `|F|(|F|+1)/2`.
* `first_row_local`, `second_row_local`, `returner_local`: the local two-balls in `F` of first-layer
  rows lose at most `|Z|`; second-layer rows keep `r - |Z|` heads in `F`; a second-layer row heading
  the first layer has `r + 2` labels in its local two-ball.
* `third_count`: the three bounds summed against the local capacity.
* `third_floor`: hence `b + z + 1 ≤ |ball v 3|` at a root with `|ball v 1| = r + 1`,
  `|ball v 2| = b`, whenever `(b - 1) b < 2 (r (a - z) + (b - r - 1)(2 d + 1))`, `d ≤ q`,
  `d + z ≤ r`, and every row has `a ≤ |ball · 2|`.
* `returner_exists`: if `|Y| ≤ q d'`, `d' + |Z| ≤ r` and lower quota `d'`, some row of `Y` heads `X`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.RegularFirstLayer
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### Boundary hosts -/

/-- A boundary host is in-regular, by the supplied boundary law. -/
theorem host_in {t : ℕ} (law : Closure.BoundaryHub.QBoundaryInRegular q t) {S : Finset ℕ}
    (free : QFree D S q) (size : S.card = q*t + 1) (paid : ∀ x ∈ S, t ≤ (outN D S x).card) :
    ∀ x ∈ S, (inN D S x).card = t :=
  law D S free size paid

/-- **Host regularity.** A boundary host keeps exactly `t` heads inside on every row. -/
theorem host_out {t : ℕ} (law : Closure.BoundaryHub.QBoundaryInRegular q t) {S : Finset ℕ}
    (free : QFree D S q) (size : S.card = q*t + 1) (paid : ∀ x ∈ S, t ≤ (outN D S x).card) :
    ∀ x ∈ S, (outN D S x).card = t := by
  have inn := host_in law free size paid
  have sum := BR45.sum_out_in D S
  have ins : ∑ x ∈ S, (inN D S x).card = ∑ _x ∈ S, t := sum_congr rfl inn
  rw [ins] at sum
  intro x hx
  exact ((sum_eq_sum_iff_of_le paid).mp sum.symm x hx).symm

/-! ### Minimum outdegree and the second ball -/

/-- A `q`-free set has a row with at most `|N| - m` heads inside, for `1 ≤ m ≤ min(|N|, q)`. -/
theorem sparse_row {N : Finset ℕ} {m : ℕ} (free : QFree D V q) (nv : N ⊆ V)
    (hm : m ≤ N.card) (hmq : m ≤ q) (m1 : 1 ≤ m) :
    ∃ a ∈ N, (outN D N a).card + m ≤ N.card := by
  classical
  obtain ⟨M, mn, mc⟩ := exists_subset_card_eq hm
  have mlive : M.Nonempty := card_pos.mp (by omega)
  by_contra! all
  have big := closed_chain free (mn.trans nv) mlive (fun x xm => by
    by_contra none
    have sub : outN D N x ⊆ N \ M := fun w hw =>
      mem_sdiff.mpr ⟨(mem_outN.mp hw).1, fun wm => none ⟨w, wm, (mem_outN.mp hw).2⟩⟩
    have c := card_le_card sub
    rw [card_sdiff_of_subset mn] at c
    have := all x (mn xm)
    omega)
  omega

/-- **Second-ball floor.** Minimum outdegree `d ≤ q` in a `q`-free set gives every closed two-ball
at least `2 d + 1` labels. -/
theorem second_ball_floor {d y : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hd : d ≤ q) (d1 : 1 ≤ d)
    (low : ∀ x ∈ V, d ≤ (outN D V x).card) (yv : y ∈ V) : 2*d + 1 ≤ (ball D V y 2).card := by
  classical
  have yN : y ∉ outN D V y := fun h => loopfree free (by omega) yv (mem_outN.mp h).2
  have nv : outN D V y ⊆ V := filter_subset _ _
  have dN := low y yv
  obtain ⟨a, aN, sparse⟩ := sparse_row (m := d) free nv dN hd d1
  obtain ⟨av, ya⟩ := mem_outN.mp aN
  have split := card_outN_union (D := D)
    (show Disjoint (outN D V y) (V \ outN D V y) from disjoint_sdiff) a
  rw [union_sdiff_of_subset nv] at split
  have da := low a av
  have yoff : y ∉ outN D (V \ outN D V y) a :=
    fun h => digonfree free hq yv av ya (mem_outN.mp h).2
  have sub : insert y (outN D V y ∪ outN D (V \ outN D V y) a) ⊆ ball D V y 2 := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact self_mem_ball yv
    rcases mem_union.mp hw with hw | hw
    · exact ball_mono_radius (show 1 ≤ 2 by omega)
        (ball_of_adj (mem_outN.mp hw).1 (mem_outN.mp hw).2)
    · obtain ⟨wm, aw⟩ := mem_outN.mp hw
      exact mem_ball.mpr ⟨(mem_sdiff.mp wm).1, 2, le_rfl,
        .step av ya (.step (mem_sdiff.mp wm).1 aw (.refl w))⟩
  have dis : Disjoint (outN D V y) (outN D (V \ outN D V y) a) :=
    disjoint_left.mpr (fun w h1 h2 => (mem_sdiff.mp (mem_outN.mp h2).1).2 h1)
  have notin : y ∉ outN D V y ∪ outN D (V \ outN D V y) a := by
    intro h
    rcases mem_union.mp h with h | h
    · exact yN h
    · exact yoff h
  have c := card_le_card sub
  rw [card_insert_of_notMem notin, card_union_of_disjoint dis] at c
  omega

/-! ### Layers -/

/-- A label of shell `k + 2` has a parent in shell `k + 1`. -/
theorem layer_parent {v w k : ℕ} (vv : v ∈ V)
    (hw : w ∈ ball D V v (k+2) \ ball D V v (k+1)) :
    ∃ p ∈ ball D V v (k+1) \ ball D V v k, D p w = true := by
  obtain ⟨wb, off⟩ := mem_sdiff.mp hw
  obtain ⟨wv, j, hj, walk⟩ := mem_ball.mp wb
  have jeq : j = k + 2 := by
    by_contra ne
    exact off (mem_ball.mpr ⟨wv, j, by omega, walk⟩)
  subst jeq
  obtain ⟨p, wp, _, pw⟩ := walk.unsnoc
  have pv : p ∈ V := by
    rcases wp.end_mem_or with e | h
    · rw [e]
      exact vv
    · exact h
  exact ⟨p, mem_sdiff.mpr ⟨mem_ball.mpr ⟨pv, k+1, le_rfl, wp⟩,
    fun pk => off (ball_step pk wv pw)⟩, pw⟩

/-- A second-layer label has a first-layer parent. -/
theorem first_parent {v y : ℕ} (vv : v ∈ V) (hy : y ∈ ball D V v 2 \ ball D V v 1) :
    ∃ x ∈ (ball D V v 1).erase v, D x y = true := by
  obtain ⟨p, hp, py⟩ := layer_parent (k := 0) vv hy
  obtain ⟨p1, p0⟩ := mem_sdiff.mp hp
  exact ⟨p, mem_erase.mpr ⟨fun e => p0 (by rw [e]; exact self_mem_ball vv), p1⟩, py⟩

/-- A label of the closed two-ball other than the root is in the first or the second layer. -/
theorem two_split {v w : ℕ} (hw : w ∈ ball D V v 2) (ne : w ≠ v) :
    w ∈ (ball D V v 1).erase v ∨ w ∈ ball D V v 2 \ ball D V v 1 := by
  by_cases h : w ∈ ball D V v 1
  · exact Or.inl (mem_erase.mpr ⟨ne, h⟩)
  · exact Or.inr (mem_sdiff.mpr ⟨hw, h⟩)

/-- A first-layer row has every head in the first or second layer. -/
theorem first_heads {v x w : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (vv : v ∈ V)
    (hx : x ∈ (ball D V v 1).erase v) (wv : w ∈ V) (xw : D x w = true) :
    w ∈ (ball D V v 1).erase v ∨ w ∈ ball D V v 2 \ ball D V v 1 := by
  have x1 := (mem_erase.mp hx).2
  refine two_split (ball_step x1 wv xw) (fun e => ?_)
  rw [e] at xw
  exact no_back_arc free vv x1 (by omega) xw

/-- The second ball of a first-layer row sits in the third ball of the root. -/
theorem ball_shift {v x w : ℕ} (hx : x ∈ ball D V v 1) (hw : w ∈ ball D V x 2) :
    w ∈ ball D V v 3 := by
  obtain ⟨_, i, hi, wi⟩ := mem_ball.mp hx
  obtain ⟨wv, j, hj, wj⟩ := mem_ball.mp hw
  exact mem_ball.mpr ⟨wv, i + j, by omega, wi.append wj⟩

/-! ### Omissions -/

/-- Second-layer labels that the row `x` does not head. -/
noncomputable def lack (D : CH.Digraph) (V : Finset ℕ) (v x : ℕ) : Finset ℕ :=
  (ball D V v 2 \ ball D V v 1) \ outN D V x

open Classical in
/-- Third-layer labels whose second-layer parents all lie in `A`. -/
noncomputable def priv (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (ball D V v 3 \ ball D V v 2).filter
    (fun z => ∀ y ∈ ball D V v 2 \ ball D V v 1, D y z = true → y ∈ A)

theorem lack_subset {v x : ℕ} : lack D V v x ⊆ ball D V v 2 \ ball D V v 1 := sdiff_subset

theorem priv_subset {v : ℕ} {A : Finset ℕ} : priv D V v A ⊆ ball D V v 3 \ ball D V v 2 :=
  filter_subset _ _

/-- **Omission count.** A first-layer row misses exactly `|Y| + (internal heads) - deg` labels. -/
theorem lack_card {v x : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (vv : v ∈ V)
    (hx : x ∈ (ball D V v 1).erase v) :
    (lack D V v x).card + (outN D V x).card
      = (ball D V v 2 \ ball D V v 1).card + (outN D ((ball D V v 1).erase v) x).card := by
  have xs : (ball D V v 1).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have split := card_outN_union (D := D)
    (show Disjoint ((ball D V v 1).erase v) (V \ (ball D V v 1).erase v) from disjoint_sdiff) x
  rw [union_sdiff_of_subset xs] at split
  have eq : outN D (V \ (ball D V v 1).erase v) x
      = (ball D V v 2 \ ball D V v 1) ∩ outN D V x := by
    ext w
    simp only [mem_inter, mem_outN, mem_sdiff]
    constructor
    · rintro ⟨⟨wv, wx⟩, xw⟩
      rcases first_heads free hq vv hx wv xw with h | h
      · exact absurd h wx
      · exact ⟨mem_sdiff.mp h, wv, xw⟩
    · rintro ⟨⟨w2, w1⟩, wv, xw⟩
      exact ⟨⟨wv, fun h => w1 (mem_erase.mp h).2⟩, xw⟩
  rw [eq] at split
  have part := card_sdiff_add_card_inter (ball D V v 2 \ ball D V v 1) (outN D V x)
  unfold lack
  omega

/-- **Transition row.** Let every row of the first layer keep `t` heads inside it, the first layer
having at most `q t + 1` labels. If some first-layer row misses the second-layer label `y`, some
row that misses `y` has a first-layer head that heads `y`. -/
theorem transition {t v y : ℕ} (none : NoHost q t) (free : QFree D V q) (vv : v ∈ V)
    (host : ((ball D V v 1).erase v).card ≤ q*t + 1)
    (paid : ∀ x ∈ (ball D V v 1).erase v, t ≤ (outN D ((ball D V v 1).erase v) x).card)
    (hy : y ∈ ball D V v 2 \ ball D V v 1)
    (miss : ∃ x ∈ (ball D V v 1).erase v, y ∈ lack D V v x) :
    ∃ x ∈ (ball D V v 1).erase v, y ∈ lack D V v x ∧
      ∃ x' ∈ (ball D V v 1).erase v, D x x' = true ∧ D x' y = true := by
  classical
  obtain ⟨p, pX, py⟩ := first_parent vv hy
  have xs : (ball D V v 1).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have cx : ((ball D V v 1).erase v).filter (fun x => y ∈ lack D V v x)
      ⊆ ((ball D V v 1).erase v).erase p := by
    intro x hx
    obtain ⟨xX, xo⟩ := mem_filter.mp hx
    refine mem_erase.mpr ⟨fun e => ?_, xX⟩
    rw [e] at xo
    exact (mem_sdiff.mp xo).2 (mem_outN.mpr ⟨(mem_sdiff.mp hy).1 |> ball_subset, py⟩)
  have small := card_le_card cx
  rw [card_erase_of_mem pX] at small
  obtain ⟨x0, x0X, x0o⟩ := miss
  obtain ⟨x, xC, short⟩ := fragment_row none free
    (S := ((ball D V v 1).erase v).filter (fun x => y ∈ lack D V v x))
    ((filter_subset _ _).trans xs) ⟨x0, mem_filter.mpr ⟨x0X, x0o⟩⟩ (by omega)
  obtain ⟨xX, xo⟩ := mem_filter.mp xC
  have pay := paid x xX
  obtain ⟨x', hx', off⟩ : ∃ x' ∈ outN D ((ball D V v 1).erase v) x,
      x' ∉ outN D (((ball D V v 1).erase v).filter (fun x => y ∈ lack D V v x)) x := by
    by_contra! all
    have := card_le_card (fun w hw => all w hw)
    omega
  obtain ⟨x'X, xx'⟩ := mem_outN.mp hx'
  refine ⟨x, xX, xo, x', x'X, xx', ?_⟩
  by_contra no
  exact off (mem_outN.mpr ⟨mem_filter.mpr ⟨x'X, mem_sdiff.mpr ⟨hy, fun h => no (mem_outN.mp h).2⟩⟩, xx'⟩)

/-- **Transition ball.** A first-layer row `x` with a head `x'` that heads every label `x` misses
sees its internal two-ball, the whole second layer, and every third-layer label not private to what
it misses. -/
theorem transition_ball {v x x' : ℕ}
    (hx : x ∈ (ball D V v 1).erase v) (x'v : x' ∈ V) (xx' : D x x' = true)
    (cover : lack D V v x ⊆ outN D V x') :
    (ball D ((ball D V v 1).erase v) x 2).card + (ball D V v 2 \ ball D V v 1).card
      + ((ball D V v 3 \ ball D V v 2).card - (priv D V v (lack D V v x)).card)
      ≤ (ball D V x 2).card := by
  classical
  have xs : (ball D V v 1).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have xv : x ∈ V := xs hx
  have inner : ball D ((ball D V v 1).erase v) x 2 ⊆ ball D V x 2 := by
    intro w hw
    obtain ⟨wX, j, hj, walk⟩ := mem_ball.mp hw
    exact mem_ball.mpr ⟨xs wX, j, hj, walk.mono xs⟩
  have second : ball D V v 2 \ ball D V v 1 ⊆ ball D V x 2 := by
    intro y hy
    have yv : y ∈ V := ball_subset (mem_sdiff.mp hy).1
    by_cases xy : D x y = true
    · exact ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj yv xy)
    · have yo : y ∈ lack D V v x := mem_sdiff.mpr ⟨hy, fun h => xy (mem_outN.mp h).2⟩
      have x'y := (mem_outN.mp (cover yo)).2
      exact mem_ball.mpr ⟨yv, 2, le_rfl, .step x'v xx' (.step yv x'y (.refl y))⟩
  have third : (ball D V v 3 \ ball D V v 2) \ priv D V v (lack D V v x) ⊆ ball D V x 2 := by
    intro z hz
    obtain ⟨hz3, hzp⟩ := mem_sdiff.mp hz
    have zv : z ∈ V := ball_subset (mem_sdiff.mp hz3).1
    have ex : ∃ y ∈ ball D V v 2 \ ball D V v 1, D y z = true ∧ y ∉ lack D V v x := by
      by_contra! all
      exact hzp (mem_filter.mpr ⟨hz3, fun y hy yz => all y hy yz⟩)
    obtain ⟨y, hy, yz, yo⟩ := ex
    have yv : y ∈ V := ball_subset (mem_sdiff.mp hy).1
    have xy : D x y = true := by
      by_contra no
      exact yo (mem_sdiff.mpr ⟨hy, fun h => no (mem_outN.mp h).2⟩)
    exact mem_ball.mpr ⟨zv, 2, le_rfl, .step yv xy (.step zv yz (.refl z))⟩
  have d12 : Disjoint (ball D ((ball D V v 1).erase v) x 2) (ball D V v 2 \ ball D V v 1) :=
    disjoint_left.mpr (fun w h1 h2 => (mem_sdiff.mp h2).2 (mem_erase.mp (ball_subset h1)).2)
  have d3 : Disjoint (ball D ((ball D V v 1).erase v) x 2 ∪ (ball D V v 2 \ ball D V v 1))
      ((ball D V v 3 \ ball D V v 2) \ priv D V v (lack D V v x)) := by
    refine disjoint_left.mpr (fun w h1 h2 => ?_)
    have off := (mem_sdiff.mp (mem_sdiff.mp h2).1).2
    rcases mem_union.mp h1 with h | h
    · exact off (ball_mono_radius (show 1 ≤ 2 by omega) (mem_erase.mp (ball_subset h)).2)
    · exact off (mem_sdiff.mp h).1
  have total := card_le_card (union_subset (union_subset inner second) third)
  rw [card_union_of_disjoint d3, card_union_of_disjoint d12,
    card_sdiff_of_subset priv_subset] at total
  exact total

/-- **Ordinary rows.** Let `K` hold every second-layer label missed by some first-layer row. A
second-layer row outside `K` heads only second-layer labels and third-layer labels not private to
`K`; with lower quota `t'` on at most `q t'` such rows, the private part of `Z` is bounded. -/
theorem ordinary_bound {t' r v : ℕ} (none : NoHost q t') (free : QFree D V q) (hq : 3 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card) (vv : v ∈ V) {K : Finset ℕ}
    (hK : ∀ x ∈ (ball D V v 1).erase v, lack D V v x ⊆ K)
    (live : ((ball D V v 2 \ ball D V v 1) \ K).Nonempty)
    (small : ((ball D V v 2 \ ball D V v 1) \ K).card ≤ q*t') :
    r + 1 + (priv D V v K).card ≤ t' + K.card + (ball D V v 3 \ ball D V v 2).card := by
  classical
  have ov : (ball D V v 2 \ ball D V v 1) \ K ⊆ V :=
    sdiff_subset.trans (sdiff_subset.trans ball_subset)
  obtain ⟨y, yO, short⟩ := fragment_row none free ov live small
  obtain ⟨hy, yK⟩ := mem_sdiff.mp yO
  have y2 := (mem_sdiff.mp hy).1
  have yv : y ∈ V := ball_subset y2
  have heads : outN D V y ⊆ (outN D ((ball D V v 2 \ ball D V v 1) \ K) y ∪ K)
      ∪ ((ball D V v 3 \ ball D V v 2) \ priv D V v K) := by
    intro w hw
    obtain ⟨wv, yw⟩ := mem_outN.mp hw
    have w3 : w ∈ ball D V v 3 := ball_step y2 wv yw
    have wne : w ≠ v := by
      intro e
      rw [e] at yw
      exact no_back_arc free vv y2 (by omega) yw
    by_cases w2 : w ∈ ball D V v 2
    · rcases two_split w2 wne with wX | wY
      · exfalso
        have wy : D w y = true := by
          by_contra no
          exact yK (hK w wX (mem_sdiff.mpr ⟨hy, fun h => no (mem_outN.mp h).2⟩))
        exact digonfree free (by omega) yv wv yw wy
      · by_cases wK : w ∈ K
        · exact mem_union_left _ (mem_union_right _ wK)
        · exact mem_union_left _ (mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨wY, wK⟩, yw⟩))
    · refine mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨w3, w2⟩, fun wp => ?_⟩)
      exact yK ((mem_filter.mp wp).2 y hy yw)
  have c := card_le_card heads
  have u1 := card_union_le (outN D ((ball D V v 2 \ ball D V v 1) \ K) y ∪ K)
    ((ball D V v 3 \ ball D V v 2) \ priv D V v K)
  have u2 := card_union_le (outN D ((ball D V v 2 \ ball D V v 1) \ K) y) K
  rw [card_sdiff_of_subset priv_subset] at u1
  have pz := card_le_card (priv_subset (D := D) (V := V) (v := v) (A := K))
  have dy := degree y yv
  omega

/-- **Private classes are disjoint.** Distinct second-layer labels have disjoint private classes,
all inside the private class of any set containing them. -/
theorem priv_sum {v : ℕ} (vv : v ∈ V) (K : Finset ℕ) :
    ∑ y ∈ K, (priv D V v {y}).card ≤ (priv D V v K).card := by
  classical
  have dis : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → Disjoint (priv D V v {a}) (priv D V v {b}) := by
    intro a _ b _ ne
    refine disjoint_left.mpr (fun z za zb => ne ?_)
    obtain ⟨z3, pa⟩ := mem_filter.mp za
    obtain ⟨_, pb⟩ := mem_filter.mp zb
    obtain ⟨p, hp, pz⟩ := layer_parent (k := 1) vv z3
    exact (mem_singleton.mp (pa p hp pz)).symm.trans (mem_singleton.mp (pb p hp pz))
  rw [← card_biUnion dis]
  refine card_le_card (fun z hz => ?_)
  obtain ⟨a, aK, za⟩ := mem_biUnion.mp hz
  obtain ⟨z3, pa⟩ := mem_filter.mp za
  exact mem_filter.mpr ⟨z3, fun y hy yz => by rw [mem_singleton.mp (pa y hy yz)]; exact aK⟩

/-! ### The regular first layer law -/

/-- **The regular first layer forces a wide first head.** Let `v` have first layer of `q t + 1`
labels keeping `t` heads inside on every row (a boundary host; in-regular by `law`), second layer
of `s` labels with `s + t = r + 1`, third layer of `z` labels, exact degree `r`, lower quotas `t`
and `t'` with `s ≤ q t' + 2`. With `A = 2 t + 1 + s + z - σ`, if `σ < 2 t + 1 + s + z`,
`z < s A` and `z + t' + 1 < 2 A + r`, some first head of `v` has a closed two-ball of more than
`σ` labels. -/
theorem regular_witness {t t' r s z σ v : ℕ} (free : QFree D V q) (hq : 3 ≤ q)
    (exact : ∀ x ∈ V, (outN D V x).card = r)
    (law : Closure.BoundaryHub.QBoundaryInRegular q t) (ht : t ≤ q) (t1 : 1 ≤ t)
    (none : NoHost q t) (none' : NoHost q t') (vv : v ∈ V)
    (host : ((ball D V v 1).erase v).card = q*t + 1)
    (paid : ∀ x ∈ (ball D V v 1).erase v, t ≤ (outN D ((ball D V v 1).erase v) x).card)
    (hs : (ball D V v 2 \ ball D V v 1).card = s) (hz : (ball D V v 3 \ ball D V v 2).card = z)
    (shell : s + t = r + 1) (quota : s ≤ q*t' + 2)
    (pos : σ < 2*t + 1 + s + z) (wide : z < s * (2*t + 1 + s + z - σ))
    (deep : z + t' + 1 < 2 * (2*t + 1 + s + z - σ) + r) :
    ∃ x ∈ (ball D V v 1).erase v, σ < (ball D V x 2).card := by
  classical
  obtain ⟨A, hA⟩ : ∃ A, A = 2*t + 1 + s + z - σ := ⟨_, rfl⟩
  rw [← hA] at wide deep
  have A1 : 1 ≤ A := by omega
  by_contra! cap
  have xs : (ball D V v 1).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have freeX : QFree D ((ball D V v 1).erase v) q := free.mono_set xs
  have reg := host_out law freeX host paid
  have inner : ∀ x ∈ (ball D V v 1).erase v,
      2*t + 1 ≤ (ball D ((ball D V v 1).erase v) x 2).card :=
    fun x hx => second_ball_floor freeX (by omega) ht t1 paid hx
  have one : ∀ x ∈ (ball D V v 1).erase v, (lack D V v x).card = 1 := by
    intro x hx
    have c := lack_card free (by omega) vv hx
    have e := exact x (xs hx)
    have rx := reg x hx
    omega
  obtain ⟨K, hK⟩ : ∃ K, K = ((ball D V v 1).erase v).biUnion (lack D V v) := ⟨_, rfl⟩
  have Ksub : ∀ x ∈ (ball D V v 1).erase v, lack D V v x ⊆ K := by
    intro x hx w hw
    rw [hK]
    exact mem_biUnion.mpr ⟨x, hx, hw⟩
  have KY : K ⊆ ball D V v 2 \ ball D V v 1 := by
    rw [hK]
    exact biUnion_subset.mpr (fun x _ => lack_subset)
  -- each omitted label has a private class of at least `A` labels
  have each : ∀ y ∈ K, A ≤ (priv D V v {y}).card := by
    intro y yK
    have miss : ∃ x ∈ (ball D V v 1).erase v, y ∈ lack D V v x := by
      rw [hK] at yK
      obtain ⟨x, hx, hy⟩ := mem_biUnion.mp yK
      exact ⟨x, hx, hy⟩
    obtain ⟨x, hx, yo, x', x'X, xx', x'y⟩ :=
      transition none free vv (by omega) paid (KY yK) miss
    obtain ⟨a, ha⟩ := card_eq_one.mp (one x hx)
    have ya : y = a := by
      rw [ha] at yo
      exact mem_singleton.mp yo
    have osing : lack D V v x = {y} := by rw [ha, ya]
    have cover : lack D V v x ⊆ outN D V x' := by
      rw [osing]
      exact singleton_subset_iff.mpr (mem_outN.mpr ⟨ball_subset (mem_sdiff.mp (KY yK)).1, x'y⟩)
    have tb := transition_ball hx (xs x'X) xx' cover
    rw [osing] at tb
    have ib := inner x hx
    have cx := cap x hx
    omega
  have sum : K.card * A ≤ (priv D V v K).card := by
    have s1 := sum_le_sum each
    rw [sum_const, smul_eq_mul] at s1
    exact s1.trans (priv_sum vv K)
  have pz := card_le_card (priv_subset (D := D) (V := V) (v := v) (A := K))
  have kY := card_le_card KY
  -- at least two labels are omitted
  have k2 : 2 ≤ K.card := by
    by_contra few
    obtain ⟨x0, hx0⟩ : ((ball D V v 1).erase v).Nonempty := card_pos.mp (by omega)
    obtain ⟨y0, hy0⟩ := card_pos.mp (show 0 < (lack D V v x0).card by rw [one x0 hx0]; omega)
    obtain ⟨p, pX, py⟩ := first_parent vv (KY (Ksub x0 hx0 hy0))
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (lack D V v p).card by rw [one p pX]; omega)
    have e : a = y0 := card_le_one.mp (by omega) a (Ksub p pX ha) y0 (Ksub x0 hx0 hy0)
    rw [e] at ha
    exact (mem_sdiff.mp ha).2 (mem_outN.mpr
      ⟨ball_subset (mem_sdiff.mp (KY (Ksub x0 hx0 hy0))).1, py⟩)
  have kA : 2 * A + (K.card - 2) ≤ K.card * A := by
    have split : K.card * A = (K.card - 2) * A + 2 * A := by
      rw [← Nat.add_mul, Nat.sub_add_cancel k2]
    have lo : (K.card - 2) * 1 ≤ (K.card - 2) * A := Nat.mul_le_mul_left _ A1
    omega
  have Ocard : ((ball D V v 2 \ ball D V v 1) \ K).card = s - K.card := by
    rw [card_sdiff_of_subset KY, hs]
  by_cases O : ((ball D V v 2 \ ball D V v 1) \ K).Nonempty
  · have ord := ordinary_bound none' free hq (fun x hx => (exact x hx).ge) vv Ksub O
      (by omega)
    omega
  · have empty : ((ball D V v 2 \ ball D V v 1) \ K).card = 0 := by
      rw [card_eq_zero]
      exact not_nonempty_iff_eq_empty.mp O
    have ks : K.card = s := by omega
    rw [ks] at sum
    omega

/-- **Regular first layer, regime form.** Exact degree `r = q t + 1`, a root `v` with
`|ball v 2| = 2 r + 2 - t` whose first layer keeps `t` heads inside on every row, third layer of
at least `z` labels, lower quotas `t`, `t'` with `r + 1 - t ≤ q t' + 2`, the boundary law at
`(q, t)`. Writing `A = r + t + 2 + z - σ`: if `σ < r + t + 2 + z`, `z < (r + 1 - t) A` and
`z + t' + 1 < 2 A + r`, then not every first head has a two-ball of at most `σ` labels. -/
theorem regular_regime {t t' r σ z v : ℕ} (free : QFree D V q) (hq : 3 ≤ q)
    (exact : ∀ x ∈ V, (outN D V x).card = r) (hr : r = q*t + 1)
    (law : Closure.BoundaryHub.QBoundaryInRegular q t) (ht : t ≤ q) (t1 : 1 ≤ t)
    (none : NoHost q t) (none' : NoHost q t') (vv : v ∈ V)
    (two : (ball D V v 2).card = 2*r + 2 - t)
    (paid : ∀ x ∈ (ball D V v 1).erase v, t ≤ (outN D ((ball D V v 1).erase v) x).card)
    (third : z ≤ (ball D V v 3 \ ball D V v 2).card) (quota : r + 1 - t ≤ q*t' + 2)
    (pos : σ < r + t + 2 + z) (wide : z < (r + 1 - t) * (r + t + 2 + z - σ))
    (deep : z + t' + 1 < 2 * (r + t + 2 + z - σ) + r)
    (cap : ∀ x ∈ (ball D V v 1).erase v, (ball D V x 2).card ≤ σ) : False := by
  have one := ball_one free (by omega) vv
  rw [exact v vv] at one
  have tq : t ≤ q*t := Nat.le_mul_of_pos_left t (by omega)
  have host : ((ball D V v 1).erase v).card = q*t + 1 := by
    rw [card_erase_of_mem (self_mem_ball vv), one]
    omega
  have i12 : ball D V v 1 ⊆ ball D V v 2 := ball_mono_radius (by omega)
  have hs : (ball D V v 2 \ ball D V v 1).card = r + 1 - t := by
    rw [card_sdiff_of_subset i12, one, two]
    omega
  have e : 2*t + 1 + (r + 1 - t) + (ball D V v 3 \ ball D V v 2).card - σ
      = (r + t + 2 + z - σ) + ((ball D V v 3 \ ball D V v 2).card - z) := by omega
  have grow : (r + 1 - t) * (r + t + 2 + z - σ) + ((ball D V v 3 \ ball D V v 2).card - z)
      ≤ (r + 1 - t) * (2*t + 1 + (r + 1 - t) + (ball D V v 3 \ ball D V v 2).card - σ) := by
    rw [e, Nat.mul_add]
    have : ((ball D V v 3 \ ball D V v 2).card - z) * 1
        ≤ ((ball D V v 3 \ ball D V v 2).card - z) * (r + 1 - t) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm ((ball D V v 3 \ ball D V v 2).card - z) (r + 1 - t)] at this
    omega
  obtain ⟨x, hx, big⟩ := regular_witness (σ := σ) free hq exact law ht t1 none none' vv host paid
    hs rfl (by omega) quota (by omega) (by omega) (by omega)
  have := cap x hx
  omega

/-! ### The third-layer count -/

/-- **Local capacity.** In a `q`-free set with `q ≥ 4`, the closed two-balls sum to at most
`|F| (|F| + 1) / 2`. -/
theorem local_capacity (free : QFree D V q) (hq : 4 ≤ q) {F : Finset ℕ} (fv : F ⊆ V) :
    2 * ∑ x ∈ F, (ball D F x 2).card ≤ F.card * (F.card + 1) := by
  have total := ledger (D := D) (V := F) (i := 2) (j := 2) (free.mono_set fv) (by omega)
  omega

/-- The punctured two-ball is the first layer and the second layer. -/
theorem punctured_split {v : ℕ} :
    (ball D V v 2).erase v = (ball D V v 1).erase v ∪ (ball D V v 2 \ ball D V v 1) := by
  ext w
  simp only [mem_erase, mem_union, mem_sdiff]
  constructor
  · rintro ⟨ne, w2⟩
    by_cases w1 : w ∈ ball D V v 1
    · exact Or.inl ⟨ne, w1⟩
    · exact Or.inr ⟨w2, w1⟩
  · rintro (⟨ne, w1⟩ | ⟨w2, w1⟩)
    · exact ⟨ne, ball_mono_radius (show 1 ≤ 2 by omega) w1⟩
    · refine ⟨fun e => w1 ?_, w2⟩
      have wv := ball_subset w2
      rw [e] at wv ⊢
      exact self_mem_ball wv

/-- **First rows, locally.** A first-layer row loses at most the third layer from its two-ball
when the walks are confined to the punctured two-ball of the root. -/
theorem first_row_local {v x : ℕ} (free : QFree D V q) (hq : 3 ≤ q) (vv : v ∈ V)
    (hx : x ∈ (ball D V v 1).erase v) :
    (ball D V x 2).card ≤ (ball D ((ball D V v 2).erase v) x 2).card
      + (ball D V v 3 \ ball D V v 2).card := by
  classical
  have x1 := (mem_erase.mp hx).2
  have xF : x ∈ (ball D V v 2).erase v :=
    mem_erase.mpr ⟨(mem_erase.mp hx).1, ball_mono_radius (show 1 ≤ 2 by omega) x1⟩
  have headF : ∀ w ∈ V, D x w = true → w ∈ (ball D V v 2).erase v := by
    intro w wv xw
    rcases first_heads free (by omega) vv hx wv xw with h | h
    · exact mem_erase.mpr ⟨(mem_erase.mp h).1, ball_mono_radius (show 1 ≤ 2 by omega) (mem_erase.mp h).2⟩
    · exact mem_erase.mpr ⟨fun e => (mem_sdiff.mp h).2 (by rw [e]; exact self_mem_ball vv),
        (mem_sdiff.mp h).1⟩
  have sub : ball D V x 2 ⊆ ball D ((ball D V v 2).erase v) x 2 ∪ (ball D V v 3 \ ball D V v 2) := by
    intro w hw
    by_cases w2 : w ∈ ball D V v 2
    · refine mem_union_left _ ?_
      have wne : w ≠ v := by
        intro e
        obtain ⟨_, j, hj, walk⟩ := mem_ball.mp hw
        obtain ⟨_, i, hi, wi⟩ := mem_ball.mp x1
        rw [e] at walk
        match i, hi, wi with
        | 0, _, wi =>
          cases wi
          exact (mem_erase.mp hx).1 rfl
        | 1, _, wi =>
          exact free v (1 + j) (by omega) (by omega) (wi.append walk)
        | n + 2, hi, _ => omega
      obtain ⟨wv, j, hj, walk⟩ := mem_ball.mp hw
      have wF : w ∈ (ball D V v 2).erase v := mem_erase.mpr ⟨wne, w2⟩
      match j, hj, walk with
      | 0, _, walk =>
        cases walk
        exact self_mem_ball xF
      | 1, _, walk =>
        cases walk with
        | step _ arc rest =>
          cases rest
          exact mem_ball.mpr ⟨wF, 1, by omega, .step wF arc (.refl w)⟩
      | 2, _, walk =>
        cases walk with
        | step av arc rest =>
          cases rest with
          | step _ arc2 rest2 =>
            cases rest2
            exact mem_ball.mpr ⟨wF, 2, le_rfl,
              .step (headF _ av arc) arc (.step wF arc2 (.refl w))⟩
      | n + 3, hj, _ => omega
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_shift x1 hw, w2⟩)
  exact (card_le_card sub).trans (card_union_le _ _)

/-- **Second rows, locally.** A second-layer row keeps all its heads outside the third layer in the
punctured two-ball. -/
theorem second_row_local {r v y : ℕ} (free : QFree D V q) (hq : 3 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card) (vv : v ∈ V)
    (hy : y ∈ ball D V v 2 \ ball D V v 1) :
    r ≤ (outN D ((ball D V v 2).erase v) y).card + (ball D V v 3 \ ball D V v 2).card := by
  classical
  have y2 := (mem_sdiff.mp hy).1
  have sub : outN D V y ⊆ outN D ((ball D V v 2).erase v) y ∪ (ball D V v 3 \ ball D V v 2) := by
    intro w hw
    obtain ⟨wv, yw⟩ := mem_outN.mp hw
    by_cases w2 : w ∈ ball D V v 2
    · refine mem_union_left _ (mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => ?_, w2⟩, yw⟩)
      rw [e] at yw
      exact no_back_arc free vv y2 (by omega) yw
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_step y2 wv yw, w2⟩)
  have := degree y (ball_subset y2)
  have c := (card_le_card sub).trans (card_union_le _ _)
  omega

/-- **Returning rows, locally.** A second-layer row that heads a first-layer row sees, inside the
punctured two-ball, itself, that row and all of its heads. -/
theorem returner_local {r v y x : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card) (vv : v ∈ V)
    (hy : y ∈ ball D V v 2 \ ball D V v 1) (hx : x ∈ (ball D V v 1).erase v)
    (yx : D y x = true) :
    r + 2 ≤ (ball D ((ball D V v 2).erase v) y 2).card := by
  classical
  have xs : (ball D V v 1).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have xv := xs hx
  have yv : y ∈ V := ball_subset (mem_sdiff.mp hy).1
  have toF : ∀ w, w ∈ (ball D V v 1).erase v ∨ w ∈ ball D V v 2 \ ball D V v 1 →
      w ∈ (ball D V v 2).erase v := by
    intro w h
    rw [punctured_split]
    exact mem_union.mpr h
  have yF := toF y (Or.inr hy)
  have xF := toF x (Or.inl hx)
  have sub : insert y (insert x (outN D V x)) ⊆ ball D ((ball D V v 2).erase v) y 2 := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact self_mem_ball yF
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact mem_ball.mpr ⟨xF, 1, by omega, .step xF yx (.refl x)⟩
    · obtain ⟨wv, xw⟩ := mem_outN.mp hw
      have wF := toF w (first_heads free hq vv hx wv xw)
      exact mem_ball.mpr ⟨wF, 2, le_rfl, .step xF yx (.step wF xw (.refl w))⟩
  have xn : x ∉ outN D V x := fun h => loopfree free (by omega) xv (mem_outN.mp h).2
  have yn : y ∉ insert x (outN D V x) := by
    intro h
    rcases mem_insert.mp h with e | h
    · rw [e] at yx
      exact loopfree free (by omega) xv yx
    · exact digonfree free hq yv xv yx (mem_outN.mp h).2
  have c := card_le_card sub
  rw [card_insert_of_notMem yn, card_insert_of_notMem xn] at c
  have := degree x xv
  omega

/-- **Third-layer count.** Let every row have `a ≤ |ball · 2|`, let `d ≤ q` with `d + |Z| ≤ r`,
and let `R` be second-layer rows that each head the first layer. Then
`2 (|X| (a - |Z|) + (|Y| - |R|)(2 d + 1) + |R| (r + 2)) ≤ |F| (|F| + 1)`. -/
theorem third_count {r a d v : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card) (floor : ∀ x ∈ V, a ≤ (ball D V x 2).card)
    (vv : v ∈ V) (hd : d ≤ q) (d1 : 1 ≤ d) (low : d + (ball D V v 3 \ ball D V v 2).card ≤ r)
    {R : Finset ℕ} (hR : R ⊆ ball D V v 2 \ ball D V v 1)
    (ret : ∀ y ∈ R, ∃ x ∈ (ball D V v 1).erase v, D y x = true) :
    2 * (((ball D V v 1).erase v).card * (a - (ball D V v 3 \ ball D V v 2).card)
        + ((ball D V v 2 \ ball D V v 1).card - R.card) * (2*d + 1) + R.card * (r + 2))
      ≤ ((ball D V v 2).erase v).card * (((ball D V v 2).erase v).card + 1) := by
  classical
  have fv : (ball D V v 2).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have cap := local_capacity free hq fv
  have freeF : QFree D ((ball D V v 2).erase v) q := free.mono_set fv
  -- minimum outdegree `d` in `F`
  have minF : ∀ x ∈ (ball D V v 2).erase v, d ≤ (outN D ((ball D V v 2).erase v) x).card := by
    intro x hx
    rw [punctured_split] at hx
    rcases mem_union.mp hx with hx | hx
    · have sub : outN D V x ⊆ outN D ((ball D V v 2).erase v) x := by
        intro w hw
        obtain ⟨wv, xw⟩ := mem_outN.mp hw
        refine mem_outN.mpr ⟨?_, xw⟩
        rw [punctured_split]
        exact mem_union.mpr (first_heads free (by omega) vv hx wv xw)
      have := card_le_card sub
      have := degree x (fv (by rw [punctured_split]; exact mem_union_left _ hx))
      omega
    · have := second_row_local free (by omega) degree vv hx
      omega
  have dis : Disjoint ((ball D V v 1).erase v) (ball D V v 2 \ ball D V v 1) :=
    disjoint_left.mpr (fun w h1 h2 => (mem_sdiff.mp h2).2 (mem_erase.mp h1).2)
  rw [punctured_split, sum_union dis, card_union_of_disjoint dis] at cap
  have hX : ∑ _x ∈ (ball D V v 1).erase v, (a - (ball D V v 3 \ ball D V v 2).card)
      ≤ ∑ x ∈ (ball D V v 1).erase v,
        (ball D ((ball D V v 1).erase v ∪ (ball D V v 2 \ ball D V v 1)) x 2).card := by
    refine sum_le_sum (fun x hx => ?_)
    have loc := first_row_local free (by omega) vv hx
    rw [punctured_split] at loc
    have := floor x (((erase_subset _ _).trans ball_subset) hx)
    omega
  have hY : ∑ _y ∈ (ball D V v 2 \ ball D V v 1) \ R, (2*d + 1)
      ≤ ∑ y ∈ (ball D V v 2 \ ball D V v 1) \ R,
        (ball D ((ball D V v 1).erase v ∪ (ball D V v 2 \ ball D V v 1)) y 2).card := by
    refine sum_le_sum (fun y hy => ?_)
    have f := second_ball_floor freeF (by omega) hd d1 minF
      (y := y) (by rw [punctured_split]; exact mem_union_right _ (mem_sdiff.mp hy).1)
    rw [punctured_split] at f
    exact f
  have hRs : ∑ _y ∈ R, (r + 2)
      ≤ ∑ y ∈ R, (ball D ((ball D V v 1).erase v ∪ (ball D V v 2 \ ball D V v 1)) y 2).card := by
    refine sum_le_sum (fun y hy => ?_)
    obtain ⟨x, hx, yx⟩ := ret y hy
    have f := returner_local free (by omega) degree vv (hR hy) hx yx
    rw [punctured_split] at f
    exact f
  have split := sum_sdiff hR (f := fun y =>
    (ball D ((ball D V v 1).erase v ∪ (ball D V v 2 \ ball D V v 1)) y 2).card)
  rw [sum_const, smul_eq_mul] at hX hY hRs
  rw [card_sdiff_of_subset hR] at hY
  rw [punctured_split, card_union_of_disjoint dis]
  have cY : R.card ≤ (ball D V v 2 \ ball D V v 1).card := card_le_card hR
  omega

/-- **Third-layer floor.** At a root with `|ball v 1| = r + 1` and `|ball v 2| = b`, every row having
`a ≤ |ball · 2|`: if `d ≤ q`, `d + z ≤ r` and `(b - 1) b < 2 (r (a - z) + (b - r - 1)(2 d + 1))`,
then `b + z + 1 ≤ |ball v 3|`. -/
theorem third_floor {r a b d z v : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card) (floor : ∀ x ∈ V, a ≤ (ball D V x 2).card)
    (vv : v ∈ V) (one : (ball D V v 1).card = r + 1) (two : (ball D V v 2).card = b)
    (hd : d ≤ q) (d1 : 1 ≤ d) (low : d + z ≤ r)
    (arith : (b - 1) * b < 2 * (r * (a - z) + (b - r - 1) * (2*d + 1))) :
    b + z + 1 ≤ (ball D V v 3).card := by
  classical
  by_contra! few
  have i23 : ball D V v 2 ⊆ ball D V v 3 := ball_mono_radius (by omega)
  have zc : (ball D V v 3 \ ball D V v 2).card ≤ z := by
    rw [card_sdiff_of_subset i23]
    omega
  have cnt := third_count (R := ∅) free hq degree floor vv hd d1 (by omega)
    (empty_subset _) (fun y hy => absurd hy (notMem_empty y))
  have i12 : ball D V v 1 ⊆ ball D V v 2 := ball_mono_radius (by omega)
  have vb1 : v ∈ ball D V v 1 := self_mem_ball vv
  have vb2 : v ∈ ball D V v 2 := self_mem_ball vv
  rw [card_erase_of_mem vb1, card_erase_of_mem vb2, card_sdiff_of_subset i12, one, two,
    card_empty] at cnt
  have m1 : r * (a - z) ≤ r * (a - (ball D V v 3 \ ball D V v 2).card) :=
    Nat.mul_le_mul_left _ (by omega)
  have e1 : r + 1 - 1 = r := by omega
  rw [e1] at cnt
  have e2 : b - (r + 1) = b - r - 1 := by omega
  rw [e2] at cnt
  simp only [Nat.sub_zero, Nat.zero_mul, Nat.add_zero] at cnt
  have e3 : b - 1 + 1 = b := by
    have := card_le_card i12
    omega
  rw [e3] at cnt
  omega

/-- **A second-layer row returns.** With lower quota `d'`, `|Y| ≤ q d'` and `d' + |Z| ≤ r`, some
row of the second layer heads the first layer. -/
theorem returner_exists {r d' v : ℕ} (none : NoHost q d') (free : QFree D V q) (hq : 3 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card) (vv : v ∈ V)
    (live : (ball D V v 2 \ ball D V v 1).Nonempty)
    (small : (ball D V v 2 \ ball D V v 1).card ≤ q*d')
    (low : d' + (ball D V v 3 \ ball D V v 2).card ≤ r) :
    ∃ y ∈ ball D V v 2 \ ball D V v 1, ∃ x ∈ (ball D V v 1).erase v, D y x = true := by
  classical
  by_contra! none'
  have yv : ball D V v 2 \ ball D V v 1 ⊆ V := sdiff_subset.trans ball_subset
  obtain ⟨y, hy, short⟩ := fragment_row none free yv live small
  have y2 := (mem_sdiff.mp hy).1
  have sub : outN D V y ⊆ outN D (ball D V v 2 \ ball D V v 1) y ∪ (ball D V v 3 \ ball D V v 2) := by
    intro w hw
    obtain ⟨wv, yw⟩ := mem_outN.mp hw
    by_cases w2 : w ∈ ball D V v 2
    · have wne : w ≠ v := by
        intro e
        rw [e] at yw
        exact no_back_arc free vv y2 (by omega) yw
      rcases two_split w2 wne with wX | wY
      · exact absurd yw (none' y hy w wX)
      · exact mem_union_left _ (mem_outN.mpr ⟨wY, yw⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_step y2 wv yw, w2⟩)
  have := degree y (ball_subset y2)
  have c := (card_le_card sub).trans (card_union_le _ _)
  omega

#print axioms host_in
#print axioms host_out
#print axioms sparse_row
#print axioms second_ball_floor
#print axioms layer_parent
#print axioms first_parent
#print axioms lack_card
#print axioms transition
#print axioms transition_ball
#print axioms ordinary_bound
#print axioms priv_sum
#print axioms regular_witness
#print axioms regular_regime
#print axioms local_capacity
#print axioms first_row_local
#print axioms second_row_local
#print axioms returner_local
#print axioms third_count
#print axioms third_floor
#print axioms returner_exists
end LeanCH.BR.RegularFirstLayer
