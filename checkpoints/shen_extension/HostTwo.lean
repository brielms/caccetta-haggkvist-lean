import checkpoints.shen_extension.LoopCollar

/-!
# The degree-two host is rigid

The analogue of `LoopCollar` one degree up. All of it is generic in `q` and `r`.

* `host_two_out`, `host_two_in`: a `q`-free digraph on exactly `2 q + 1` labels with minimum
  out-degree at least two has every out-degree and every in-degree exactly two.
* `collar_two`: a root `u` with exactly `2 q + 1` heads `X`, each of out-degree at least `r`, and
  at most `r - 2` labels at distance two. Then `X` is such a host, every head has out-degree
  exactly `r`, the second layer has exactly `r - 2` labels and every head points to all of it.
* `collar_two_ball`: so `|B (j+1) u| + 2 j ≤ |B j x| + 2 q + 1` for each head `x`, `j ≤ q`.

At `r = 2 q + 1` (the row `r = 9`, `q = 4`) this is the root with second layer `r - 2 = 7`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.HostTwo
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)

variable {D : CH.Digraph} {q : ℕ}

/-- In-neighbours inside `S`. -/
noncomputable def inN (D : CH.Digraph) (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  S.filter (fun w => D w v = true)

/-- The reverse 1-ball is the label and its in-neighbours. -/
theorem reverseBall_one {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q) {v : ℕ} (hv : v ∈ S) :
    (reverseBall D S v 1).card = (inN D S v).card + 1 := by
  classical
  have eq : reverseBall D S v 1 = insert v (inN D S v) := by
    ext w
    simp only [reverseBall, inN, mem_filter, mem_insert]
    constructor
    · rintro ⟨wS, hb⟩
      rcases (mem_ball_one wS).mp hb with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨wS, (mem_outN.mp h).2⟩
    · rintro (rfl | ⟨wS, wv⟩)
      · exact ⟨hv, self_mem_ball hv⟩
      · exact ⟨wS, (mem_ball_one wS).mpr (Or.inr (mem_outN.mpr ⟨hv, wv⟩))⟩
  rw [eq, card_insert_of_notMem]
  intro h
  exact loopfree free hq hv (mem_filter.mp h).2

/-- Every reverse 1-ball has at most three labels. -/
theorem host_two_rev {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (size : S.card = 2 * q + 1) (deg : ∀ v ∈ S, 2 ≤ (outN D S v).card) :
    ∀ v ∈ S, (reverseBall D S v 1).card ≤ 3 := by
  intro v hv
  have two := reverseBall_add_ball_le (v := v) (i := q - 1) (j := 1) free (by omega)
  have grow := ball_growth q hq D S free deg v hv (q - 1) (by omega)
  omega

/-- **The degree-two host, out-degrees.** `2 q + 1` labels, no closed walk of length at most
`q`, minimum out-degree at least two: every out-degree is exactly two. -/
theorem host_two_out {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (size : S.card = 2 * q + 1) (deg : ∀ v ∈ S, 2 ≤ (outN D S v).card) :
    ∀ x ∈ S, (outN D S x).card = 2 := by
  have rev := host_two_rev free hq size deg
  have total : ∑ v ∈ S, (ball D S v 1).card ≤ ∑ _v ∈ S, 3 := by
    rw [← sum_reverseBall_eq_sum_ball]
    exact Finset.sum_le_sum rev
  intro x hx
  by_contra ne
  have big : 3 < (ball D S x 1).card := by
    rw [ReachLedger.ball_one free hq hx]
    have := deg x hx
    omega
  have lt : ∑ _v ∈ S, 3 < ∑ v ∈ S, (ball D S v 1).card :=
    Finset.sum_lt_sum
      (fun v hv => by
        rw [ReachLedger.ball_one free hq hv]
        have := deg v hv
        omega)
      ⟨x, hx, big⟩
  omega

/-- **The degree-two host, in-degrees.** Same hypotheses: every in-degree is exactly two. -/
theorem host_two_in {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (size : S.card = 2 * q + 1) (deg : ∀ v ∈ S, 2 ≤ (outN D S v).card) :
    ∀ x ∈ S, (inN D S x).card = 2 := by
  have rev := host_two_rev free hq size deg
  have out := host_two_out free hq size deg
  have total : ∑ v ∈ S, (reverseBall D S v 1).card = ∑ _v ∈ S, 3 := by
    rw [sum_reverseBall_eq_sum_ball]
    exact Finset.sum_congr rfl (fun v hv => by rw [ReachLedger.ball_one free hq hv, out v hv])
  intro x hx
  have one := reverseBall_one free hq hx
  by_contra ne
  have small : (reverseBall D S x 1).card < 3 := by
    have := rev x hx
    omega
  have lt : ∑ v ∈ S, (reverseBall D S v 1).card < ∑ _v ∈ S, 3 :=
    Finset.sum_lt_sum (fun v hv => rev v hv) ⟨x, hx, small⟩
  omega

section collar
variable {V : Finset ℕ} {u r : ℕ}

/-- **The degree-two collar.** A root with exactly `2 q + 1` heads, each of out-degree at least
`r`, and a second layer of at most `r - 2` labels: inside the heads every out- and in-degree is
two, each head has out-degree exactly `r` and points to the whole second layer, which has
exactly `r - 2` labels. -/
theorem collar_two (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = 2 * q + 1) (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 2 ≤ r) :
    (∀ x ∈ outN D V u, (outN D (outN D V u) x).card = 2) ∧
      (∀ x ∈ outN D V u, (inN D (outN D V u) x).card = 2) ∧
      (layer D V 2 u).card + 2 = r ∧
      ∀ x ∈ outN D V u, (outN D V x).card = r ∧ layer D V 2 u ⊆ outN D V x := by
  classical
  have keep := head_keep free hq hu
  have inner := DipCost.layer_host (X := outN D V u) (Y := layer D V 2 u) (c := 2) quota keep thin
  have freeX := free.mono_set (outN_subset (D := D) (W := V) (y := u))
  have two := host_two_out freeX (by omega) heads inner
  have twoIn := host_two_in freeX (by omega) heads inner
  have cover : ∀ x ∈ outN D V u,
      outN D V x ⊆ outN D (outN D V u) x ∪ (layer D V 2 u ∩ outN D V x) := by
    intro x hx w hw
    rcases mem_union.mp (keep x hx hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
  have count : ∀ x ∈ outN D V u, r ≤ 2 + (layer D V 2 u ∩ outN D V x).card ∧
      (outN D V x).card ≤ 2 + (layer D V 2 u ∩ outN D V x).card := by
    intro x hx
    have c := (card_le_card (cover x hx)).trans (card_union_le _ _)
    rw [two x hx] at c
    exact ⟨(quota x hx).trans c, c⟩
  obtain ⟨x0, hx0⟩ : (outN D V u).Nonempty := card_pos.mp (by omega)
  have le0 := card_le_card (inter_subset_left : layer D V 2 u ∩ outN D V x0 ⊆ layer D V 2 u)
  have width : (layer D V 2 u).card + 2 = r := by
    have := (count x0 hx0).1
    omega
  refine ⟨two, twoIn, width, fun x hx => ?_⟩
  have le := card_le_card (inter_subset_left : layer D V 2 u ∩ outN D V x ⊆ layer D V 2 u)
  have full : layer D V 2 u ∩ outN D V x = layer D V 2 u :=
    eq_of_subset_of_card_le inter_subset_left (by have := (count x hx).1; omega)
  refine ⟨?_, fun w hw => (mem_inter.mp (full ▸ hw)).2⟩
  have := (count x hx).2
  have := quota x hx
  omega

/-- **The heads are fat.** Under the degree-two collar, for each head `x` and each `j ≤ q`:
`|B (j+1) u| + 2 j ≤ |B j x| + 2 q + 1`. -/
theorem collar_two_ball (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = 2 * q + 1) (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 2 ≤ r) {x : ℕ} (hx : x ∈ outN D V u) {j : ℕ} (hj : j ≤ q) :
    (ball D V u (j+1)).card + 2 * j ≤ (ball D V x j).card + 2 * q + 1 := by
  classical
  obtain ⟨two, -, -, all⟩ := collar_two free hq hu heads quota thin
  have keep := head_keep free hq hu
  have inh := collar_inherit hu keep hx (all x hx).2 j
  have uX : u ∉ outN D V u := fun h => loopfree free (by omega) hu (mem_outN.mp h).2
  have hostBall : ball D (outN D V u) x j ⊆ ball D V x j ∩ outN D V u := by
    intro w hw
    obtain ⟨wX, i, hi, walk⟩ := mem_ball.mp hw
    exact mem_inter.mpr ⟨mem_ball.mpr ⟨outN_subset wX, i, hi, walk.mono outN_subset⟩, wX⟩
  have grow := ball_growth q (by omega) D (outN D V u)
    (free.mono_set (outN_subset (D := D) (W := V) (y := u)))
    (fun v hv => (two v hv).ge) x hx j hj
  have inside := card_le_card hostBall
  have split : ball D V u (j+1) ⊆ insert u (outN D V u) ∪ (ball D V x j \ outN D V u) := by
    intro w hw
    rcases mem_union.mp (inh hw) with h | h
    · exact mem_union_left _ h
    · by_cases wX : w ∈ outN D V u
      · exact mem_union_left _ (mem_insert_of_mem wX)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨h, wX⟩)
  have c := (card_le_card split).trans (card_union_le _ _)
  rw [card_insert_of_notMem uX, heads] at c
  have parts := card_sdiff_add_card_inter (ball D V x j) (outN D V u)
  omega

/-- **No arcs back.** Under the degree-two collar (`3 ≤ q`), no label of the second layer points
to the root or to a head. -/
theorem two_no_return (free : QFree D V q) (hq : 3 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = 2 * q + 1) (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 2 ≤ r) {y : ℕ} (hy : y ∈ layer D V 2 u)
    {w : ℕ} (hw : w ∈ insert u (outN D V u)) : ¬ D y w = true := by
  intro yw
  obtain ⟨-, -, -, all⟩ := collar_two free (by omega) hu heads quota thin
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have yV : y ∈ V := ball_subset yb
  rcases mem_insert.mp hw with rfl | wX
  · exact no_back_arc free hu yb (by omega) yw
  · exact digonfree free (by omega) (outN_subset wX) yV
      (mem_outN.mp ((all w wX).2 hy)).2 yw

/-- Rows of the second layer stay in the second and third layers. -/
theorem two_keep (free : QFree D V q) (hq : 3 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = 2 * q + 1) (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 2 ≤ r) :
    ∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u := by
  intro y hy w hw
  obtain ⟨wV, yw⟩ := mem_outN.mp hw
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have wb : w ∈ ball D V u 3 := ball_step yb wV yw
  have n1 : w ∉ ball D V u 1 := by
    intro h
    rcases (mem_ball_one hu).mp h with e | h
    · exact two_no_return free hq hu heads quota thin hy
        (e ▸ mem_insert_self u (outN D V u)) yw
    · exact two_no_return free hq hu heads quota thin hy (mem_insert_of_mem h) yw
  by_cases n2 : w ∈ ball D V u 2
  · exact mem_union_left _ (mem_layer.mpr ⟨n2, n1⟩)
  · exact mem_union_right _ (mem_layer.mpr ⟨wb, n2⟩)

/-- **The third layer is wide.** Under the degree-two collar with `r ≤ 2 q + 2` and minimum
out-degree `r` on the second layer, the third layer has at least `r - 1` labels (`3 ≤ r`): otherwise the
second layer keeps minimum out-degree two on `r - 2 < 2 q + 1` labels. -/
theorem two_third_wide (free : QFree D V q) (hq : 3 ≤ q) (hu : u ∈ V)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (heads : (outN D V u).card = 2 * q + 1) (thin : (layer D V 2 u).card + 2 ≤ r)
    (hr : r ≤ 2 * q + 2) (hr3 : 3 ≤ r) :
    r ≤ (layer D V 3 u).card + 1 := by
  have quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card := fun x hx => deg x (outN_subset hx)
  obtain ⟨-, -, width, -⟩ := collar_two free (by omega) hu heads quota thin
  by_contra h
  push Not at h
  have keep := two_keep free hq hu heads quota thin
  have inner := DipCost.layer_host (X := layer D V 2 u) (Y := layer D V 3 u) (c := 2)
    (fun y hy => deg y (DotTwoPassShellTransport.layer_subset hy)) keep (by omega)
  obtain ⟨y, hy⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
  have big := ball_growth q (by omega) D (layer D V 2 u)
    (free.mono_set DotTwoPassShellTransport.layer_subset) (fun v hv => inner v hv) y hy q le_rfl
  have := card_le_card (ball_subset (D := D) (W := layer D V 2 u) (u := y) (k := q))
  omega

/-- **Each head is far above the level.** Under the degree-two collar, `3 ≤ q`, minimum
out-degree `r ≤ 2 q + 2`: every head `x` has `|B 2 x| ≥ 2 r + 2`. At `(r, q) = (9, 4)`: the
nine heads of a root with second layer `7` have `|B 2 x| ≥ 20` (punctured `f₂ ≥ 19`). -/
theorem two_head_fat (free : QFree D V q) (hq : 3 ≤ q) (hu : u ∈ V)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (heads : (outN D V u).card = 2 * q + 1) (thin : (layer D V 2 u).card + 2 ≤ r)
    (hr : r ≤ 2 * q + 2) (hr3 : 3 ≤ r) {x : ℕ} (hx : x ∈ outN D V u) :
    2 * r + 2 ≤ (ball D V x 2).card := by
  have quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card := fun x hx => deg x (outN_subset hx)
  obtain ⟨-, -, width, -⟩ := collar_two free (by omega) hu heads quota thin
  have wide := two_third_wide free hq hu deg heads thin hr hr3
  have fat : (ball D V u 3).card + 2 * 2 ≤ (ball D V x 2).card + 2 * q + 1 :=
    collar_two_ball free (by omega) hu heads quota thin hx (j := 2) (by omega)
  have b1 := ReachLedger.ball_one free (by omega) hu
  have b2 : (ball D V u 2).card = (layer D V 2 u).card + (ball D V u 1).card :=
    ShapeClimbRoot.card_ball_succ 1
  have b3 : (ball D V u 3).card = (layer D V 3 u).card + (ball D V u 2).card :=
    ShapeClimbRoot.card_ball_succ 2
  omega

/-- **Degree-two banks meet only if equal.** Two roots under the degree-two collar that share a
head have the same heads (and the same second layer). Paper: dossier Appendix 2 ("two such low
banks intersect only if identical"); here the order bound replaces strong connectivity. -/
theorem banks_equal (free : QFree D V q) (hq : 2 ≤ q) {u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V)
    (heads : (outN D V u).card = 2 * q + 1) (heads' : (outN D V u').card = 2 * q + 1)
    (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (quota' : ∀ x ∈ outN D V u', r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 2 ≤ r) (thin' : (layer D V 2 u').card + 2 ≤ r)
    {x : ℕ} (hx : x ∈ outN D V u) (hx' : x ∈ outN D V u') :
    layer D V 2 u = layer D V 2 u' ∧ outN D V u = outN D V u' := by
  classical
  obtain ⟨two, -, width, all⟩ := collar_two free hq hu heads quota thin
  obtain ⟨two', -, width', all'⟩ := collar_two free hq hu' heads' quota' thin'
  have keep := head_keep free hq hu
  have keep' := head_keep free hq hu'
  -- a head is never in the second layer
  have sep : ∀ {v w : ℕ}, v ∈ V → w ∈ outN D V v → w ∉ layer D V 2 v := by
    intro v w hv hw hl
    exact (mem_layer.mp hl).2 ((mem_ball_one hv).mpr (Or.inr hw))
  -- the second layers agree: otherwise a digon between the two complete rectangles
  have sub : layer D V 2 u ⊆ layer D V 2 u' := by
    by_contra ns
    have ns' : ¬ layer D V 2 u' ⊆ layer D V 2 u := by
      intro h
      have := eq_of_subset_of_card_le h (by omega)
      exact ns this.symm.subset
    obtain ⟨y, hy, hy'⟩ := not_subset.mp ns
    obtain ⟨z, hz', hz⟩ := not_subset.mp ns'
    have yX' : y ∈ outN D V u' := by
      rcases mem_union.mp (keep' x hx' ((all x hx).2 hy)) with h | h
      · exact h
      · exact (hy' h).elim
    have zX : z ∈ outN D V u := by
      rcases mem_union.mp (keep x hx ((all' x hx').2 hz')) with h | h
      · exact h
      · exact (hz h).elim
    have yz := (mem_outN.mp ((all' y yX').2 hz')).2
    have zy := (mem_outN.mp ((all z zX).2 hy)).2
    exact digonfree free hq (outN_subset yX') (outN_subset zX) yz zy
  have eqY : layer D V 2 u = layer D V 2 u' := eq_of_subset_of_card_le sub (by omega)
  -- the common heads are closed under the host arcs
  set T := outN D V u ∩ outN D V u' with hT
  have closed : ∀ v ∈ T, outN D (outN D V u) v ⊆ outN D T v := by
    intro v hv w hw
    obtain ⟨vX, vX'⟩ := mem_inter.mp hv
    obtain ⟨wX, vw⟩ := mem_outN.mp hw
    have wout : w ∈ outN D V v := mem_outN.mpr ⟨outN_subset wX, vw⟩
    rcases mem_union.mp (keep' v vX' wout) with h | h
    · exact mem_outN.mpr ⟨mem_inter.mpr ⟨wX, h⟩, vw⟩
    · exact (sep hu wX (eqY ▸ h)).elim
  have deg : ∀ v ∈ T, 2 ≤ (outN D T v).card := by
    intro v hv
    have := card_le_card (closed v hv)
    rw [two v (mem_inter.mp hv).1] at this
    exact this
  have TV : T ⊆ V := fun v hv => outN_subset (mem_inter.mp hv).1
  have xT : x ∈ T := mem_inter.mpr ⟨hx, hx'⟩
  have big := ball_growth q (by omega) D T (free.mono_set TV) deg x xT q le_rfl
  have bT := card_le_card (ball_subset (D := D) (W := T) (u := x) (k := q))
  have e1 : T = outN D V u := eq_of_subset_of_card_le inter_subset_left (by omega)
  have e2 : T = outN D V u' := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact ⟨eqY, e1.symm.trans e2⟩

end collar

/-! ### In-degrees and the tight-supplier count -/

/-- **Parents lie outside the forward ball.** For `j + 1 ≤ q`:
`indeg v + |B j v| ≤ |V|`. -/
theorem indeg_ball {V : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q) {v : ℕ} (hv : v ∈ V)
    {j : ℕ} (hj : j + 1 ≤ q) : (inN D V v).card + (ball D V v j).card ≤ V.card := by
  have two := reverseBall_add_ball_le (v := v) (i := j) (j := 1) free (by omega)
  have one := reverseBall_one free hq hv
  omega

/-- Arcs from `T` into `H`, counted from both ends. -/
theorem arcs_between (T H : Finset ℕ) :
    ∑ u ∈ T, (H.filter (fun v => D u v = true)).card =
      ∑ v ∈ H, (T.filter (fun u => D u v = true)).card := by
  simp only [card_filter]
  exact sum_comm

/-- **The tight-supplier count.** `T ⊆ V`, `H = V \ T`. If every row of `T` has at least `a`
heads in `H` and every row of `H` has at most `c` parents, then `a |T| ≤ c |H|`. With the
SAT-supported law "a root with second layer `r - 1` has at most one head with second layer
`≤ r - 1`" one takes `T` = the rows with second layer `≤ 8`, `a = 8` at `r = 9`. -/
theorem supplier_count {V T : Finset ℕ} {a c : ℕ} (tv : T ⊆ V)
    (supply : ∀ u ∈ T, a ≤ ((V \ T).filter (fun v => D u v = true)).card)
    (cap : ∀ v ∈ V \ T, (inN D V v).card ≤ c) :
    a * T.card ≤ c * (V \ T).card := by
  have lhs : a * T.card ≤ ∑ u ∈ T, ((V \ T).filter (fun v => D u v = true)).card := by
    have := sum_le_sum supply
    simpa [sum_const, smul_eq_mul, mul_comm] using this
  rw [arcs_between T (V \ T)] at lhs
  have rhs : ∑ v ∈ V \ T, (T.filter (fun u => D u v = true)).card ≤ ∑ _v ∈ V \ T, c := by
    refine sum_le_sum (fun v hv => ?_)
    refine le_trans (card_le_card (fun u hu => ?_)) (cap v hv)
    obtain ⟨uT, uv⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨tv uT, uv⟩
  simp only [sum_const, smul_eq_mul] at rhs
  rw [mul_comm] at rhs
  omega

#print axioms host_two_out
#print axioms host_two_in
#print axioms collar_two
#print axioms collar_two_ball
#print axioms two_no_return
#print axioms two_third_wide
#print axioms two_head_fat
#print axioms banks_equal
#print axioms indeg_ball
#print axioms supplier_count
end LeanCH.BR.HostTwo
