import checkpoints.shen_extension.ThinSuppliers
import checkpoints.shen_extension.ShapeClimbAvoid

/-!
# Tight floors on the row `r = q + 2`

Every out-degree is exactly `r = q + 2` and there is no closed walk of length at most `q`.
A root `u` has heads `X`, second layer `Y`, third layer `Z`, fourth layer `W`.

* `grow_one` (generic): in a `q`-free fragment of minimum out-degree two, a ball of fewer than
  `2q + 1` labels grows at the next radius (a closed ball would contradict `ball_growth`).
* **P7b** `p7b_fourth` (`4 ≤ q`): widths `|Y| = q + 1`, `|Z| = q + 2` force `|W| ≥ q + 1`.
  The root is thin, so `Y` heads only `Y ∪ Z` (`ThinSuppliers.y_keep_r`). No row of `Z` heads
  a head of the root (`p7b_z_no_x`: a complete head heads all of `Y`; a head that is not complete
  has two heads among the heads and at most one of them is not complete, since only two heads
  are not complete; so `x → (c →) y → z → x` closes a walk of length at most four). With
  `|W| ≤ q` the fragment `Y ∪ Z` (`2q + 3` labels) has minimum out-degree two and its `q + 1`
  rows of `Y` have balls of at least `q + 4` labels at radius two; the ledger at radii
  `2, q - 2` then overflows `(2q + 3)(2q + 4)`.
* **Q** `q_fifth` (`5 ≤ q`): widths `|Y| = |Z| = |W| = q + 1` force a fifth layer of at least
  `q + 1`. The root is tight: `Y` is a loop complete to `Z` (`CollarTwo.loop_complete`), `Z` heads
  only `Z ∪ W` (`ThinSuppliers.z_keep`) and is then a loop complete to `W` (`loop_next`); a row of
  `W` heading `u`, `X`, `Y` or `Z` closes a walk of length at most five, so `W` heads only `W`
  and the fifth layer, and `ball_growth` on `W` needs `q + 1` exits.
* **P7a** `p7a_fourth` (`6 ≤ q`, floors as hypotheses): widths `|Y| = q + 2`, `|Z| = q + 1` force
  `|W| ≥ q + 1` whenever the floors `f2`, `f3` of every root at radii two and three pass the
  arithmetic test `P7aOK q f2 f3` (true for the computed floors at `q = 6, 7, 8, 9`). A fragment
  count on `X ∪ Y ∪ Z` at radii `3, q - 3` shows that no row of `Z` heads back into `X ∪ Y`; then
  `Z` keeps minimum out-degree two on `q + 1` labels.
* The patterns `p7aA`, `p7bA`, `qA` with their avoidance lemmas, for `ShapeClimbAvoid.layersA`
  (regular digraphs): every root avoids P7a (over floors of every root) and P7b, and a tight root
  avoids `notTightA` and Q (`tight_avoids`).

Everything is generic in `q`; the smallest `q` and the numeric hypothesis are stated with each
result.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TightFloors
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ThinSuppliers

variable {D : CH.Digraph} {q : ℕ}

/-! ### Growth in a fragment of minimum out-degree two -/

/-- A closed ball of a `q`-free fragment of minimum out-degree two has at least `2q + 1`
labels; so a smaller ball grows at the next radius. -/
theorem grow_one {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (m2 : ∀ v ∈ S, 2 ≤ (outN D S v).card) {v : ℕ} (hv : v ∈ S) (k : ℕ)
    (small : (ball D S v k).card < 2 * q + 1) :
    (ball D S v k).card + 1 ≤ (ball D S v (k + 1)).card := by
  rcases TubeAtCutoff.closed_or_grow (D := D) (S := S) (v := v) (a := k) (M := 1) with
    ⟨j, hj1, hj2, cl⟩ | g
  · obtain rfl : j = k := by omega
    exfalso
    have KS : ball D S v j ⊆ S := ball_subset
    have m2K : MinOut2 D (ball D S v j) := by
      intro x hx
      change 2 ≤ (outN D (ball D S v j) x).card
      refine (m2 x (KS hx)).trans (card_le_card fun t ht => ?_)
      obtain ⟨tS, xt⟩ := mem_outN.mp ht
      exact mem_outN.mpr ⟨cl x hx t tS xt, xt⟩
    have big := ball_growth q hq D _ (free.mono_set KS) m2K v (self_mem_ball hv) q le_rfl
    have := card_le_card (ball_subset (D := D) (W := ball D S v j) (u := v) (k := q))
    omega
  · exact g

/-- In such a fragment, a row with `d` heads has at least `min (d + 2) (2q + 1)` labels within
two steps. -/
theorem ball_two_of_heads {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (m2 : ∀ v ∈ S, 2 ≤ (outN D S v).card) {v : ℕ} (hv : v ∈ S) :
    min ((outN D S v).card + 2) (2 * q + 1) ≤ (ball D S v 2).card := by
  have b1 := ReachLedger.ball_one free hq hv
  have mono : (ball D S v 1).card ≤ (ball D S v 2).card :=
    card_le_card (ball_mono_radius (by omega))
  by_cases small : (ball D S v 1).card < 2 * q + 1
  · have := grow_one free hq m2 hv 1 small
    rw [show 1 + 1 = 2 from rfl] at this
    omega
  · omega

/-! ### P7b: widths `(q + 2, q + 1, q + 2)` -/

section p7b
variable {V : Finset ℕ} {u : ℕ}

/-- At a thin root on the row `r = q + 2`, `4 ≤ q`, no row of the third layer heads a head of
the root. -/
theorem p7b_z_no_x (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (thin : Thin D V (q + 2) u) {z : ℕ} (hz : z ∈ layer D V 3 u) {x : ℕ}
    (hx : x ∈ outN D V u) : ¬ D z x = true := by
  classical
  intro zx
  have XV : outN D V u ⊆ V := outN_subset
  have xV := XV hx
  obtain ⟨y0, hy0, y0z⟩ := ShapeClimbRoot.parent_mem hu (i := 2) (by norm_num) hz
  have zV : z ∈ V := layer_subset hz
  have y0V : y0 ∈ V := layer_subset hy0
  have cX := complete_count free (by omega) reg hu thin (by omega)
  by_cases xc : x ∈ complete D V u
  · have xy := (mem_outN.mp (complete_full free (by omega) reg hu thin xc hy0)).2
    exact free x (0 + 1 + 1 + 1) (by omega) (by omega)
      ((((Walk.refl x).snoc y0V xy).snoc zV y0z).snoc xV zx)
  · have two : 2 ≤ (outN D (outN D V u) x).card := by
      by_contra h
      exact xc (mem_lone.mpr ⟨hx, by omega⟩)
    obtain ⟨c, hc, cc⟩ : ∃ c ∈ outN D (outN D V u) x, c ∈ complete D V u := by
      by_contra none
      push Not at none
      have sub : outN D (outN D V u) x ⊆ (outN D V u \ complete D V u).erase x := by
        intro c hc
        refine mem_erase.mpr ⟨fun e => ?_, mem_sdiff.mpr ⟨(mem_outN.mp hc).1, none c hc⟩⟩
        rw [e] at hc
        exact loopfree free (by omega) xV (mem_outN.mp hc).2
      have c1 := card_le_card sub
      rw [card_erase_of_mem (mem_sdiff.mpr ⟨hx, xc⟩), card_sdiff_of_subset complete_subset,
        reg u hu] at c1
      omega
    obtain ⟨cX', xc'⟩ := mem_outN.mp hc
    have cy := (mem_outN.mp (complete_full free (by omega) reg hu thin cc hy0)).2
    exact free x (0 + 1 + 1 + 1 + 1) (by omega) (by omega)
      (((((Walk.refl x).snoc (XV cX') xc').snoc y0V cy).snoc zV y0z).snoc xV zx)

/-- **P7b.** On the row `r = q + 2`, `4 ≤ q`: a root with second layer `q + 1` and third layer
`q + 2` has at least `q + 1` labels in its fourth layer. -/
theorem p7b_fourth (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (h2 : (layer D V 2 u).card = q + 1) (h3 : (layer D V 3 u).card = q + 2) :
    q + 1 ≤ (layer D V 4 u).card := by
  by_contra small
  push Not at small
  have thin : Thin D V (q + 2) u := by unfold Thin; omega
  have hr : q + 2 + 1 ≤ 2 * q := by omega
  set Y := layer D V 2 u with hY
  set Z := layer D V 3 u with hZ
  have ykeep := y_keep_r free (by omega) reg hu thin hr
  have zkeep : ∀ z ∈ Z, outN D V z ⊆ (Y ∪ Z) ∪ layer D V 4 u := by
    intro z hz t ht
    obtain ⟨tV, zt⟩ := mem_outN.mp ht
    have zb : z ∈ ball D V u 3 := (mem_layer.mp hz).1
    have tb : t ∈ ball D V u 4 := ball_step zb tV zt
    have n1 : t ∉ ball D V u 1 := by
      intro h1
      rcases (mem_ball_one hu).mp h1 with rfl | hX
      · exact no_back_arc free hu zb (by omega) zt
      · exact p7b_z_no_x free hq reg hu thin hz hX zt
    by_cases n2 : t ∈ ball D V u 2
    · exact mem_union_left _ (mem_union_left _ (mem_layer.mpr ⟨n2, n1⟩))
    · by_cases n3 : t ∈ ball D V u 3
      · exact mem_union_left _ (mem_union_right _ (mem_layer.mpr ⟨n3, n2⟩))
      · exact mem_union_right _ (mem_layer.mpr ⟨tb, n3⟩)
  set S := Y ∪ Z with hS
  have SV : S ⊆ V := union_subset layer_subset layer_subset
  have freeS : QFree D S q := free.mono_set SV
  have disj : Disjoint Y Z := ShapeClimbRoot.layer_disjoint (by norm_num)
  have cS : S.card = 2 * q + 3 := by rw [hS, card_union_of_disjoint disj]; omega
  -- rows of `Y` keep all their heads
  have yfull : ∀ y ∈ Y, q + 2 ≤ (outN D S y).card := by
    intro y hy
    rw [← reg y (layer_subset hy)]
    exact card_le_card fun t ht => mem_outN.mpr ⟨ykeep y hy ht, (mem_outN.mp ht).2⟩
  have zfull : ∀ z ∈ Z, 2 ≤ (outN D S z).card := by
    intro z hz
    have cover : outN D V z ⊆ outN D S z ∪ layer D V 4 u := by
      intro t ht
      rcases mem_union.mp (zkeep z hz ht) with h | h
      · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp ht).2⟩)
      · exact mem_union_right _ h
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg z (layer_subset hz)] at c
    omega
  have m2 : ∀ v ∈ S, 2 ≤ (outN D S v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · have := yfull v h; omega
    · exact zfull v h
  have m2' : MinOut2 D S := m2
  -- the ledger at radii `2` and `q - 2`
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 4 := ⟨q - 4, by omega⟩
  have led := ReachLedger.ledger (D := D) (V := S) (i := 2) (j := p + 2) freeS (by omega)
  have lowY2 : ∀ y ∈ Y, p + 8 ≤ (ball D S y 2).card := by
    intro y hy
    have := ball_two_of_heads freeS (by omega) m2 (mem_union_left _ hy)
    have := yfull y hy
    omega
  have lowYj : ∀ y ∈ Y, p + 8 ≤ (ball D S y (p + 2)).card := fun y hy =>
    (lowY2 y hy).trans (card_le_card (ball_mono_radius (by omega)))
  have lowZ2 : ∀ z ∈ Z, 5 ≤ (ball D S z 2).card := fun z hz =>
    ball_growth (p + 4) (by omega) D S freeS m2' z (mem_union_right _ hz) 2 (by omega)
  have lowZj : ∀ z ∈ Z, 2 * (p + 2) + 1 ≤ (ball D S z (p + 2)).card := fun z hz =>
    ball_growth (p + 4) (by omega) D S freeS m2' z (mem_union_right _ hz) (p + 2) (by omega)
  have e2 : ∑ v ∈ S, (ball D S v 2).card =
      ∑ v ∈ Y, (ball D S v 2).card + ∑ v ∈ Z, (ball D S v 2).card := sum_union disj
  have ej : ∑ v ∈ S, (ball D S v (p + 2)).card =
      ∑ v ∈ Y, (ball D S v (p + 2)).card + ∑ v ∈ Z, (ball D S v (p + 2)).card := sum_union disj
  have sY2 := card_nsmul_le_sum Y (fun v => (ball D S v 2).card) (p + 8) lowY2
  have sYj := card_nsmul_le_sum Y (fun v => (ball D S v (p + 2)).card) (p + 8) lowYj
  have sZ2 := card_nsmul_le_sum Z (fun v => (ball D S v 2).card) 5 lowZ2
  have sZj := card_nsmul_le_sum Z (fun v => (ball D S v (p + 2)).card) (2 * (p + 2) + 1) lowZj
  rw [smul_eq_mul, h2] at sY2 sYj
  rw [smul_eq_mul, h3] at sZ2 sZj
  rw [cS] at led
  have key : (2 * (p + 4) + 3) * (2 * (p + 4) + 3 + 1) <
      (p + 4 + 1) * (p + 8) + (p + 4 + 2) * 5 + (p + 4 + 1) * (p + 8) +
        (p + 4 + 2) * (2 * (p + 2) + 1) := by nlinarith
  generalize ∑ v ∈ S, (ball D S v 2).card = s2 at led e2
  generalize ∑ v ∈ S, (ball D S v (p + 2)).card = sj at led ej
  generalize ∑ v ∈ Y, (ball D S v 2).card = y2 at e2 sY2
  generalize ∑ v ∈ Z, (ball D S v 2).card = z2 at e2 sZ2
  generalize ∑ v ∈ Y, (ball D S v (p + 2)).card = yj at ej sYj
  generalize ∑ v ∈ Z, (ball D S v (p + 2)).card = zj at ej sZj
  omega

end p7b

/-! ### Q: a tight root with a fourth layer of `q + 1` labels -/

section qpat
variable {V : Finset ℕ} {u : ℕ}

/-- A set `Z` of `q + 1` labels whose rows head only `Z` and a set `W` of `q + 1` labels is a
loop complete to `W`. -/
theorem loop_next {Z W : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q) (ZV : Z ⊆ V)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2) (cZ : Z.card = q + 1) (cW : W.card = q + 1)
    (keep : ∀ z ∈ Z, outN D V z ⊆ Z ∪ W) : ∀ z ∈ Z, W ⊆ outN D V z := by
  have inner := DipCost.layer_host (X := Z) (Y := W) (c := 1)
    (fun z hz => (reg z (ZV hz)).ge) keep (by omega)
  have one := loop_unique_head (free.mono_set ZV) hq cZ inner
  intro z hz
  have cover : outN D V z ⊆ outN D Z z ∪ (W ∩ outN D V z) := by
    intro w hw
    rcases mem_union.mp (keep z hz hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
  have c := (card_le_card cover).trans (card_union_le _ _)
  rw [one z hz, reg z (ZV hz)] at c
  have full : W ∩ outN D V z = W := eq_of_subset_of_card_le inter_subset_left (by omega)
  intro w hw
  rw [← full] at hw
  exact (mem_inter.mp hw).2

/-- A head of a root on the row `r = q + 2` with second layer `q + 1` heads a label of the
second layer. -/
theorem head_to_second (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2) (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) :
    ∃ y ∈ layer D V 2 u, D x y = true := by
  by_contra none
  push Not at none
  have xV : x ∈ V := outN_subset hx
  have sub : outN D V x ⊆ (outN D V u).erase x := by
    intro a ha
    rcases mem_union.mp (head_keep free hq hu x hx ha) with h | h
    · refine mem_erase.mpr ⟨fun e => ?_, h⟩
      rw [e] at ha
      exact loopfree free (by omega) xV (mem_outN.mp ha).2
    · exact absurd (mem_outN.mp ha).2 (none a h)
  have := card_le_card sub
  rw [card_erase_of_mem hx, reg x xV, reg u hu] at this
  omega

/-- **Q.** On the row `r = q + 2`, `5 ≤ q`: a root with second, third and fourth layers of
`q + 1` labels each has at least `q + 1` labels in its fifth layer. The root is tight, so `Y`
is a loop complete to `Z` (`CollarTwo.loop_complete`) and `Z` heads only `Z ∪ W`
(`ThinSuppliers.z_keep`); then `Z` is a loop complete to `W` (`loop_next`), so a row of `W`
heading `u`, `X`, `Y` or `Z` closes a walk of length at most five; with at most `q` labels in
the fifth layer the rows of `W` keep two heads in `W`, against `ball_growth`. -/
theorem q_fifth (free : QFree D V q) (hq : 5 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (h2 : (layer D V 2 u).card = q + 1) (h3 : (layer D V 3 u).card = q + 1)
    (h4 : (layer D V 4 u).card = q + 1) : q + 1 ≤ (layer D V 5 u).card := by
  by_contra small
  push Not at small
  have tight : CollarTwo.Tight D V q u := ⟨h2, h3.le⟩
  obtain ⟨-, -, yz⟩ := CollarTwo.loop_complete free (by omega) reg hu tight
  have tightR : TightR D V (q + 2) u := ⟨by omega, by omega⟩
  have zkeep := z_keep free (by omega) reg hu tightR (by omega) (by omega)
  have zw := loop_next free (by omega) layer_subset reg h3 h4 zkeep
  have wkeep : ∀ w ∈ layer D V 4 u, outN D V w ⊆ layer D V 4 u ∪ layer D V 5 u := by
    intro w hw t ht
    obtain ⟨tV, wt⟩ := mem_outN.mp ht
    have wb : w ∈ ball D V u 4 := (mem_layer.mp hw).1
    have wV : w ∈ V := layer_subset hw
    have tb : t ∈ ball D V u 5 := ball_step wb tV wt
    obtain ⟨z, hz, -⟩ := ShapeClimbRoot.parent_mem hu (i := 3) (by norm_num) hw
    have zV : z ∈ V := layer_subset hz
    have zw2 := (mem_outN.mp (zw z hz hw)).2
    have n3 : t ∉ ball D V u 3 := by
      intro t3
      by_cases t1 : t ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp t1 with rfl | hX
        · exact no_back_arc free hu wb (by omega) wt
        · obtain ⟨y, hy, ty⟩ := head_to_second free (by omega) reg hu hX
          have yz2 := (mem_outN.mp (yz y hy hz)).2
          exact free t (0 + 1 + 1 + 1 + 1) (by omega) (by omega)
            (((((Walk.refl t).snoc (layer_subset hy) ty).snoc zV yz2).snoc wV zw2).snoc tV wt)
      · by_cases t2 : t ∈ ball D V u 2
        · have tz := (mem_outN.mp (yz t (mem_layer.mpr ⟨t2, t1⟩) hz)).2
          exact free t (0 + 1 + 1 + 1) (by omega) (by omega)
            ((((Walk.refl t).snoc zV tz).snoc wV zw2).snoc tV wt)
        · have tw := (mem_outN.mp (zw t (mem_layer.mpr ⟨t3, t2⟩) hw)).2
          exact digonfree free (by omega) tV wV tw wt
    by_cases n4 : t ∈ ball D V u 4
    · exact mem_union_left _ (mem_layer.mpr ⟨n4, n3⟩)
    · exact mem_union_right _ (mem_layer.mpr ⟨tb, n4⟩)
  have inner := DipCost.layer_host (X := layer D V 4 u) (Y := layer D V 5 u) (c := 2)
    (fun w hw => (reg w (layer_subset hw)).ge) wkeep (by omega)
  obtain ⟨w, hw⟩ : (layer D V 4 u).Nonempty := card_pos.mp (by omega)
  have big := ball_growth q (by omega) D (layer D V 4 u) (free.mono_set layer_subset)
    (fun v hv => inner v hv) w hw q le_rfl
  have := card_le_card (ball_subset (D := D) (W := layer D V 4 u) (u := w) (k := q))
  omega

end qpat

/-! ### P7a: widths `(q + 2, q + 2, q + 1)`, by a fragment count over floors -/

section p7a
variable {V : Finset ℕ} {u : ℕ}

/-- The fragment of a root: its heads, second and third layers. -/
noncomputable def frag (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (outN D V u ∪ layer D V 2 u) ∪ layer D V 3 u

theorem mem_frag (hu : u ∈ V) {w : ℕ} (h3 : w ∈ ball D V u 3) (ne : w ≠ u) :
    w ∈ frag D V u := by
  by_cases h1 : w ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp h1 with e | hX
    · exact (ne e).elim
    · exact mem_union_left _ (mem_union_left _ hX)
  · by_cases h2 : w ∈ ball D V u 2
    · exact mem_union_left _ (mem_union_right _ (mem_layer.mpr ⟨h2, h1⟩))
    · exact mem_union_right _ (mem_layer.mpr ⟨h3, h2⟩)

theorem frag_ball (free : QFree D V q) (hq : 1 ≤ q) (hu : u ∈ V) {w : ℕ}
    (hw : w ∈ frag D V u) : w ∈ ball D V u 3 ∧ w ≠ u := by
  rcases mem_union.mp hw with h | h
  · rcases mem_union.mp h with hX | hY
    · refine ⟨ball_mono_radius (by omega) ((mem_ball_one hu).mpr (Or.inr hX)), fun e => ?_⟩
      rw [e] at hX
      exact loopfree free hq hu (mem_outN.mp hX).2
    · exact ⟨ball_mono_radius (by omega) (mem_layer.mp hY).1,
        fun e => (mem_layer.mp hY).2 (by rw [e]; exact self_mem_ball hu)⟩
  · exact ⟨(mem_layer.mp h).1, fun e => (mem_layer.mp h).2 (by rw [e]; exact self_mem_ball hu)⟩

theorem frag_subset : frag D V u ⊆ V :=
  union_subset (union_subset outN_subset layer_subset) layer_subset

/-- Short walks from the fragment that end outside the fourth layer stay in the fragment. -/
theorem frag_walk (free : QFree D V q) (hq : 4 ≤ q) (hu : u ∈ V) :
    ∀ {v w j : ℕ}, Walk D V v w j → ∀ m, v ∈ ball D V u m → v ≠ u → m + j ≤ 4 →
      w ∉ layer D V 4 u → (w ∈ ball D V u 3 ∧ w ≠ u) ∧ Walk D (frag D V u) v w j := by
  intro v w j walk
  induction walk with
  | refl a =>
    intro m ha ne hm out
    refine ⟨⟨?_, ne⟩, .refl a⟩
    by_contra h3
    exact out (mem_layer.mpr ⟨ball_mono_radius (by omega) ha, h3⟩)
  | @step a b c k hb hab rest ih =>
    intro m ha ne hm out
    have bb : b ∈ ball D V u (m + 1) := ball_step ha hb hab
    have bne : b ≠ u := fun e => no_back_arc free hu ha (by omega) (e ▸ hab)
    obtain ⟨cc, wk⟩ := ih (m + 1) bb bne (by omega) out
    have b3 : b ∈ ball D V u 3 := by
      rcases Nat.eq_zero_or_pos k with rfl | pos
      · cases rest
        exact cc.1
      · exact ball_mono_radius (by omega) bb
    exact ⟨cc, .step (mem_frag hu b3 bne) hab wk⟩

/-- Balls of fragment rows lose at most the fourth layer. -/
theorem frag_ball_card (free : QFree D V q) (hq : 4 ≤ q) (hu : u ∈ V) {v m k : ℕ}
    (hv : v ∈ ball D V u m) (ne : v ≠ u) (hmk : m + k ≤ 4) :
    (ball D V v k).card ≤ (ball D (frag D V u) v k).card + (layer D V 4 u).card := by
  have sub : ball D V v k \ layer D V 4 u ⊆ ball D (frag D V u) v k := by
    intro w hw
    obtain ⟨hw, out⟩ := mem_sdiff.mp hw
    obtain ⟨-, j, hj, walk⟩ := mem_ball.mp hw
    obtain ⟨⟨w3, wne⟩, wk⟩ := frag_walk free hq hu walk m hv ne (by omega) out
    exact mem_ball.mpr ⟨mem_frag hu w3 wne, j, hj, wk⟩
  have := card_le_card sub
  have := le_card_sdiff (layer D V 4 u) (ball D V v k)
  omega

/-- A row that heads `t` inside a `q`-free fragment has a larger ball one radius further. -/
theorem ball_succ_head {S : Finset ℕ} (free : QFree D S q) {z t k : ℕ} (hz : z ∈ S)
    (ht : t ∈ S) (zt : D z t = true) (hk : k + 1 ≤ q) :
    (ball D S t k).card + 1 ≤ (ball D S z (k + 1)).card := by
  have out : z ∉ ball D S t k := by
    intro h
    obtain ⟨-, j, hj, w⟩ := mem_ball.mp h
    exact free t (j + 1) (by omega) (by omega) (w.snoc ht zt)
  have sub : insert z (ball D S t k) ⊆ ball D S z (k + 1) := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact self_mem_ball hz
    · obtain ⟨wS, j, hj, wk⟩ := mem_ball.mp hw
      exact mem_ball.mpr ⟨wS, j + 1, by omega, .step ht zt wk⟩
  have := card_le_card sub
  rw [card_insert_of_notMem out] at this
  exact this

/-- Balls of a fragment of minimum out-degree two grow by one per radius below `2q + 1`. -/
theorem grow_iter {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (m2 : ∀ v ∈ S, 2 ≤ (outN D S v).card) {v : ℕ} (hv : v ∈ S) (a k : ℕ) :
    min ((ball D S v a).card + k) (2 * q + 1) ≤ (ball D S v (a + k)).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have mono : (ball D S v (a + k)).card ≤ (ball D S v (a + (k + 1))).card :=
      card_le_card (ball_mono_radius (by omega))
    by_cases small : (ball D S v (a + k)).card < 2 * q + 1
    · have := grow_one free hq m2 hv (a + k) small
      rw [show a + k + 1 = a + (k + 1) by omega] at this
      omega
    · omega

/-- The arithmetic of the fragment count (`3` and `q - 3` are the radii). -/
def p7aT (q f2 f3 : ℕ) : ℕ :=
  (q + 2) * (2 * (f3 - q)) +
    (q + 2) * (min (f2 - q + 1) (2 * q + 1) + min (f2 - q + (q - 5)) (2 * q + 1)) +
    q * (7 + (2 * (q - 3) + 1)) +
    ((f2 - q + 1) + (min (f2 - q + (q - 6)) (2 * q + 1) + 1))

def P7aOK (q f2 f3 : ℕ) : Prop := (3 * q + 5) * (3 * q + 5 + 1) < p7aT q f2 f3

instance {q f2 f3 : ℕ} : Decidable (P7aOK q f2 f3) := by unfold P7aOK; infer_instance

/-- **P7a.** On the row `r = q + 2`, `6 ≤ q`: if every root has at least `f2` labels within two
steps and `f3` within three, and `P7aOK q f2 f3`, a root with second layer `q + 2` and third
layer `q + 1` has at least `q + 1` labels in its fourth layer.

With at most `q` labels in the fourth layer `W`, the fragment `S = X ∪ Y ∪ Z` (`3q + 5` labels)
has minimum out-degree two. Its rows of `X` keep at least `f3 - q` labels within three steps,
its rows of `X ∪ Y` at least `f2 - q` within two (`frag_ball_card`), and these grow by one per
step (`grow_iter`); its rows of `Z` have balls of at least `2k + 1` (`ball_growth`). A row of `Z`
heading a row `t` of `X ∪ Y` has balls one larger than those of `t` one radius down
(`ball_succ_head`). The ledger of `S` at radii `3`, `q - 3` then overflows (`P7aOK`), so no row of
`Z` heads back into `X ∪ Y`; then the rows of `Z` keep two heads in `Z`, which has `q + 1`
labels, against `ball_growth`. (Paper source: degree-nine dossier, Appendix 27, fifth bullet,
the case `f₂ = 18`.) -/
theorem p7a_fourth (free : QFree D V q) (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) (h2 : (layer D V 2 u).card = q + 2) (h3 : (layer D V 3 u).card = q + 1)
    {f2 f3 : ℕ} (fl2 : ∀ v ∈ V, f2 ≤ (ball D V v 2).card)
    (fl3 : ∀ v ∈ V, f3 ≤ (ball D V v 3).card) (ok : P7aOK q f2 f3) :
    q + 1 ≤ (layer D V 4 u).card := by
  by_contra small
  push Not at small
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set Z := layer D V 3 u with hZ
  set W := layer D V 4 u with hW
  set S := frag D V u with hS
  have SV : S ⊆ V := frag_subset
  have freeS : QFree D S q := free.mono_set SV
  have XS : ∀ x ∈ X, x ∈ S := fun x hx => mem_union_left _ (mem_union_left _ hx)
  have ZS : ∀ z ∈ Z, z ∈ S := fun z hz => mem_union_right _ hz
  have Xb : ∀ x ∈ X, x ∈ ball D V u 1 := fun x hx => (mem_ball_one hu).mpr (Or.inr hx)
  -- rows of the fragment head only the fragment and `W`
  have keep : ∀ v ∈ S, outN D V v ⊆ S ∪ W := by
    intro v hv t ht
    obtain ⟨v3, vne⟩ := frag_ball free (by omega) hu hv
    obtain ⟨tV, vt⟩ := mem_outN.mp ht
    have t4 : t ∈ ball D V u 4 := ball_step v3 tV vt
    have tne : t ≠ u := fun e => no_back_arc free hu v3 (by omega) (e ▸ vt)
    by_cases tW : t ∈ W
    · exact mem_union_right _ tW
    · refine mem_union_left _ (mem_frag hu ?_ tne)
      by_contra t3
      exact tW (mem_layer.mpr ⟨t4, t3⟩)
  have m2 : ∀ v ∈ S, 2 ≤ (outN D S v).card := by
    intro v hv
    have cover : outN D V v ⊆ outN D S v ∪ W := by
      intro t ht
      rcases mem_union.mp (keep v hv ht) with h | h
      · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp ht).2⟩)
      · exact mem_union_right _ h
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg v (SV hv)] at c
    omega
  have m2' : MinOut2 D S := m2
  by_cases ret : ∃ z ∈ Z, ∃ t ∈ X ∪ Y, D z t = true
  · obtain ⟨z0, hz0, t0, ht0, zt⟩ := ret
    have t0S : t0 ∈ S := mem_union_left _ ht0
    have z0S := ZS z0 hz0
    -- lower bounds
    have twoXY : ∀ t ∈ X ∪ Y, f2 - q ≤ (ball D S t 2).card := by
      intro t ht
      have tb : t ∈ ball D V u 2 := by
        rcases mem_union.mp ht with h | h
        · exact ball_mono_radius (by omega) (Xb t h)
        · exact (mem_layer.mp h).1
      have tne := (frag_ball free (by omega) hu (mem_union_left _ ht)).2
      have e1 : (ball D V t 2).card ≤ (ball D S t 2).card + W.card :=
        frag_ball_card free (by omega) hu tb tne (k := 2) (by omega)
      have := fl2 t (SV (mem_union_left _ ht))
      omega
    have growXY : ∀ t ∈ X ∪ Y, ∀ k, min (f2 - q + k) (2 * q + 1) ≤ (ball D S t (2 + k)).card := by
      intro t ht k
      have := grow_iter freeS (by omega) m2 (mem_union_left _ ht) 2 k
      have := twoXY t ht
      omega
    have bX : ∀ x ∈ X, 2 * (f3 - q) ≤
        (ball D S x 3).card + (ball D S x (q - 3)).card := by
      intro x hx
      have e1 : (ball D V x 3).card ≤ (ball D S x 3).card + W.card :=
        frag_ball_card free (by omega) hu (Xb x hx) (frag_ball free (by omega) hu (XS x hx)).2
          (k := 3) (by omega)
      have := fl3 x (SV (XS x hx))
      have mono : (ball D S x 3).card ≤ (ball D S x (q - 3)).card :=
        card_le_card (ball_mono_radius (by omega))
      omega
    have bY : ∀ y ∈ Y, min (f2 - q + 1) (2 * q + 1) + min (f2 - q + (q - 5)) (2 * q + 1) ≤
        (ball D S y 3).card + (ball D S y (q - 3)).card := by
      intro y hy
      have a := growXY y (mem_union_right _ hy) 1
      have b := growXY y (mem_union_right _ hy) (q - 5)
      rw [show 2 + 1 = 3 from rfl] at a
      rw [show 2 + (q - 5) = q - 3 by omega] at b
      omega
    have bZ : ∀ z ∈ Z, 7 + (2 * (q - 3) + 1) ≤
        (ball D S z 3).card + (ball D S z (q - 3)).card := by
      intro z hz
      have a := ball_growth q (by omega) D S freeS m2' z (ZS z hz) 3 (by omega)
      have b := ball_growth q (by omega) D S freeS m2' z (ZS z hz) (q - 3) (by omega)
      omega
    have bR : (f2 - q + 1) + (min (f2 - q + (q - 6)) (2 * q + 1) + 1) ≤
        (ball D S z0 3).card + (ball D S z0 (q - 3)).card := by
      have a := ball_succ_head freeS z0S t0S zt (k := 2) (by omega)
      have b := ball_succ_head freeS z0S t0S zt (k := q - 4) (by omega)
      rw [show 2 + 1 = 3 from rfl] at a
      rw [show q - 4 + 1 = q - 3 by omega] at b
      have c := twoXY t0 ht0
      have d := growXY t0 ht0 (q - 6)
      rw [show 2 + (q - 6) = q - 4 by omega] at d
      omega
    -- the ledger
    have dXY : Disjoint X Y := by
      rw [disjoint_left]
      intro v hx hy
      exact (mem_layer.mp hy).2 (Xb v hx)
    have dXYZ : Disjoint (X ∪ Y) Z := by
      rw [disjoint_left]
      intro v hv hz
      rcases mem_union.mp hv with h | h
      · exact (mem_layer.mp hz).2 (ball_mono_radius (by omega) (Xb v h))
      · exact (mem_layer.mp hz).2 (mem_layer.mp h).1
    have eSf : S = (X ∪ Y) ∪ Z := rfl
    have cS : S.card = 3 * q + 5 := by
      rw [eSf, card_union_of_disjoint dXYZ, card_union_of_disjoint dXY, h2, h3, hX, reg u hu]
      omega
    have led := ReachLedger.ledger (D := D) (V := S) (i := 3) (j := q - 3) freeS (by omega)
    rw [cS] at led
    set F : ℕ → ℕ := fun v => (ball D S v 3).card + (ball D S v (q - 3)).card with hF
    have eS : ∑ v ∈ S, (ball D S v 3).card + ∑ v ∈ S, (ball D S v (q - 3)).card =
        ∑ v ∈ S, F v := by rw [hF, ← sum_add_distrib]
    have split : ∑ v ∈ S, F v = ∑ v ∈ X, F v + ∑ v ∈ Y, F v + (F z0 + ∑ v ∈ Z.erase z0, F v) := by
      rw [eSf, sum_union dXYZ, sum_union dXY, ← add_sum_erase Z F hz0]
    have sX := card_nsmul_le_sum X F (2 * (f3 - q)) bX
    have sY := card_nsmul_le_sum Y F _ bY
    have sZ := card_nsmul_le_sum (Z.erase z0) F _ (fun z hz => bZ z (mem_of_mem_erase hz))
    have cX : X.card = q + 2 := by rw [hX, reg u hu]
    rw [smul_eq_mul, cX] at sX
    rw [smul_eq_mul, h2] at sY
    rw [smul_eq_mul, card_erase_of_mem hz0, h3, Nat.add_sub_cancel] at sZ
    have bR' : (f2 - q + 1) + (min (f2 - q + (q - 6)) (2 * q + 1) + 1) ≤ F z0 := bR
    unfold P7aOK p7aT at ok
    generalize ∑ v ∈ S, F v = sF at eS split
    generalize ∑ v ∈ X, F v = sXv at split sX
    generalize ∑ v ∈ Y, F v = sYv at split sY
    generalize ∑ v ∈ Z.erase z0, F v = sZv at split sZ
    generalize F z0 = fz at split bR'
    generalize ∑ v ∈ S, (ball D S v 3).card = s3 at led eS
    generalize ∑ v ∈ S, (ball D S v (q - 3)).card = sb at led eS
    generalize ∑ v ∈ S, (ReachLedger.gap D S 3 (q - 3) v).card = sg at led
    generalize (q + 2) * (2 * (f3 - q)) = P1 at ok sX
    generalize (q + 2) * (min (f2 - q + 1) (2 * q + 1) + min (f2 - q + (q - 5)) (2 * q + 1))
      = P2 at ok sY
    generalize q * (7 + (2 * (q - 3) + 1)) = P3 at ok sZ
    generalize (3 * q + 5) * (3 * q + 5 + 1) = N at ok led
    omega
  · push Not at ret
    have zkeep : ∀ z ∈ Z, outN D V z ⊆ Z ∪ W := by
      intro z hz t ht
      rcases mem_union.mp (keep z (ZS z hz) ht) with h | h
      · rcases mem_union.mp h with h' | h'
        · exact absurd (mem_outN.mp ht).2 (ret z hz t h')
        · exact mem_union_left _ h'
      · exact mem_union_right _ h
    have inner := DipCost.layer_host (X := Z) (Y := W) (c := 2)
      (fun z hz => (reg z (layer_subset hz)).ge) zkeep (by omega)
    obtain ⟨z, hz⟩ : Z.Nonempty := card_pos.mp (by omega)
    have big := ball_growth q (by omega) D Z (free.mono_set layer_subset)
      (fun v hv => inner v hv) z hz q le_rfl
    have := card_le_card (ball_subset (D := D) (W := Z) (u := z) (k := q))
    omega

end p7a

/-! ### The patterns -/

section patterns
open ShapeClimbAvoid (Avoids)

/-- Either pattern. -/
def orA (A B : List ℕ → ℕ → Bool) : List ℕ → ℕ → Bool := fun ws last => A ws last || B ws last

theorem avoids_or {V : Finset ℕ} {u : ℕ} {A B : List ℕ → ℕ → Bool} (a : Avoids D V u A)
    (b : Avoids D V u B) : Avoids D V u (orA A B) := by
  intro ws last exact bound
  simp only [orA, a ws last exact bound, b ws last exact bound, Bool.or_false]

/-- P7b: widths `(r, r - 1, r)` and a fourth layer of at most `r - 2`. -/
def p7bA (r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (3 ≤ ws.length ∧ ws.getD 1 0 + 1 = r ∧ ws.getD 2 0 = r ∧
    (if 4 ≤ ws.length then ws.getD 3 0 else last) + 2 ≤ r)

/-- Q: widths `(r, r - 1, r - 1, r - 1)` and a fifth layer of at most `r - 2`. -/
def qA (r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (4 ≤ ws.length ∧ ws.getD 1 0 + 1 = r ∧ ws.getD 2 0 + 1 = r ∧ ws.getD 3 0 + 1 = r ∧
    (if 5 ≤ ws.length then ws.getD 4 0 else last) + 2 ≤ r)

variable {V : Finset ℕ} {u : ℕ}

/-- Every root on the row `r = q + 2`, `4 ≤ q`, avoids P7b. -/
theorem avoids_p7b (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) : Avoids D V u (p7bA (q + 2)) := by
  intro ws last exact bound
  simp only [p7bA, decide_eq_false_iff_not]
  rintro ⟨len, w2, w3, w4⟩
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := p7b_fourth free hq reg hu (by omega) (by omega)
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    rw [show ws.length + 1 = 4 by omega] at bound
    omega

/-- P7a: widths `(r, r, r - 1)` and a fourth layer of at most `r - 2`, `r = q + 2`, when the
floors `fs` of every root pass `P7aOK` at radii two and three. -/
def p7aA (q : ℕ) (fs : List ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (6 ≤ q ∧ P7aOK q (fs.getD 2 0) (fs.getD 3 0) ∧ 3 ≤ ws.length ∧ ws.getD 1 0 = q + 2 ∧
    ws.getD 2 0 = q + 1 ∧ (if 4 ≤ ws.length then ws.getD 3 0 else last) ≤ q)

/-- Every root on the row `r = q + 2` avoids P7a over floors valid for every root. -/
theorem avoids_p7a (free : QFree D V q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) {fs : List ℕ} (floors : ∀ i, MixedRadiusCompletion.Floor q (q + 2) i (fs.getD i 0)) :
    Avoids D V u (p7aA q fs) := by
  intro ws last exact bound
  simp only [p7aA, decide_eq_false_iff_not]
  rintro ⟨hq, ok, len, w2, w3, w4⟩
  have deg : ∀ v ∈ V, q + 2 ≤ (outN D V v).card := fun v hv => (reg v hv).ge
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have fourth := p7a_fourth free hq reg hu (by omega) (by omega)
    (fun v hv => floors 2 D V free deg v hv) (fun v hv => floors 3 D V free deg v hv) ok
  by_cases long : 4 ≤ ws.length
  · have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
    simp only [long, ↓reduceIte] at w4
    omega
  · simp only [long, ↓reduceIte] at w4
    rw [show ws.length + 1 = 4 by omega] at bound
    omega

/-- Every root on the row `r = q + 2`, `5 ≤ q`, avoids Q. -/
theorem avoids_q (free : QFree D V q) (hq : 5 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 2)
    (hu : u ∈ V) : Avoids D V u (qA (q + 2)) := by
  intro ws last exact bound
  simp only [qA, decide_eq_false_iff_not]
  rintro ⟨len, w2, w3, w4, w5⟩
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
  have l4 : (layer D V 4 u).card = ws.getD 3 0 := exact 3 (by omega)
  have fifth := q_fifth free hq reg hu (by omega) (by omega) (by omega)
  by_cases long : 5 ≤ ws.length
  · have l5 : (layer D V 5 u).card = ws.getD 4 0 := exact 4 (by omega)
    simp only [long, ↓reduceIte] at w5
    omega
  · simp only [long, ↓reduceIte] at w5
    rw [show ws.length + 1 = 5 by omega] at bound
    omega

/-- A tight root (`CollarTwo.Tight`), `5 ≤ q`, avoids `notTightA (q + 2)` and Q. -/
theorem tight_avoids (free : QFree D V q) (hq : 5 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2) (hu : u ∈ V) (tight : CollarTwo.Tight D V q u) :
    Avoids D V u (orA (ShapeClimbAvoid.notTightA (q + 2)) (qA (q + 2))) := by
  obtain ⟨-, z, -⟩ := CollarTwo.loop_complete free (by omega) reg hu tight
  exact avoids_or (ShapeClimbAvoid.avoids_notTight (by rw [tight.1]) (by rw [z]))
    (avoids_q free hq reg hu)

end patterns

#print axioms grow_one
#print axioms ball_two_of_heads
#print axioms p7b_z_no_x
#print axioms p7b_fourth
#print axioms loop_next
#print axioms head_to_second
#print axioms q_fifth
#print axioms avoids_or
#print axioms avoids_p7b
#print axioms avoids_q
#print axioms tight_avoids
#print axioms frag_walk
#print axioms frag_ball_card
#print axioms ball_succ_head
#print axioms grow_iter
#print axioms p7a_fourth
#print axioms avoids_p7a
end LeanCH.BR.TightFloors
