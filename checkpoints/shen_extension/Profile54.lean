import checkpoints.shen_extension.ThinSuppliers
import checkpoints.shen_extension.ShapeClimbMono

/-!
# Layer profiles at a root of a 6-free 9-regular digraph

Lean 4.35.0. A root `u` of a `q`-free digraph on `V` with every out-degree `r` has heads
`X = outN D V u`, second layer `Y = layer D V 2 u` and third layer `Z = layer D V 3 u`.
`inner D V u = X ∪ Y` (the punctured two-ball).

Fragments (generic in a `q`-free set `W`; `reach D W i x` = other labels within `i` steps):
* `shell_step`: a punctured `k`-ball of at most `q c` labels gains at least `d + 1 - c` labels at
  radius `k + 1` (`NoHost q c`, rows of out-degree `≥ d`, `k + 1 ≤ q`).
* `growth_facts` and the table (Lemma 3, `q = 6`): `reach_three_two` (`d ≥ 2`: `≥ 6`),
  `reach_three_three` (`≥ 9`), `reach_three_four` (`≥ 11`), `reach_three_five` (`≥ 13`);
  `head_reach` (generic) and `nine_row` (`q = 6`): a row with nine heads in a fragment of minimum
  out-degree two has `reach 3 ≥ 12`.
* `pair_budget` (Lemma P): `2 Σ reach k ≤ |W| (|W| - 1)` for `2k ≤ q`; `budget_floor`: the same
  with floors `a` on `X ⊆ W` and `b` off `X`.

Roots:
* `x_keep`, `y_keep`, `inner_card` (Lemma 1, generic in `q`, `r`): inside `X ∪ Y` the rows of `X`
  keep all `r` heads (`2 ≤ q`) and the rows of `Y` keep at least `r - |Z|` heads (`3 ≤ q`);
  `|X ∪ Y| = r + |Y|`.
* `wide_second` (Theorem 2, generic): with `c ≥ 1`, `c + |Z| ≤ r` and `r + |Y| ≤ q c`, the closed
  lower degree `c` (`NoHost q c`) is contradicted. `profile_wide`: at `q = 6`, `r = 9`,
  `|Y| + |Z| = 17` and `|Y| ≥ 12` is impossible (lower degree `|Y| - 8`, or `8` when `Z = ∅`).
* `one_short` (generic): a nonempty `q`-free set in which every row has a head and all rows but
  one have two heads has at least `2q + 1` labels (`ThinSuppliers.lone_count`).
* `head_second`, `head_third` (generic): in a `q`-free set of minimum out-degree two, a row with
  `n` heads, `n + 2 ≤ 2q`, has `|B_2| ≥ n + 2` (`2 ≤ q`) and `|B_3| ≥ n + 4` (`3 ≤ q`).
* `back_ball` (generic): a row pointing to `x` has `|B_3| ≥ |B_2(x)| + 1` (`3 ≤ q`).
* `core` and `profile_10_7` (Theorem 3): the profile `(|Y|, |Z|) = (10, 7)` is impossible at
  `q = 6`, `r = 9`, by the pair budget `ReachLedger.ledger` at radii `(3, 3)` inside `X ∪ Y`.
* `root_budget`, `no_wide_27`, `thin_26` (Lemma 10): at `|B_3| = 27` no root has `|Y| ≥ 10`;
  at `|B_3| = 26` every root has profile `(8, 8)`.
* `profile_cases` (Corollary 4): `|Y| ≥ 9` and `|B_3| = 27` force `(9, 8)`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.Profile54
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open BypassRepair (NoHost)

variable {D : CH.Digraph}

/-- The closed lower degrees are `1 … 8`. -/
theorem floor_nine : ProjectedQuotaTransfer.projectionFloor = 9 := rfl

/-- The other labels of `F` within `i` steps of `x` inside `F`. -/
noncomputable def reach (D : CH.Digraph) (F : Finset ℕ) (i x : ℕ) : ℕ := ((ball D F x i).erase x).card

/-! ### Degree-two orders inside a set -/

section inside
variable {W : Finset ℕ} {q : ℕ}

/-- A nonempty `q`-free set where every row has a head and every row but `y` has two heads has
at least `2q + 1` labels. -/
theorem one_short {S : Finset ℕ} {y : ℕ} (free : QFree D S q) (hq : 1 ≤ q) (ne : S.Nonempty)
    (one : ∀ v ∈ S, 1 ≤ (outN D S v).card) (two : ∀ v ∈ S, v ≠ y → 2 ≤ (outN D S v).card) :
    2 * q + 1 ≤ S.card := by
  by_contra h
  have lc := ThinSuppliers.lone_count (D := D) free hq one ne (by omega)
  have sub : ThinSuppliers.lone D S ⊆ {y} := by
    intro v hv
    obtain ⟨vS, le⟩ := ThinSuppliers.mem_lone.mp hv
    by_contra hy
    have := two v vS (fun e => hy (mem_singleton.mpr e))
    omega
  have := card_le_card sub
  rw [card_singleton] at this
  omega

/-- Minimum out-degree two: at least `2q + 1` labels. -/
theorem two_order {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q) (ne : S.Nonempty)
    (deg : ∀ v ∈ S, 2 ≤ (outN D S v).card) : 2 * q + 1 ≤ S.card :=
  one_short (y := 0) free hq ne (fun v hv => by have := deg v hv; omega) (fun v hv _ => deg v hv)

theorem out_restrict {S : Finset ℕ} {v : ℕ} (sub : S ⊆ W) (keep : outN D W v ⊆ S) :
    outN D S v = outN D W v := by
  ext w
  constructor
  · intro h
    obtain ⟨a, b⟩ := mem_outN.mp h
    exact mem_outN.mpr ⟨sub a, b⟩
  · intro h
    exact mem_outN.mpr ⟨keep h, (mem_outN.mp h).2⟩

theorem card_ball_erase {x k : ℕ} (hx : x ∈ W) :
    ((ball D W x k).erase x).card + 1 = (ball D W x k).card :=
  card_erase_add_one (self_mem_ball hx)

/-- A head of a row of the `k`-ball lies in the punctured `(k+1)`-ball, `k + 1 ≤ q`. -/
theorem step_erase (free : QFree D W q) {x k v w : ℕ} (hx : x ∈ W) (hk : k + 1 ≤ q)
    (hv : v ∈ ball D W x k) (hw : w ∈ outN D W v) : w ∈ (ball D W x (k + 1)).erase x := by
  obtain ⟨wW, vw⟩ := mem_outN.mp hw
  refine mem_erase.mpr ⟨?_, ball_step hv wW vw⟩
  intro e
  rw [e] at vw
  exact no_back_arc free hx hv hk vw

theorem heads_sub (free : QFree D W q) (hq : 2 ≤ q) {x : ℕ} (hx : x ∈ W) :
    outN D W x ⊆ (ball D W x 2).erase x := by
  intro v hv
  refine mem_erase.mpr ⟨?_, ?_⟩
  · intro e
    rw [e] at hv
    exact loopfree free (by omega) hx (mem_outN.mp hv).2
  · exact ball_mono_radius (by omega) ((mem_ball_one hx).mpr (Or.inr hv))

/-- **Second ball.** A row with `n` heads, `n + 2 ≤ 2q`, in a `q`-free set of minimum
out-degree two: its heads are not closed, so `|B_2| ≥ n + 2`. -/
theorem head_second (free : QFree D W q) (hq : 2 ≤ q) {x : ℕ} (hx : x ∈ W)
    (hn : (outN D W x).card + 2 ≤ 2 * q) (deg : ∀ v ∈ W, 2 ≤ (outN D W v).card) :
    (outN D W x).card + 2 ≤ (ball D W x 2).card := by
  have NW : outN D W x ⊆ W := outN_subset
  have NS2 := heads_sub free hq hx
  have k1 : ∀ v ∈ outN D W x, outN D W v ⊆ (ball D W x 2).erase x := fun v hv w hw =>
    step_erase free hx (k := 1) (by omega) ((mem_ball_one hx).mpr (Or.inr hv)) hw
  have c2 := card_ball_erase (D := D) (k := 2) hx
  by_contra h
  have eq : outN D W x = (ball D W x 2).erase x := eq_of_subset_of_card_le NS2 (by omega)
  have ne : (outN D W x).Nonempty := card_pos.mp (by have := deg x hx; omega)
  have := two_order (free.mono_set NW) (by omega) ne (fun v hv => by
    rw [out_restrict NW (by rw [eq]; exact k1 v hv)]
    exact deg v (NW hv))
  omega

/-- **Third ball.** A row with `n` heads, `n + 2 ≤ 2q`, in a `q`-free set of minimum
out-degree two has `|B_3| ≥ n + 4`. -/
theorem head_third (free : QFree D W q) (hq : 3 ≤ q) {x : ℕ} (hx : x ∈ W)
    (hn : (outN D W x).card + 2 ≤ 2 * q) (deg : ∀ v ∈ W, 2 ≤ (outN D W v).card) :
    (outN D W x).card + 4 ≤ (ball D W x 3).card := by
  have A := head_second free (by omega) hx hn deg
  have c2 := card_ball_erase (D := D) (k := 2) hx
  have c3 := card_ball_erase (D := D) (k := 3) hx
  have S2W : (ball D W x 2).erase x ⊆ W := (erase_subset _ _).trans ball_subset
  have S23 : (ball D W x 2).erase x ⊆ (ball D W x 3).erase x :=
    erase_subset_erase x (ball_mono_radius (by omega))
  have NS2 := heads_sub free (by omega) hx
  have k2 : ∀ v ∈ (ball D W x 2).erase x, outN D W v ⊆ (ball D W x 3).erase x :=
    fun v hv w hw => step_erase free hx (k := 2) (by omega) (mem_of_mem_erase hv) hw
  have k1 : ∀ v ∈ outN D W x, outN D W v ⊆ (ball D W x 2).erase x := fun v hv w hw =>
    step_erase free hx (k := 1) (by omega) ((mem_ball_one hx).mpr (Or.inr hv)) hw
  have ne : (outN D W x).Nonempty := card_pos.mp (by have := deg x hx; omega)
  obtain ⟨v0, hv0⟩ := ne
  by_contra h
  have le23 := card_le_card S23
  have B : ((ball D W x 2).erase x).card + 1 ≤ ((ball D W x 3).erase x).card := by
    by_contra hB
    have eq : (ball D W x 2).erase x = (ball D W x 3).erase x :=
      eq_of_subset_of_card_le S23 (by omega)
    have := two_order (free.mono_set S2W) (by omega) ⟨v0, NS2 hv0⟩ (fun v hv => by
      rw [out_restrict S2W (by rw [eq]; exact k2 v hv)]
      exact deg v (S2W hv))
    omega
  have one2 : (((ball D W x 2).erase x) \ outN D W x).card = 1 := by
    rw [card_sdiff_of_subset NS2]; omega
  have one3 : (((ball D W x 3).erase x) \ (ball D W x 2).erase x).card = 1 := by
    rw [card_sdiff_of_subset S23]; omega
  obtain ⟨y, hy⟩ := card_eq_one.mp one2
  obtain ⟨e, he⟩ := card_eq_one.mp one3
  have yS2 : y ∈ (ball D W x 2).erase x := by
    have : y ∈ ((ball D W x 2).erase x) \ outN D W x := by rw [hy]; exact mem_singleton_self y
    exact (mem_sdiff.mp this).1
  have onlyY : ∀ v ∈ (ball D W x 2).erase x, v ≠ y → v ∈ outN D W x := by
    intro v hv hne
    by_contra hn'
    have : v ∈ ((ball D W x 2).erase x) \ outN D W x := mem_sdiff.mpr ⟨hv, hn'⟩
    rw [hy] at this
    exact hne (mem_singleton.mp this)
  have yone : 1 ≤ (outN D ((ball D W x 2).erase x) y).card := by
    have cover : outN D W y ⊆ outN D ((ball D W x 2).erase x) y ∪ {e} := by
      intro w hw
      by_cases ws : w ∈ (ball D W x 2).erase x
      · exact mem_union_left _ (mem_outN.mpr ⟨ws, (mem_outN.mp hw).2⟩)
      · apply mem_union_right
        have : w ∈ ((ball D W x 3).erase x) \ (ball D W x 2).erase x :=
          mem_sdiff.mpr ⟨k2 y yS2 hw, ws⟩
        rw [he] at this
        exact this
    have := (card_le_card cover).trans (card_union_le _ _)
    rw [card_singleton] at this
    have := deg y (S2W yS2)
    omega
  have two : ∀ v ∈ (ball D W x 2).erase x, v ≠ y →
      2 ≤ (outN D ((ball D W x 2).erase x) v).card := by
    intro v hv hne
    have vN := onlyY v hv hne
    rw [out_restrict S2W (k1 v vN)]
    exact deg v (S2W hv)
  have := one_short (free.mono_set S2W) (by omega) ⟨y, yS2⟩
    (fun v hv => by
      by_cases hvy : v = y
      · rw [hvy]; exact yone
      · have := two v hv hvy; omega)
    two
  omega

/-- **Back arc.** A row pointing to `x` sees the two-ball of `x` within three steps, and is not in
it. -/
theorem back_ball (free : QFree D W q) (hq : 3 ≤ q) {x y : ℕ} (hx : x ∈ W) (hy : y ∈ W)
    (yx : D y x = true) : (ball D W x 2).card + 1 ≤ (ball D W y 3).card := by
  have notin : y ∉ ball D W x 2 := by
    intro h
    obtain ⟨-, j, hj, w⟩ := mem_ball.mp h
    exact free x (j + 1) (by omega) (by omega) (w.snoc hx yx)
  have sub : insert y (ball D W x 2) ⊆ ball D W y 3 := by
    intro z hz
    rcases mem_insert.mp hz with e | hz
    · rw [e]; exact self_mem_ball hy
    · obtain ⟨zW, j, hj, w⟩ := mem_ball.mp hz
      exact mem_ball.mpr ⟨zW, j + 1, by omega, Walk.step hx yx w⟩
  have := card_le_card sub
  rw [card_insert_of_notMem notin] at this
  exact this

/-! ### Lemma 3: the growth table -/

/-- **Shell step.** Rows of the punctured `k`-ball (`k + 1 ≤ q`) do not point to `x`, so with `e`
new labels at radius `k + 1` they keep `d - e` heads inside; a closed lower degree `c` on at most
`q c` labels forces `e ≥ d + 1 - c`. -/
theorem shell_step (free : QFree D W q) {x k d c : ℕ} (hx : x ∈ W) (hk : k + 1 ≤ q)
    (host : NoHost q c) (deg : ∀ v ∈ W, d ≤ (outN D W v).card)
    (ne : ((ball D W x k).erase x).Nonempty) (small : ((ball D W x k).erase x).card ≤ q * c) :
    ((ball D W x k).erase x).card + d + 1 ≤ ((ball D W x (k + 1)).erase x).card + c := by
  have PW : (ball D W x k).erase x ⊆ W := (erase_subset _ _).trans ball_subset
  have PP : (ball D W x k).erase x ⊆ (ball D W x (k + 1)).erase x :=
    erase_subset_erase x (ball_mono_radius (by omega))
  have cd := card_sdiff_of_subset PP
  have le := card_le_card PP
  by_contra h
  refine host D _ ne small (free.mono_set PW) ?_
  intro v hv
  have cover : outN D W v ⊆ outN D ((ball D W x k).erase x) v ∪
      (((ball D W x (k + 1)).erase x) \ (ball D W x k).erase x) := by
    intro w hw
    by_cases ws : w ∈ (ball D W x k).erase x
    · exact mem_union_left _ (mem_outN.mpr ⟨ws, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _
        (mem_sdiff.mpr ⟨step_erase free hx hk (mem_of_mem_erase hv) hw, ws⟩)
  have := (card_le_card cover).trans (card_union_le _ _)
  have := deg v (PW hv)
  omega

/-- **Growth facts.** In a `q`-free set with out-degrees `≥ d ≥ 1`: `reach 1 ≥ d`, monotone
reaches, and the shell steps with the lower degrees one (`≤ q` labels) and two (`≤ 2q`). -/
theorem growth_facts (free : QFree D W q) (hq : 3 ≤ q) {x d : ℕ} (hx : x ∈ W) (hd : 1 ≤ d)
    (deg : ∀ v ∈ W, d ≤ (outN D W v).card) :
    d ≤ reach D W 1 x ∧ reach D W 1 x ≤ reach D W 2 x ∧ reach D W 2 x ≤ reach D W 3 x ∧
      (q < reach D W 1 x ∨ reach D W 1 x + d ≤ reach D W 2 x) ∧
      (2 * q < reach D W 1 x ∨ reach D W 1 x + d ≤ reach D W 2 x + 1) ∧
      (q < reach D W 2 x ∨ reach D W 2 x + d ≤ reach D W 3 x) ∧
      (2 * q < reach D W 2 x ∨ reach D W 2 x + d ≤ reach D W 3 x + 1) := by
  have h1 : outN D W x ⊆ (ball D W x 1).erase x := by
    intro v hv
    refine mem_erase.mpr ⟨?_, (mem_ball_one hx).mpr (Or.inr hv)⟩
    intro e
    rw [e] at hv
    exact loopfree free (by omega) hx (mem_outN.mp hv).2
  have g1 : d ≤ ((ball D W x 1).erase x).card := (deg x hx).trans (card_le_card h1)
  have s12 : (ball D W x 1).erase x ⊆ (ball D W x 2).erase x :=
    erase_subset_erase x (ball_mono_radius (by omega))
  have s23 : (ball D W x 2).erase x ⊆ (ball D W x 3).erase x :=
    erase_subset_erase x (ball_mono_radius (by omega))
  have ne1 : ((ball D W x 1).erase x).Nonempty := card_pos.mp (by omega)
  have ne2 : ((ball D W x 2).erase x).Nonempty := Nonempty.mono s12 ne1
  have host1 : NoHost q 1 := ShapeClimbMono.lower_hosts_every q 1 (by rw [floor_nine]; norm_num)
  have host2 : NoHost q 2 := ShapeClimbMono.lower_hosts_every q 2 (by rw [floor_nine]; norm_num)
  have m12 := card_le_card s12
  have m23 := card_le_card s23
  unfold reach
  refine ⟨g1, m12, m23, ?_, ?_, ?_, ?_⟩
  · by_cases h : ((ball D W x 1).erase x).card ≤ q
    · have : ((ball D W x 1).erase x).card + d + 1 ≤ ((ball D W x 2).erase x).card + 1 :=
        shell_step free hx (k := 1) (by omega) host1 deg ne1 (by omega)
      omega
    · omega
  · by_cases h : ((ball D W x 1).erase x).card ≤ 2 * q
    · have : ((ball D W x 1).erase x).card + d + 1 ≤ ((ball D W x 2).erase x).card + 2 :=
        shell_step free hx (k := 1) (by omega) host2 deg ne1 (by omega)
      omega
    · omega
  · by_cases h : ((ball D W x 2).erase x).card ≤ q
    · have : ((ball D W x 2).erase x).card + d + 1 ≤ ((ball D W x 3).erase x).card + 1 :=
        shell_step free hx (k := 2) (by omega) host1 deg ne2 (by omega)
      omega
    · omega
  · by_cases h : ((ball D W x 2).erase x).card ≤ 2 * q
    · have : ((ball D W x 2).erase x).card + d + 1 ≤ ((ball D W x 3).erase x).card + 2 :=
        shell_step free hx (k := 2) (by omega) host2 deg ne2 (by omega)
      omega
    · omega

/-- **Lemma 3, `d ≥ 2`.** -/
theorem reach_three_two (free : QFree D W 6) {x d : ℕ} (hx : x ∈ W) (hd : 2 ≤ d)
    (deg : ∀ v ∈ W, d ≤ (outN D W v).card) : 6 ≤ reach D W 3 x := by
  obtain ⟨a, b, c, e, f, g, h⟩ := growth_facts free (by norm_num) hx (by omega) deg
  omega

/-- **Lemma 3, `d ≥ 3`.** -/
theorem reach_three_three (free : QFree D W 6) {x d : ℕ} (hx : x ∈ W) (hd : 3 ≤ d)
    (deg : ∀ v ∈ W, d ≤ (outN D W v).card) : 9 ≤ reach D W 3 x := by
  obtain ⟨a, b, c, e, f, g, h⟩ := growth_facts free (by norm_num) hx (by omega) deg
  omega

/-- **Lemma 3, `d ≥ 4`.** -/
theorem reach_three_four (free : QFree D W 6) {x d : ℕ} (hx : x ∈ W) (hd : 4 ≤ d)
    (deg : ∀ v ∈ W, d ≤ (outN D W v).card) : 11 ≤ reach D W 3 x := by
  obtain ⟨a, b, c, e, f, g, h⟩ := growth_facts free (by norm_num) hx (by omega) deg
  omega

/-- **Lemma 3, `d ≥ 5`.** -/
theorem reach_three_five (free : QFree D W 6) {x d : ℕ} (hx : x ∈ W) (hd : 5 ≤ d)
    (deg : ∀ v ∈ W, d ≤ (outN D W v).card) : 13 ≤ reach D W 3 x := by
  obtain ⟨a, b, c, e, f, g, h⟩ := growth_facts free (by norm_num) hx (by omega) deg
  omega

/-- A row with `n` heads, `n + 2 ≤ 2q`, in a `q`-free set of minimum out-degree two reaches at
least `n + 3` other labels within three steps. -/
theorem head_reach (free : QFree D W q) (hq : 3 ≤ q) {x : ℕ} (hx : x ∈ W)
    (hn : (outN D W x).card + 2 ≤ 2 * q) (deg : ∀ v ∈ W, 2 ≤ (outN D W v).card) :
    (outN D W x).card + 3 ≤ reach D W 3 x := by
  have := head_third free hq hx hn deg
  have := card_ball_erase (D := D) (k := 3) hx
  unfold reach
  omega

/-- **Lemma 3, nine heads.** At `q = 6`, a row with nine heads in a fragment of minimum
out-degree two reaches at least `12` other labels within three steps. -/
theorem nine_row (free : QFree D W 6) {x : ℕ} (hx : x ∈ W) (nine : (outN D W x).card = 9)
    (deg : ∀ v ∈ W, 2 ≤ (outN D W v).card) : 12 ≤ reach D W 3 x := by
  have := head_reach free (by norm_num) hx (by omega) deg
  omega

/-! ### Lemma P: the pair budget -/

/-- **Lemma P.** In a `q`-free set, `2k ≤ q`: no two labels see each other both ways within `k`
steps, so `2 Σ_x reach k x ≤ |W| (|W| - 1)`. -/
theorem pair_budget (free : QFree D W q) {k : ℕ} (hk : 2 * k ≤ q) :
    2 * ∑ x ∈ W, reach D W k x ≤ W.card * (W.card - 1) := by
  have led := ReachLedger.ledger (D := D) (V := W) (q := q) (i := k) (j := k) free (by omega)
  have e : ∑ x ∈ W, (ball D W x k).card = ∑ x ∈ W, (reach D W k x + 1) :=
    sum_congr rfl (fun x hx => (card_ball_erase hx).symm)
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at e
  rw [e, mul_add, mul_one] at led
  rw [Nat.mul_sub_one]
  generalize W.card * W.card = M at led ⊢
  omega

/-- **Lemma P with floors.** Floors `a` on `X ⊆ W` and `b` on `W \ X`. -/
theorem budget_floor (free : QFree D W q) (hq : 6 ≤ q) {X : Finset ℕ} (XW : X ⊆ W) {a b : ℕ}
    (onX : ∀ x ∈ X, a ≤ reach D W 3 x) (off : ∀ v ∈ W \ X, b ≤ reach D W 3 v) :
    2 * (X.card * a + (W \ X).card * b) ≤ W.card * (W.card - 1) := by
  have split : ∑ v ∈ W \ X, reach D W 3 v + ∑ v ∈ X, reach D W 3 v
      = ∑ v ∈ W, reach D W 3 v := sum_sdiff XW
  have sX : X.card • a ≤ ∑ v ∈ X, reach D W 3 v := card_nsmul_le_sum X _ a onX
  have sY : (W \ X).card • b ≤ ∑ v ∈ W \ X, reach D W 3 v := card_nsmul_le_sum _ _ b off
  calc 2 * (X.card * a + (W \ X).card * b)
      ≤ 2 * (∑ v ∈ X, reach D W 3 v + ∑ v ∈ W \ X, reach D W 3 v) := by
        rw [← smul_eq_mul X.card a, ← smul_eq_mul (W \ X).card b]
        exact Nat.mul_le_mul_left 2 (Nat.add_le_add sX sY)
    _ = 2 * ∑ v ∈ W, reach D W 3 v := by rw [← split, add_comm]
    _ ≤ W.card * (W.card - 1) := pair_budget free (k := 3) (by omega)

end inside

/-! ### Theorem 3, inside the punctured two-ball -/

/-- **Core of Theorem 3.** A `6`-free set of `19` labels with minimum out-degree two, nine of
whose rows have exactly nine heads, does not exist. -/
theorem core {W X : Finset ℕ} (free : QFree D W 6) (XW : X ⊆ W) (hW : W.card = 19)
    (hX : X.card = 9) (xdeg : ∀ x ∈ X, (outN D W x).card = 9)
    (deg : ∀ v ∈ W, 2 ≤ (outN D W v).card) : False := by
  have led := ReachLedger.ledger (D := D) (V := W) (q := 6) (i := 3) (j := 3) free (by norm_num)
  rw [hW] at led
  have ga : ∀ v ∈ W, 7 ≤ (ball D W v 3).card := fun v hv =>
    ball_growth 6 (by norm_num) D W free deg v hv 3 (by norm_num)
  have gb : ∀ x ∈ X, 13 ≤ (ball D W x 3).card := by
    intro x hx
    have := head_third free (by norm_num) (XW hx) (by have := xdeg x hx; omega) deg
    rw [xdeg x hx] at this
    exact this
  have split : ∑ v ∈ W \ X, (ball D W v 3).card + ∑ v ∈ X, (ball D W v 3).card
      = ∑ v ∈ W, (ball D W v 3).card := sum_sdiff XW
  have sX : X.card • 13 ≤ ∑ v ∈ X, (ball D W v 3).card := card_nsmul_le_sum X _ 13 gb
  rw [hX, smul_eq_mul] at sX
  have cY : (W \ X).card = 10 := by rw [card_sdiff_of_subset XW]; omega
  have noBack : ∀ y ∈ W \ X, ∀ x ∈ X, D y x ≠ true := by
    intro y hy x hx yx
    have yW := (mem_sdiff.mp hy).1
    have b2 := head_second free (by norm_num) (XW hx) (by have := xdeg x hx; omega) deg
    rw [xdeg x hx] at b2
    have b3 := back_ball free (by norm_num) (XW hx) yW yx
    have er : (ball D W y 3).card + ∑ v ∈ (W \ X).erase y, (ball D W v 3).card
        = ∑ v ∈ W \ X, (ball D W v 3).card := add_sum_erase _ (fun v => (ball D W v 3).card) hy
    have sE : ((W \ X).erase y).card • 7 ≤ ∑ v ∈ (W \ X).erase y, (ball D W v 3).card :=
      card_nsmul_le_sum _ _ 7 (fun v hv => ga v (mem_sdiff.mp (mem_of_mem_erase hv)).1)
    rw [card_erase_of_mem hy, cY, smul_eq_mul] at sE
    omega
  have Yclosed : ∀ y ∈ W \ X, outN D W y ⊆ W \ X := by
    intro y hy w hw
    obtain ⟨wW, yw⟩ := mem_outN.mp hw
    exact mem_sdiff.mpr ⟨wW, fun wX => noBack y hy w wX yw⟩
  have YW : W \ X ⊆ W := sdiff_subset
  obtain ⟨y0, hy0⟩ : (W \ X).Nonempty := card_pos.mp (by omega)
  have := two_order (free.mono_set YW) (by norm_num) ⟨y0, hy0⟩ (fun v hv => by
    rw [out_restrict YW (Yclosed v hv)]
    exact deg v (YW hv))
  omega

/-! ### Lemma 1: the punctured two-ball of a root -/

section root
variable {V : Finset ℕ} {q r u : ℕ}

/-- `X ∪ Y`: the heads and the second layer of `u`. -/
noncomputable abbrev inner (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  outN D V u ∪ layer D V 2 u

theorem inner_subset : inner D V u ⊆ V := union_subset outN_subset layer_subset

/-- **Lemma 1(a).** A head of the root keeps all its heads in `X ∪ Y` (`2 ≤ q`). -/
theorem x_keep (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) :
    outN D (inner D V u) x = outN D V x :=
  out_restrict inner_subset (LoopCollar.head_keep free hq hu x hx)

/-- **Lemma 1(b).** A row of the second layer keeps at least `r - |Z|` heads in `X ∪ Y`
(`3 ≤ q`). -/
theorem y_keep (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) {y : ℕ} (hy : y ∈ layer D V 2 u) :
    r ≤ (outN D (inner D V u) y).card + (layer D V 3 u).card := by
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have yV : y ∈ V := ball_subset yb
  have cover : outN D V y ⊆ outN D (inner D V u) y ∪ layer D V 3 u := by
    intro w hw
    obtain ⟨wV, yw⟩ := mem_outN.mp hw
    have wb : w ∈ ball D V u 3 := ball_step yb wV yw
    by_cases n2 : w ∈ ball D V u 2
    · apply mem_union_left
      refine mem_outN.mpr ⟨?_, yw⟩
      by_cases n1 : w ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp n1 with e | h
        · rw [e] at yw
          exact absurd yw (no_back_arc free hu yb (by omega))
        · exact mem_union_left _ h
      · exact mem_union_right _ (mem_layer.mpr ⟨n2, n1⟩)
    · exact mem_union_right _ (mem_layer.mpr ⟨wb, n2⟩)
  have := (card_le_card cover).trans (card_union_le _ _)
  rw [reg y yV] at this
  exact this

/-- **Lemma 1(c).** `|X ∪ Y| = r + |Y|`. -/
theorem inner_card (hu : u ∈ V) (reg : ∀ v ∈ V, (outN D V v).card = r) :
    (inner D V u).card = r + (layer D V 2 u).card := by
  have dis : outN D V u ∩ layer D V 2 u = ∅ := by
    ext v
    constructor
    · intro h
      obtain ⟨hv, hl⟩ := mem_inter.mp h
      exact absurd ((mem_ball_one hu).mpr (Or.inr hv)) (mem_layer.mp hl).2
    · intro h
      simp at h
  have := card_union_add_card_inter (outN D V u) (layer D V 2 u)
  rw [dis, card_empty, reg u hu] at this
  unfold inner
  omega

/-! ### Theorem 2: a large second layer -/

/-- **Theorem 2 (generic).** If `X ∪ Y` keeps `c ≥ 1` heads on every row and has at most `q c`
labels, the lower degree `c` hosts it. -/
theorem wide_second (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) {c : ℕ} (hc : 1 ≤ c) (keep : c + (layer D V 3 u).card ≤ r)
    (small : r + (layer D V 2 u).card ≤ q * c) (host : NoHost q c) : False := by
  obtain ⟨x, hx⟩ : (outN D V u).Nonempty := card_pos.mp (by rw [reg u hu]; omega)
  refine host D (inner D V u) ⟨x, mem_union_left _ hx⟩ (by rw [inner_card hu reg]; exact small)
    (free.mono_set inner_subset) ?_
  intro v hv
  rcases mem_union.mp hv with hx' | hy
  · rw [x_keep free (by omega) hu hx', reg v (outN_subset hx')]
    omega
  · have := y_keep free hq reg hu hy
    omega

/-- **Theorem 2 at `q = 6`, `r = 9`.** A second layer of at least `12` labels with
`|Y| + |Z| = 17` is impossible. -/
theorem profile_wide (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (sum : (layer D V 2 u).card + (layer D V 3 u).card = 17) (big : 12 ≤ (layer D V 2 u).card) :
    False := by
  by_cases top : (layer D V 2 u).card = 17
  · exact wide_second free (by norm_num) reg hu (c := 8) (by norm_num) (by omega) (by omega)
      (ShapeClimbMono.lower_hosts_every 6 8 (by rw [floor_nine]; norm_num))
  · exact wide_second free (by norm_num) reg hu (c := (layer D V 2 u).card - 8) (by omega)
      (by omega) (by omega)
      (ShapeClimbMono.lower_hosts_every 6 _ (by rw [floor_nine]; omega))

/-! ### Theorem 3 and Corollary 4 -/

/-- **Theorem 3.** The profile `(|Y|, |Z|) = (10, 7)` is impossible at `q = 6`, `r = 9`. -/
theorem profile_10_7 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (h2 : (layer D V 2 u).card = 10) (h3 : (layer D V 3 u).card = 7) : False := by
  refine core (W := inner D V u) (X := outN D V u) (free.mono_set inner_subset)
    (fun _ h => mem_union_left _ h) (by rw [inner_card hu reg, h2]) (reg u hu) ?_ ?_
  · intro x hx
    rw [x_keep free (by norm_num) hu hx, reg x (outN_subset hx)]
  · intro v hv
    rcases mem_union.mp hv with hx | hy
    · rw [x_keep free (by norm_num) hu hx, reg v (outN_subset hx)]
      norm_num
    · have := y_keep free (by norm_num) reg hu hy
      omega

/-! ### Lemma 10: roots with `|B_3| = 27` or `26` -/

/-- **Root budget.** At `q = 6`, `r = 9`: if the rows of `Y` keep `d ≥ 2` heads in `X ∪ Y`
(`d + |Z| ≤ 9`) and every fragment of minimum out-degree `d` has `reach 3 ≥ a`, then
`2 (9 · 12 + |Y| a) ≤ (9 + |Y|)(8 + |Y|)`. -/
theorem root_budget (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    {d a : ℕ} (hd : 2 ≤ d) (keep : d + (layer D V 3 u).card ≤ 9)
    (tab : ∀ W : Finset ℕ, QFree D W 6 → (∀ v ∈ W, d ≤ (outN D W v).card) →
      ∀ x ∈ W, a ≤ reach D W 3 x) :
    2 * (9 * 12 + (layer D V 2 u).card * a) ≤
      (9 + (layer D V 2 u).card) * (8 + (layer D V 2 u).card) := by
  have fr : QFree D (inner D V u) 6 := free.mono_set inner_subset
  have XF : outN D V u ⊆ inner D V u := fun _ h => mem_union_left _ h
  have deg : ∀ v ∈ inner D V u, d ≤ (outN D (inner D V u) v).card := by
    intro v hv
    rcases mem_union.mp hv with hx | hy
    · rw [x_keep free (by norm_num) hu hx, reg v (outN_subset hx)]
      omega
    · have := y_keep free (by norm_num) reg hu hy
      omega
  have deg2 : ∀ v ∈ inner D V u, 2 ≤ (outN D (inner D V u) v).card :=
    fun v hv => hd.trans (deg v hv)
  have onX : ∀ x ∈ outN D V u, 12 ≤ reach D (inner D V u) 3 x := fun x hx =>
    nine_row fr (XF hx) (by rw [x_keep free (by norm_num) hu hx, reg x (outN_subset hx)]) deg2
  have off : ∀ v ∈ inner D V u \ outN D V u, a ≤ reach D (inner D V u) 3 v :=
    fun v hv => tab _ fr deg v (mem_sdiff.mp hv).1
  have bf := budget_floor fr le_rfl XF onX off
  rw [card_sdiff_of_subset XF, inner_card hu reg, reg u hu] at bf
  have e1 : 9 + (layer D V 2 u).card - 9 = (layer D V 2 u).card := by omega
  have e2 : 9 + (layer D V 2 u).card - 1 = 8 + (layer D V 2 u).card := by omega
  rw [e1, e2] at bf
  exact bf

/-- **Lemma 10, `|B_3| = 27`.** No root with `|B_3| = 27` has a second layer of `10` or more. -/
theorem no_wide_27 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (b3 : (ball D V u 3).card = 27) (wide : 10 ≤ (layer D V 2 u).card) : False := by
  have L := (ThinSuppliers.balls_by_layers free (by norm_num) reg hu).2.2
  by_cases h10 : (layer D V 2 u).card = 10
  · exact profile_10_7 free reg hu h10 (by omega)
  by_cases h11 : (layer D V 2 u).card = 11
  · have := root_budget free reg hu (d := 3) (a := 9) (by norm_num) (by omega)
      (fun W fr dg x hx => reach_three_three fr hx le_rfl dg)
    rw [h11] at this
    norm_num at this
  by_cases h12 : (layer D V 2 u).card = 12
  · have := root_budget free reg hu (d := 4) (a := 11) (by norm_num) (by omega)
      (fun W fr dg x hx => reach_three_four fr hx le_rfl dg)
    rw [h12] at this
    norm_num at this
  have := root_budget free reg hu (d := 5) (a := 13) (by norm_num) (by omega)
    (fun W fr dg x hx => reach_three_five fr hx le_rfl dg)
  obtain ⟨w, hw⟩ : ∃ w, (layer D V 2 u).card = w := ⟨_, rfl⟩
  rw [hw] at this
  have lo : 13 ≤ w := by omega
  have hi : w ≤ 17 := by omega
  interval_cases w <;> norm_num at this

/-- **Lemma 10, `|B_3| = 26`.** A root with `|B_3| = 26` has profile `(8, 8)`. -/
theorem thin_26 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (b3 : (ball D V u 3).card = 26) :
    (layer D V 2 u).card = 8 ∧ (layer D V 3 u).card = 8 := by
  have L := (ThinSuppliers.balls_by_layers free (by norm_num) reg hu).2.2
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  have thin8 : (layer D V 2 u).card = 8 := by
    by_contra h8
    by_cases h9 : (layer D V 2 u).card = 9
    · have := root_budget free reg hu (d := 2) (a := 6) le_rfl (by omega)
        (fun W fr dg x hx => reach_three_two fr hx le_rfl dg)
      rw [h9] at this
      norm_num at this
    by_cases h10 : (layer D V 2 u).card = 10
    · have := root_budget free reg hu (d := 3) (a := 9) (by norm_num) (by omega)
        (fun W fr dg x hx => reach_three_three fr hx le_rfl dg)
      rw [h10] at this
      norm_num at this
    by_cases h11 : (layer D V 2 u).card = 11
    · have := root_budget free reg hu (d := 4) (a := 11) (by norm_num) (by omega)
        (fun W fr dg x hx => reach_three_four fr hx le_rfl dg)
      rw [h11] at this
      norm_num at this
    have := root_budget free reg hu (d := 5) (a := 13) (by norm_num) (by omega)
      (fun W fr dg x hx => reach_three_five fr hx le_rfl dg)
    obtain ⟨w, hw⟩ : ∃ w, (layer D V 2 u).card = w := ⟨_, rfl⟩
    rw [hw] at this
    have lo : 12 ≤ w := by omega
    have hi : w ≤ 16 := by omega
    interval_cases w <;> norm_num at this
  have w3 := ThinSuppliers.third_wide free (by norm_num) reg hu
    (show ThinSuppliers.Thin D V 9 u by unfold ThinSuppliers.Thin; omega) (by norm_num)
  exact ⟨thin8, by omega⟩

/-- **Corollary 4.** At `q = 6`, `r = 9`, a root with `|Y| ≥ 9` and `|B_3| = 27` has profile
`(9, 8)`. -/
theorem profile_cases (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (wide : 9 ≤ (layer D V 2 u).card) (b3 : (ball D V u 3).card = 27) :
    (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8 := by
  have L := (ThinSuppliers.balls_by_layers free (by norm_num) reg hu).2.2
  by_cases h10 : 10 ≤ (layer D V 2 u).card
  · exact (no_wide_27 free reg hu b3 h10).elim
  omega

end root

#print axioms shell_step
#print axioms growth_facts
#print axioms reach_three_two
#print axioms reach_three_three
#print axioms reach_three_four
#print axioms reach_three_five
#print axioms nine_row
#print axioms pair_budget
#print axioms budget_floor
#print axioms wide_second
#print axioms profile_wide
#print axioms core
#print axioms profile_10_7
#print axioms root_budget
#print axioms no_wide_27
#print axioms thin_26
#print axioms profile_cases

end LeanCH.BR.Profile54
