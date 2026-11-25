import checkpoints.shen_extension.Profiles72

/-!
# Profile II on the row `r = q + 1`: layers `(q + 2, q, q)` are impossible (`q ≥ 8`)

Setting of `Profiles72.lean` with `|Y| = q + 2`, `|Z| = q`, `|W| = q` (at `q = 8`: `(10, 8, 8)`).
A head of `u` with `h` heads in `X` omits `h + 1` labels of `Y`; a sink of `X` omits one.

* `ii1` (II.1): a row of `Y` on a closed walk inside `Y` reaches no head of `u` in one or two
  steps (`cyc_omit` twice, the second time from the nearest sink of `X`).
* `caseA` (II.2, `Y` has a row on a closed walk). The paper's shortest cycle is replaced by
  `N`, the rows of `Y` on closed walks inside `Y`: `N` has minimum out-degree one inside `N`, so
  `|N| ≥ q + 1`. If `N = Y`, every row reaches a one-head row within one step
  (`OneHead.lone_within`); if `|N| = q + 1`, `N` is a bank and the extra row cannot be pointed to
  from `N` (it would lie on a closed walk, or close II.1 with `b = 2`). Either way every row of `Y`
  reaches all of `Z` within three steps and some row of `N` is complete to `Z`, so `Z` keeps
  minimum out-degree one on `q` labels.
* `caseB_cyc` (II.3, `Y` acyclic, `X` a bank): double counting of omissions (`om_swap`):
  `2 (q + 1)` incidences against `2 (q - 2) + 2 (q - 4)` forced by four rows near the sinks of `Y`.
* `caseB_acyc` (II.4, `Y` and `X` acyclic). Every row of `Y` lies above a tail. Fact C with the
  target (when it is `(q - 2)`-deep) or with its nearest sink (otherwise) covers `Y` by the
  omission sets of the sinks of `X` and of the `(q - 2)`-deep rows. With `k ≥ 2` sinks the deep
  rows are few (`deep_bound` with the sinks); with one sink the tails into rows that are not
  `(q - 1)`-deep all equal the one label the sink omits, so a single omission set of size at most
  four plus the at most two `(q - 1)`-deep rows (at most five omissions in all) cover `Y`.
  This reorganizes the paper's case table on `(k, h)`.
* `profileII : False`, generic; `profileII_72` at `q = 8`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Profiles72
open Finset BRq2 BRq3 ThinSuppliers OneHead
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open SupplierFat54 (oSet aSet om mem_om om_card fact_C layer_disj keep_count)
open SinkReturnAncestors (Sink)
open SinkDepthReturn (Deep return_deep deep_heads)

variable {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}

/-- **II.1.** `|Y| = q + 2`: a row of `Y` on a closed walk inside `Y` reaches no head of `u` by a
walk of length one or two. -/
theorem ii1 (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 2) {v x b : ℕ}
    (hv : OnCyc D (layer D V 2 u) v) (hx : x ∈ outN D V u) (path : Walk D V v x b)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) : False := by
  have YV : layer D V 2 u ⊆ V := layer_subset
  have XV : outN D V u ⊆ V := outN_subset
  have cX := reg u hu
  have c1 := cyc_omit free YV hv path (by omega)
  have acct := x_acct free (by omega) reg hu hx
  rw [hY] at acct
  rcases split_bank free (by omega) XV (reg u hu) with cycX | ⟨acX, -⟩
  · have := cycX x hx
    omega
  · by_cases dp : Deep D (outN D V u) (q - b - 1) x
    · have := deep_heads acX cX.le hx dp
      omega
    · obtain ⟨s, sX, sk, k, hk, w⟩ := not_deep dp
      have c2 := cyc_omit free YV hv (path.append (w.mono XV)) (by omega)
      have acs := x_acct free (by omega) reg hu sX
      rw [hY, sink_empty sk, card_empty] at acs
      omega

/-- A row of `Y` on a closed walk inside `Y`, with at most one head in `Y`, points to all of `Z`
(`|Y| = q + 2`, `|Z| = q`). -/
theorem ii_complete (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 2) (hZ : (layer D V 3 u).card = q) {c : ℕ}
    (hc : c ∈ layer D V 2 u) (oc : OnCyc D (layer D V 2 u) c)
    (one : (outN D (layer D V 2 u) c).card ≤ 1) : layer D V 3 u ⊆ outN D V c := by
  have cover : outN D V c ⊆ layer D V 2 u ∪ layer D V 3 u := by
    intro w hw
    obtain ⟨-, cw⟩ := mem_outN.mp hw
    rcases mem_union.mp (SupplierFat54.y_cover free (by omega) hu hc hw) with h | h
    · rcases mem_union.mp h with hx | hy
      · exact (ii1 (b := 1) free hq reg hu hY oc hx (.step (outN_subset hx) cw (.refl w))
          le_rfl (by norm_num)).elim
      · exact mem_union_left _ hy
    · exact mem_union_right _ h
  exact lone_full (r := q + 1) cover (reg c (layer_subset hc)).ge one (by omega)

/-- **II.2.** `|Y| = q + 2`, `|Z| = |W| = q`: no row of `Y` lies on a closed walk inside `Y`. -/
theorem caseA (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 2) (hZ : (layer D V 3 u).card = q)
    (hW : (layer D V 4 u).card = q) {v0 : ℕ} (hv0 : v0 ∈ layer D V 2 u)
    (oc0 : OnCyc D (layer D V 2 u) v0) : False := by
  classical
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have ZV : layer D V 3 u ⊆ V := layer_subset
  set N := (layer D V 2 u).filter (fun v => OnCyc D (layer D V 2 u) v) with hN
  have NY : N ⊆ layer D V 2 u := filter_subset _ _
  have NV : N ⊆ V := NY.trans YV
  have memN : ∀ v, v ∈ N ↔ v ∈ layer D V 2 u ∧ OnCyc D (layer D V 2 u) v := fun v => mem_filter
  have v0N : v0 ∈ N := (memN v0).mpr ⟨hv0, oc0⟩
  have degN : ∀ v ∈ N, 1 ≤ (outN D N v).card := by
    intro v hv
    obtain ⟨vY, oc⟩ := (memN v).mp hv
    obtain ⟨w, wY, vw, ocw⟩ := oncyc_next free (by omega) YV vY oc
    exact card_pos.mpr ⟨w, mem_outN.mpr ⟨(memN w).mpr ⟨wY, ocw⟩, vw⟩⟩
  have cN : q + 1 ≤ N.card := DipCost.order_one q D N (free.mono_set NV) degN ⟨v0, v0N⟩
  have cNY := card_le_card NY
  have noX2 : ∀ c ∈ N, ∀ h ∈ V, D c h = true → ∀ x ∈ outN D V u, ¬ D h x = true :=
    fun c hc h hV ch x hx hx' => ii1 (b := 2) free hq reg hu hY ((memN c).mp hc).2 hx
      (.step hV ch (.step (XV hx) hx' (.refl x))) (by norm_num) le_rfl
  have complete : ∀ c ∈ N, (outN D (layer D V 2 u) c).card ≤ 1 → layer D V 3 u ⊆ outN D V c :=
    fun c hc one => ii_complete free hq reg hu hY hZ ((memN c).mp hc).1 ((memN c).mp hc).2 one
  have key : (∀ y ∈ layer D V 2 u, layer D V 3 u ⊆ ball D V y 3) ∧
      ∃ c ∈ N, layer D V 3 u ⊆ outN D V c := by
    by_cases full : N.card = q + 2
    · have NeY : N = layer D V 2 u := eq_of_subset_of_card_le NY (by omega)
      have degY : ∀ v ∈ layer D V 2 u, 1 ≤ (outN D (layer D V 2 u) v).card := by
        intro v hv
        have := degN v (by rw [NeY]; exact hv)
        rwa [NeY] at this
      have lw : ∀ y ∈ layer D V 2 u, ∃ c ∈ N, c ∈ ball D V y 1 ∧ layer D V 3 u ⊆ outN D V c := by
        intro y hy
        obtain ⟨c, cb, cl⟩ := lone_within (free.mono_set YV) (by omega) degY (k := 1) (by omega)
          (by omega) (by omega) hy
        have cN' : c ∈ N := by rw [NeY]; exact lone_subset cl
        exact ⟨c, cN', SupplierFat54.ball_mono_set YV cb, complete c cN' (mem_lone.mp cl).2⟩
      refine ⟨fun y hy z hz => ?_, ?_⟩
      · obtain ⟨c, -, cb, cf⟩ := lw y hy
        exact ball_mono_radius (by norm_num)
          (ball_trans cb (ball_arc (ZV hz) (mem_outN.mp (cf hz)).2))
      · obtain ⟨c, cN', -, cf⟩ := lw v0 hv0
        exact ⟨c, cN', cf⟩
    · have cN1 : N.card = q + 1 := by omega
      obtain ⟨e, he⟩ : ∃ e, layer D V 2 u \ N = {e} :=
        card_eq_one.mp (by rw [card_sdiff_of_subset NY]; omega)
      have eIn : e ∈ layer D V 2 u \ N := by rw [he]; exact mem_singleton_self e
      have eY : e ∈ layer D V 2 u := (mem_sdiff.mp eIn).1
      have eN : e ∉ N := (mem_sdiff.mp eIn).2
      have split : ∀ y ∈ layer D V 2 u, y ∈ N ∨ y = e := by
        intro y hy
        by_cases yN : y ∈ N
        · exact Or.inl yN
        · have : y ∈ layer D V 2 u \ N := mem_sdiff.mpr ⟨hy, yN⟩
          rw [he] at this
          exact Or.inr (mem_singleton.mp this)
      have oneN := LoopCollar.loop_unique_head (free.mono_set NV) (by omega) cN1 degN
      have ballN : ∀ n ∈ N, ball D N n q = N := fun n hn =>
        eq_of_subset_of_card_le ball_subset
          (by have := LoopCollar.ball_grow (free.mono_set NV) degN hn q le_rfl; omega)
      have eHead : (∃ n ∈ N, D e n = true) ∨ ∃ x ∈ outN D V u, D e x = true := by
        by_cases h : ∃ n ∈ N, D e n = true
        · exact Or.inl h
        · push Not at h
          refine Or.inr (ysink_tail free (by omega) reg hu (by omega) eY (fun a ha ea => ?_))
          rcases split a ha with aN | ae
          · exact h a aN ea
          · rw [ae] at ea
            exact loopfree free (by omega) (YV eY) ea
      have noE : ∀ c ∈ N, ¬ D c e = true := by
        intro c hc ce
        rcases eHead with ⟨n, hn, en⟩ | ⟨x, hx, ex⟩
        · have cb : c ∈ ball D N n q := by rw [ballN n hn]; exact hc
          obtain ⟨-, j, -, w⟩ := mem_ball.mp cb
          exact eN ((memN e).mpr ⟨eY, n, NY hn, en, j + 1, (w.mono NY).snoc eY ce⟩)
        · exact noX2 c hc e (YV eY) ce x hx ex
      have compN : ∀ c ∈ N, layer D V 3 u ⊆ outN D V c := by
        intro c hc
        refine complete c hc ?_
        have sub : outN D (layer D V 2 u) c ⊆ outN D N c := by
          intro w hw
          obtain ⟨wY, cw⟩ := mem_outN.mp hw
          rcases split w wY with wN | we
          · exact mem_outN.mpr ⟨wN, cw⟩
          · rw [we] at cw
            exact (noE c hc cw).elim
        have := card_le_card sub
        rw [oneN c hc] at this
        exact this
      refine ⟨fun y hy z hz => ?_, v0, v0N, compN v0 v0N⟩
      rcases split y hy with yN | ye
      · exact ball_mono_radius (by norm_num) (ball_arc (ZV hz) (mem_outN.mp (compN y yN hz)).2)
      · rw [ye]
        rcases eHead with ⟨n, hn, en⟩ | ⟨x, hx, ex⟩
        · exact ball_mono_radius (by norm_num)
            (ball_trans (ball_arc (NV hn) en) (ball_arc (ZV hz) (mem_outN.mp (compN n hn hz)).2))
        · have acct := x_acct free (by omega) reg hu hx
          have oc := om_card (D := D) (layer D V 2 u) x
          have hle := x_heads_le free (by omega) reg hu hx
          obtain ⟨y', hy'⟩ := card_pos.mp (show 0 < (outN D (layer D V 2 u) x).card by omega)
          obtain ⟨y'Y, xy'⟩ := mem_outN.mp hy'
          have y'N : y' ∈ N := by
            rcases split y' y'Y with h | h
            · exact h
            · rw [h] at xy'
              exact (digonfree free (by omega) (YV eY) (XV hx) ex xy').elim
          exact ball_trans (ball_arc (XV hx) ex) (ball_trans (ball_arc (YV y'Y) xy')
            (ball_arc (ZV hz) (mem_outN.mp (compN y' y'N hz)).2))
  obtain ⟨reach, c0, hc0, full0⟩ := key
  have zdeg : ∀ z ∈ layer D V 3 u, 1 ≤ (outN D (layer D V 3 u) z).card := by
    intro z hz
    have cover : outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
      intro w hw
      obtain ⟨wV, zw⟩ := mem_outN.mp hw
      rcases z_heads free (by omega) hu hz zw wV with hx | hy | h | h
      · exact (noX2 c0 hc0 z (ZV hz) (mem_outN.mp (full0 hz)).2 w hx zw).elim
      · exact (no_back_arc free (YV hy) (reach w hy hz) (by omega) zw).elim
      · exact mem_union_left _ h
      · exact mem_union_right _ h
    have c := keep_count cover
    rw [reg z (ZV hz), hW] at c
    omega
  have := DipCost.order_one q D (layer D V 3 u) (free.mono_set ZV) zdeg (card_pos.mp (by omega))
  omega

/-- **II.3.** `Y` acyclic, `X` a bank: impossible. -/
theorem caseB_cyc (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 2) (hZ : (layer D V 3 u).card = q)
    (acY : QFree D (layer D V 2 u) (q + 2))
    (cycX : ∀ x ∈ outN D V u, (outN D (outN D V u) x).card = 1) : False := by
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have om2 : ∀ x ∈ outN D V u, (om D (layer D V 2 u) x).card = 2 := by
    intro x hx
    have := x_acct free (by omega) reg hu hx
    rw [cycX x hx, hY] at this
    omega
  have degX : ∀ v ∈ outN D V u, 1 ≤ (outN D (outN D V u) v).card := fun v hv => (cycX v hv).ge
  have growX : ∀ x ∈ outN D V u, ∀ j, j ≤ q → j + 1 ≤ (ball D (outN D V u) x j).card :=
    fun x hx j hj => LoopCollar.ball_grow (free.mono_set XV) degX hx j hj
  -- a row of `Y` within `j` of a sink of `Y` is omitted by at least `q - 1 - j` heads of `u`
  have cost : ∀ y ∈ layer D V 2 u, ∀ j, j ≤ q - 2 → ¬ Deep D (layer D V 2 u) (j + 1) y →
      q - 1 - j ≤ (omx D (outN D V u) y).card := by
    intro y hy j hj nd
    obtain ⟨t, tY, sk, d, hd, w⟩ := not_deep nd
    obtain ⟨x0, hx0, tx0⟩ := ysink_tail free (by omega) reg hu (by omega) tY (fun a ha => sk a ha)
    have sub : ball D (outN D V u) x0 (q - 2 - j) ⊆ omx D (outN D V u) y := by
      intro x' hx'
      obtain ⟨x'X, k, hk, w'⟩ := mem_ball.mp hx'
      refine mem_omx.mpr ⟨x'X, fun arc => ?_⟩
      exact free y (d + 1 + k + 1) (by omega) (by omega)
        ((((w.mono YV).snoc (XV hx0) tx0).append (w'.mono XV)).snoc (YV hy) arc)
    have := card_le_card sub
    have := growX x0 hx0 (q - 2 - j) (by omega)
    omega
  obtain ⟨N1, N1Y, c1, h1⟩ := near_exists acY (by omega) (t := 2) (by norm_num)
  obtain ⟨N3, N3Y, c3, h3⟩ := near_exists acY (by omega) (t := 4) (by norm_num)
  obtain ⟨S1, S1N, cS1⟩ := exists_subset_card_eq (show 2 ≤ N1.card by omega)
  have big : 2 ≤ (N3 \ S1).card := by
    have := card_le_card_sdiff_add_card (s := N3) (t := S1)
    omega
  obtain ⟨S3, S3N, cS3⟩ := exists_subset_card_eq big
  have dis : Disjoint S1 S3 := by
    rw [disjoint_left]
    intro a a1 a3
    exact (mem_sdiff.mp (S3N a3)).2 a1
  have sub : S1 ∪ S3 ⊆ layer D V 2 u :=
    union_subset (S1N.trans N1Y) (S3N.trans (sdiff_subset.trans N3Y))
  have sx : ∑ x ∈ outN D V u, (om D (layer D V 2 u) x).card = (outN D V u).card * 2 := by
    rw [sum_congr rfl (fun x hx => om2 x hx), sum_const, smul_eq_mul]
  have total := om_swap (D := D) (outN D V u) (layer D V 2 u)
  have ge : ∑ y ∈ S1 ∪ S3, (omx D (outN D V u) y).card ≤
      ∑ y ∈ layer D V 2 u, (omx D (outN D V u) y).card := sum_le_sum_of_subset sub
  rw [sum_union dis] at ge
  have g1 := card_nsmul_le_sum S1 (fun y => (omx D (outN D V u) y).card) (q - 2)
    (fun y hy => by
      have := cost y (N1Y (S1N hy)) 1 (by omega) (h1 y (S1N hy))
      omega)
  have g3 := card_nsmul_le_sum S3 (fun y => (omx D (outN D V u) y).card) (q - 4)
    (fun y hy => by
      have yN3 := (mem_sdiff.mp (S3N hy)).1
      have := cost y (N3Y yN3) 3 (by omega) (h3 y yN3)
      omega)
  rw [smul_eq_mul, cS1] at g1
  rw [smul_eq_mul, cS3] at g3
  have := reg u hu
  omega

/-- **II.4.** `Y` and `X` acyclic: impossible. -/
theorem caseB_acyc (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 2) (hZ : (layer D V 3 u).card = q)
    (acY : QFree D (layer D V 2 u) (q + 2)) (acX : QFree D (outN D V u) (q + 1)) : False := by
  classical
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have cX : (outN D V u).card = q + 1 := reg u hu
  have tailY : ∀ {o t j : ℕ}, o ∈ layer D V 2 u → Walk D (layer D V 2 u) o t j → t ∈ layer D V 2 u :=
    fun oY w => by
      rcases w.end_mem_or with e | h
      · rw [e]; exact oY
      · exact h
  have acct : ∀ x ∈ outN D V u,
      (om D (layer D V 2 u) x).card = (outN D (outN D V u) x).card + 1 := by
    intro x hx
    have := x_acct free (by omega) reg hu hx
    rw [hY] at this
    omega
  have above : ∀ y ∈ layer D V 2 u, ∃ t x, x ∈ outN D V u ∧ D t x = true ∧
      ∃ i, Walk D (layer D V 2 u) y t i := by
    intro y hy
    obtain ⟨t, tY, sk, i, -, w⟩ := reach_sink_of_card acY (by omega) hy
    obtain ⟨x, hx, tx⟩ := ysink_tail free (by omega) reg hu (by omega) tY sk
    exact ⟨t, x, hx, tx, i, w⟩
  have omDeep : ∀ x ∈ outN D V u, ∀ t, Deep D (outN D V u) t x →
      (om D (layer D V 2 u) x).card + t ≤ q + 2 := by
    intro x hx t dp
    have := deep_heads acX cX.le hx dp
    have := acct x hx
    omega
  have cardT : ∀ t, 1 ≤ t → ∀ T : Finset ℕ, T ⊆ outN D V u →
      (∀ x ∈ T, Deep D (outN D V u) t x) → t + T.card ≤ q + 1 ∨ T.card = 0 := by
    intro t ht T TX hT
    by_cases ne : T.Nonempty
    · left
      have := (deep_bound acX cX.le ht (T := T) TX hT (empty_subset _)
        (fun s hs => absurd hs (Finset.notMem_empty s)) ne).1
      omega
    · right
      exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp ne)
  -- the sinks of `X`
  set SK := (outN D V u).filter (fun s => outN D (outN D V u) s = ∅) with hSK
  have SKX : SK ⊆ outN D V u := filter_subset _ _
  have SKsink : ∀ s ∈ SK, Sink D (outN D V u) s := fun s hs => sink_of_empty (mem_filter.mp hs).2
  have SKom : ∀ s ∈ SK, (om D (layer D V 2 u) s).card = 1 := by
    intro s hs
    have := acct s (mem_filter.mp hs).1
    rw [(mem_filter.mp hs).2, card_empty] at this
    omega
  have inSK : ∀ s ∈ outN D V u, Sink D (outN D V u) s → s ∈ SK :=
    fun s hs sk => mem_filter.mpr ⟨hs, sink_empty sk⟩
  have SKne : SK.Nonempty := by
    obtain ⟨s, sX, sk⟩ := exists_sink acX (card_pos.mp (by omega)) cX.le
    exact ⟨s, inSK s sX (fun a ha => sk a ha)⟩
  -- the deep rows
  set T1 := (outN D V u).filter (fun x => Deep D (outN D V u) (q - 1) x) with hT1
  set T2 := (outN D V u).filter (fun x => Deep D (outN D V u) (q - 2) x) with hT2
  set T3 := (outN D V u).filter (fun x => Deep D (outN D V u) (q - 3) x) with hT3
  have T1T2 : T1 ⊆ T2 := fun x hx =>
    mem_filter.mpr ⟨(mem_filter.mp hx).1, SinkDepthReturn.Deep.mono (mem_filter.mp hx).2 (by omega)⟩
  have T2T3 : T2 ⊆ T3 := fun x hx =>
    mem_filter.mpr ⟨(mem_filter.mp hx).1, SinkDepthReturn.Deep.mono (mem_filter.mp hx).2 (by omega)⟩
  -- heads of a `t`-deep row are `(t - 1)`-deep
  have headsT : ∀ (T T' : Finset ℕ) (t : ℕ), 1 ≤ t →
      (∀ x ∈ T, x ∈ outN D V u ∧ Deep D (outN D V u) t x) →
      (∀ c ∈ outN D V u, Deep D (outN D V u) (t - 1) c → c ∈ T') →
      ∀ x ∈ T, outN D (outN D V u) x ⊆ T'.erase x := by
    intro T T' t ht hT hT' x hx c hc
    obtain ⟨cX', xc⟩ := mem_outN.mp hc
    obtain ⟨xX, dx⟩ := hT x hx
    refine mem_erase.mpr ⟨fun e => ?_, hT' c cX' (deep_head dx (by omega) cX' xc)⟩
    rw [e] at xc
    exact loopfree free (by omega) (XV xX) xc
  -- cover through the sinks and the `(q - 2)`-deep rows
  have cover2 : ∀ y ∈ layer D V 2 u, (∃ s ∈ SK, y ∈ om D (layer D V 2 u) s) ∨
      ∃ x ∈ T2, y ∈ om D (layer D V 2 u) x := by
    intro y hy
    obtain ⟨t, x, hx, tx, i, w⟩ := above y hy
    by_cases dx : Deep D (outN D V u) (q - 2) x
    · have := omDeep x hx _ dx
      exact Or.inr ⟨x, mem_filter.mpr ⟨hx, dx⟩,
        fact_C free YV (XV hx) tx (.refl x) (by omega) hy w⟩
    · obtain ⟨s, sX, sk, k, hk, ws⟩ := not_deep dx
      have := SKom s (inSK s sX sk)
      exact Or.inl ⟨s, inSK s sX sk, fact_C free YV (XV hx) tx (ws.mono XV) (by omega) hy w⟩
  have s1 : ∑ s ∈ SK, (om D (layer D V 2 u) s).card = SK.card := by
    rw [sum_congr rfl SKom, sum_const, smul_eq_mul, mul_one]
  by_cases k1 : SK.card = 1
  · -- one sink `s0`, omitting the single label `y0`
    obtain ⟨s0, hs0⟩ := card_eq_one.mp k1
    have s0SK : s0 ∈ SK := by rw [hs0]; exact mem_singleton_self s0
    have SKeq : ∀ s ∈ SK, s = s0 := fun s hs => by
      rw [hs0] at hs
      exact mem_singleton.mp hs
    have s0X : s0 ∈ outN D V u := SKX s0SK
    obtain ⟨y0, hy0⟩ := card_eq_one.mp (SKom s0 s0SK)
    have om0 : ∀ y, y ∈ om D (layer D V 2 u) s0 → y = y0 := fun y h => by
      rw [hy0] at h
      exact mem_singleton.mp h
    -- a tail into a row that is not `(q - 1)`-deep is `y0`
    have tail0 : ∀ t ∈ layer D V 2 u, ∀ x ∈ outN D V u, D t x = true →
        ¬ Deep D (outN D V u) (q - 1) x → t = y0 := by
      intro t tY x hx tx nd
      obtain ⟨s, sX, sk, k, hk, ws⟩ := not_deep nd
      have e := SKeq s (inSK s sX sk)
      rw [e] at ws
      refine om0 t (mem_om.mpr ⟨tY, fun st => ?_⟩)
      exact free s0 (k + 1 + 1) (by omega) (by omega)
        (.step (YV tY) st (.step (XV hx) tx (ws.mono XV)))
    have cT1 : T1.card ≤ 2 := by
      rcases cardT (q - 1) (by omega) T1 (filter_subset _ _) (fun x hx => (mem_filter.mp hx).2)
        with h | h <;> omega
    have cT2 : T2.card ≤ 3 := by
      rcases cardT (q - 2) (by omega) T2 (filter_subset _ _) (fun x hx => (mem_filter.mp hx).2)
        with h | h <;> omega
    have hT1 : ∀ x ∈ T1, outN D (outN D V u) x ⊆ T2.erase x :=
      headsT T1 T2 (q - 1) (by omega) (fun x hx => mem_filter.mp hx)
        (fun c cX' d => mem_filter.mpr ⟨cX', by rw [show q - 2 = q - 1 - 1 by omega]; exact d⟩)
    -- the `(q - 1)`-deep rows omit at most five labels in all
    have sumT1 : ∑ x ∈ T1, (om D (layer D V 2 u) x).card ≤ 5 := by
      have e1 : ∑ x ∈ T1, (om D (layer D V 2 u) x).card =
          ∑ x ∈ T1, ((outN D (outN D V u) x).card + 1) :=
        sum_congr rfl (fun x hx => acct x (mem_filter.mp hx).1)
      have e2 : ∑ x ∈ T1, ((outN D (outN D V u) x).card + 1) =
          ∑ x ∈ T1, (outN D (outN D V u) x).card + T1.card := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
      rw [e1, e2]
      by_cases two : T1.card = 2
      · obtain ⟨x1, x2, ne12, hT⟩ := card_eq_two.mp two
        have x1T : x1 ∈ T1 := by rw [hT]; simp
        have x2T : x2 ∈ T1 := by rw [hT]; simp
        have hsum : ∑ x ∈ T1, (outN D (outN D V u) x).card =
            (outN D (outN D V u) x1).card + (outN D (outN D V u) x2).card := by
          rw [hT, sum_pair ne12]
        have x1T2 := T1T2 x1T
        have x2T2 := T1T2 x2T
        have h1 := card_le_card (hT1 x1 x1T)
        have h2 := card_le_card (hT1 x2 x2T)
        rw [card_erase_of_mem x1T2] at h1
        rw [card_erase_of_mem x2T2] at h2
        have x1X := (mem_filter.mp x1T).1
        have x2X := (mem_filter.mp x2T).1
        by_cases a : D x1 x2 = true
        · have nb : ¬ D x2 x1 = true := fun b => digonfree free (by omega) (XV x1X) (XV x2X) a b
          have sub : outN D (outN D V u) x2 ⊆ (T2.erase x2).erase x1 := by
            intro c hc
            refine mem_erase.mpr ⟨fun e => ?_, hT1 x2 x2T hc⟩
            rw [e] at hc
            exact nb (mem_outN.mp hc).2
          have := card_le_card sub
          rw [card_erase_of_mem (mem_erase.mpr ⟨ne12, x1T2⟩), card_erase_of_mem x2T2] at this
          omega
        · have sub : outN D (outN D V u) x1 ⊆ (T2.erase x1).erase x2 := by
            intro c hc
            refine mem_erase.mpr ⟨fun e => ?_, hT1 x1 x1T hc⟩
            rw [e] at hc
            exact a (mem_outN.mp hc).2
          have := card_le_card sub
          rw [card_erase_of_mem (mem_erase.mpr ⟨ne12.symm, x2T2⟩), card_erase_of_mem x1T2] at this
          omega
      · have := sum_le_card_nsmul T1 (fun x => (outN D (outN D V u) x).card) 2 (fun x hx => by
          have := card_le_card (hT1 x hx)
          rw [card_erase_of_mem (T1T2 hx)] at this
          omega)
        rw [smul_eq_mul] at this
        have : T1.card ≤ 1 := by omega
        omega
    have finish : ∀ B : Finset ℕ, B.card ≤ 4 →
        (∀ y ∈ layer D V 2 u, y ∈ B ∨ ∃ x ∈ T1, y ∈ om D (layer D V 2 u) x) → False := by
      intro B cB hB
      have sub : layer D V 2 u ⊆ B ∪ T1.biUnion (om D (layer D V 2 u)) := by
        intro y hy
        rcases hB y hy with h | ⟨x, hx, h⟩
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_biUnion.mpr ⟨x, hx, h⟩)
      have c1 := card_le_card sub
      have c2 := card_union_le B (T1.biUnion (om D (layer D V 2 u)))
      have c3 := card_biUnion_le (s := T1) (t := om D (layer D V 2 u))
      omega
    -- a `(q - 1)`-deep target covers its ancestors
    have viaT1 : ∀ y ∈ layer D V 2 u, ∀ t x i, x ∈ outN D V u → D t x = true →
        Walk D (layer D V 2 u) y t i → Deep D (outN D V u) (q - 1) x →
        ∃ x ∈ T1, y ∈ om D (layer D V 2 u) x := by
      intro y hy t x i hx tx w d1
      have := omDeep x hx _ d1
      exact ⟨x, mem_filter.mpr ⟨hx, d1⟩, fact_C free YV (XV hx) tx (.refl x) (by omega) hy w⟩
    by_cases hx0 : ∃ x0 ∈ T2, x0 ∉ T1 ∧ ∃ t0 ∈ layer D V 2 u, D t0 x0 = true
    · obtain ⟨x0, x0T2, x0T1, t0, ht0, tx0⟩ := hx0
      have x0X := (mem_filter.mp x0T2).1
      have e0 : t0 = y0 := tail0 t0 ht0 x0 x0X tx0 (fun d => x0T1 (mem_filter.mpr ⟨x0X, d⟩))
      have om0' := omDeep x0 x0X _ (mem_filter.mp x0T2).2
      refine finish (om D (layer D V 2 u) x0) (by omega) (fun y hy => ?_)
      obtain ⟨t, x, hx, tx, i, w⟩ := above y hy
      by_cases d1 : Deep D (outN D V u) (q - 1) x
      · exact Or.inr (viaT1 y hy t x i hx tx w d1)
      · have et : t = y0 := tail0 t (tailY hy w) x hx tx d1
        rw [et, ← e0] at w
        exact Or.inl (fact_C free YV (XV x0X) tx0 (.refl x0) (by omega) hy w)
    · push Not at hx0
      refine finish (om D (layer D V 2 u) s0) (by have := SKom s0 s0SK; omega) (fun y hy => ?_)
      obtain ⟨t, x, hx, tx, i, w⟩ := above y hy
      by_cases d1 : Deep D (outN D V u) (q - 1) x
      · exact Or.inr (viaT1 y hy t x i hx tx w d1)
      · have d2 : ¬ Deep D (outN D V u) (q - 2) x := fun d2 =>
          hx0 x (mem_filter.mpr ⟨hx, d2⟩) (fun h => d1 (mem_filter.mp h).2) t (tailY hy w) tx
        obtain ⟨s, sX, sk, k, hk, ws⟩ := not_deep d2
        have e := SKeq s (inSK s sX sk)
        rw [e] at ws
        have := SKom s0 s0SK
        exact Or.inl (fact_C free YV (XV hx) tx (ws.mono XV) (by omega) hy w)
  · -- at least two sinks
    have k2 : 2 ≤ SK.card := by
      have := card_pos.mpr SKne
      omega
    by_cases ne2 : T2.Nonempty
    · have b2 := (deep_bound acX cX.le (by omega : 1 ≤ q - 2) (T := T2) (K := SK) (filter_subset _ _)
        (fun x hx => (mem_filter.mp hx).2) SKX SKsink ne2).2
      have b3 := (deep_bound acX cX.le (by omega : 1 ≤ q - 3) (T := T3) (K := SK) (filter_subset _ _)
        (fun x hx => (mem_filter.mp hx).2) SKX SKsink (ne2.mono T2T3)).2
      have hT2 : ∀ x ∈ T2, outN D (outN D V u) x ⊆ T3.erase x :=
        headsT T2 T3 (q - 2) (by omega) (fun x hx => mem_filter.mp hx)
          (fun c cX' d => mem_filter.mpr ⟨cX', by rw [show q - 3 = q - 2 - 1 by omega]; exact d⟩)
      have omT2 : ∀ x ∈ T2, (om D (layer D V 2 u) x).card ≤ T3.card := by
        intro x hx
        have := card_le_card (hT2 x hx)
        rw [card_erase_of_mem (T2T3 hx)] at this
        have := acct x (mem_filter.mp hx).1
        have : 1 ≤ T3.card := card_pos.mpr ⟨x, T2T3 hx⟩
        omega
      have sub : layer D V 2 u ⊆
          SK.biUnion (om D (layer D V 2 u)) ∪ T2.biUnion (om D (layer D V 2 u)) := by
        intro y hy
        rcases cover2 y hy with ⟨s, hs, h⟩ | ⟨x, hx, h⟩
        · exact mem_union_left _ (mem_biUnion.mpr ⟨s, hs, h⟩)
        · exact mem_union_right _ (mem_biUnion.mpr ⟨x, hx, h⟩)
      have c1 := card_le_card sub
      have c2 := card_union_le (SK.biUnion (om D (layer D V 2 u))) (T2.biUnion (om D (layer D V 2 u)))
      have c3 := card_biUnion_le (s := SK) (t := om D (layer D V 2 u))
      have c4 := card_biUnion_le (s := T2) (t := om D (layer D V 2 u))
      have s2 := sum_le_card_nsmul T2 (fun x => (om D (layer D V 2 u) x).card) T3.card omT2
      rw [smul_eq_mul] at s2
      have pos2 : 1 ≤ T2.card := card_pos.mpr ne2
      obtain ⟨P, hP⟩ : ∃ P, T2.card * T3.card = P := ⟨_, rfl⟩
      rw [hP] at s2
      rcases (show SK.card = 2 ∨ SK.card = 3 by omega) with h | h
      · have m := Nat.mul_le_mul (show T2.card ≤ 2 by omega) (show T3.card ≤ 3 by omega)
        rw [hP] at m
        omega
      · have m := Nat.mul_le_mul (show T2.card ≤ 1 by omega) (show T3.card ≤ 2 by omega)
        rw [hP] at m
        omega
    · have sub : layer D V 2 u ⊆ SK.biUnion (om D (layer D V 2 u)) := by
        intro y hy
        rcases cover2 y hy with ⟨s, hs, h⟩ | ⟨x, hx, h⟩
        · exact mem_biUnion.mpr ⟨s, hs, h⟩
        · exact (ne2 ⟨x, hx⟩).elim
      have c1 := card_le_card sub
      have c3 := card_biUnion_le (s := SK) (t := om D (layer D V 2 u))
      have := card_le_card SKX
      omega

/-- **Profile II (generic, `8 ≤ q`).** Layers `|Y| = q + 2`, `|Z| = q`, `|W| = q` do not occur. -/
theorem profileII (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 2) (hZ : (layer D V 3 u).card = q)
    (hW : (layer D V 4 u).card = q) : False := by
  have XV : outN D V u ⊆ V := outN_subset
  by_cases h : ∃ v ∈ layer D V 2 u, OnCyc D (layer D V 2 u) v
  · obtain ⟨v, hv, oc⟩ := h
    exact caseA free hq reg hu hY hZ hW hv oc
  · push Not at h
    have acY : QFree D (layer D V 2 u) (q + 2) := by
      intro a ℓ h1 _ w
      cases w with
      | refl => omega
      | step hb ab rest =>
        have aY : a ∈ layer D V 2 u := by
          rcases rest.end_mem_or with e | h'
          · rw [e]; exact hb
          · exact h'
        exact h a aY ⟨_, hb, ab, _, rest⟩
    rcases split_bank free (by omega) XV (reg u hu) with cycX | ⟨acX, -⟩
    · exact caseB_cyc free hq reg hu hY hZ acY cycX
    · exact caseB_acyc free hq reg hu hY hZ acY acX

/-- **Profile II at order 72** (`q = 8`, `r = 9`): layers `(10, 8, 8)` do not occur. -/
theorem profileII_72 (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (hY : (layer D V 2 u).card = 10) (hZ : (layer D V 3 u).card = 8)
    (hW : (layer D V 4 u).card = 8) : False :=
  profileII (q := 8) free le_rfl reg hu hY hZ hW

#print axioms ii1
#print axioms caseA
#print axioms caseB_cyc
#print axioms caseB_acyc
#print axioms profileII
#print axioms profileII_72

end LeanCH.BR.Profiles72
