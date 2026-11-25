import checkpoints.shen_extension.SupplierRow

/-!
# Lemma 5 and the nonthin supplier law on the whole row `r = q + 3`

`free : QFree D V q`, `6 ≤ q`, every out-degree `q + 3`, a root `u ∈ V` with
`X = outN D V u`, `Y = layer D V 2 u`, `|Y| = q + 3`.

* G1 `lemma5_row` (generic): `oSet D V u ≠ Y`, i.e. some row of `Y` reaches no tail inside `Y`.
  This is `SupplierFat54.lemma5` with the thresholds written in `q`:
  - `case_reach_row`: a target is not in `near (q - 2)` (`tgt_not_near_row`, Fact B at a sink),
    so `near 0 ⊊ … ⊊ near (q - 2)` (`near_chain_row`), `|near (q - 3)| ≥ q - 2`, and the targets
    and their `X`-heads lie in `M = X \ near (q - 3)` with `|M| ≤ 5`. Every target omits at
    most `4 ≤ q - 2` labels (Fact C with `j = 0`); the arc count inside the targets bounds the
    union of omission sets by `8 < q + 3`. The numbers `4, 5, 8` do not move with `q`.
  - `case_far_row`: `OneHead.lone_within` (`k = 2`, `|far| ≤ q + 3`) replaces `lone_two_six`.
  `|Z| = q + 2` is not needed for G1.
* G2 `fat_supplier_row` (generic): a root with layers `(q + 3, q + 2)` has at least two rows of
  `zRows D V Z` with `|B_3| ≥ 3(q + 3) + 1`: `SupplierRow.fat_supplier_row` (which assembles
  `two_suppliers`, `no_return`, `FragmentBudget.exterior_floor`) with its ancestor hypothesis
  discharged by G1. `s2_row` is the same in the shape of `Laws54.s2`.
* G3 (instances `q = 6`): `lemma5_six` (statement of `SupplierFat54.lemma5`) and `s2_six`
  (statement of `SupplierFat54.s2`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.AncestorRow
open Finset BRq2 BRq3 ThinSuppliers OneHead
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Supplier54 (zRows)
open SupplierFat54 (oSet aSet a_nonempty x_split om mem_om om_card fact_B fact_C arc_count bu_one
  bu_two snk near mem_near near_sub near_mono near_step near_flat tgt far mem_far far_sub far_out
  far_deg o_cover)

variable {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}

/-- **The chain (generic).** A row reaching a sink but not within `q - 2` steps:
`|near (q - 3)| ≥ q - 2` and `near (q - 2) ≠ near (q - 3)` (`3 ≤ q`). -/
theorem near_chain_row (hq : 3 ≤ q) {x m s0 : ℕ} (s0s : s0 ∈ snk D V u)
    (sb : s0 ∈ ball D (outN D V u) x m) (xX : x ∈ outN D V u) (xn : x ∉ near D V u (q - 2)) :
    q - 2 ≤ (near D V u (q - 3)).card ∧ (near D V u (q - 2) \ near D V u (q - 3)).Nonempty := by
  have strict : ∀ k, k + 1 ≤ q - 2 → near D V u k ⊂ near D V u (k + 1) := by
    intro k hk
    refine ssubset_of_subset_of_ne (near_mono (by omega)) (fun e => xn ?_)
    have xin : x ∈ near D V u (k + m) :=
      mem_near.mpr ⟨xX, s0, s0s, ball_mono_radius (by omega) sb⟩
    exact near_mono (by omega) (near_flat e m xin)
  have s0X := (mem_filter.mp s0s).1
  have n0 : 1 ≤ (near D V u 0).card :=
    card_pos.mpr ⟨s0, mem_near.mpr ⟨s0X, s0, s0s, self_mem_ball s0X⟩⟩
  have grow : ∀ k, k ≤ q - 3 → k + 1 ≤ (near D V u k).card := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have c := card_lt_card (strict k (by omega))
      have := ih (by omega)
      omega
  refine ⟨by have := grow (q - 3) le_rfl; omega, ?_⟩
  obtain ⟨z, hz4, hz3⟩ := exists_of_ssubset (strict (q - 3) (by omega))
  rw [show q - 3 + 1 = q - 2 by omega] at hz4
  exact ⟨z, mem_sdiff.mpr ⟨hz4, hz3⟩⟩

section five
variable (free : QFree D V q) (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3)
  (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 3)

include free hq reg hu hY in
/-- A head of `u` omits at most as many labels of `Y` as it has heads in `X`. -/
theorem om_le_row {c : ℕ} (hc : c ∈ outN D V u) :
    (om D (layer D V 2 u) c).card ≤ (outN D (outN D V u) c).card := by
  have := x_split free hu (q := q) (by omega) reg hc
  have := om_card (D := D) (layer D V 2 u) c
  rw [hY] at this
  omega

include free hq reg hu hY in
/-- A sink of `X` points to all of `Y`. -/
theorem sink_full_row {s : ℕ} (hs : s ∈ snk D V u) {a : ℕ} (ha : a ∈ layer D V 2 u) :
    D s a = true := by
  obtain ⟨sX, e⟩ := mem_filter.mp hs
  have h1 := om_le_row free hq reg hu hY sX
  rw [e, card_empty] at h1
  by_contra h
  have : a ∈ om D (layer D V 2 u) s := mem_om.mpr ⟨ha, h⟩
  have := card_pos.mpr ⟨a, this⟩
  omega

include free hq reg hu hY in
/-- **Fact A at a sink (generic).** A target is not within `q - 2` steps of a sink. -/
theorem tgt_not_near_row {x : ℕ} (hx : x ∈ tgt D V u) : x ∉ near D V u (q - 2) := by
  intro hn
  obtain ⟨xX, t, tY, tx⟩ := mem_filter.mp hx
  obtain ⟨-, s, hs, sb⟩ := mem_near.mp hn
  obtain ⟨-, j, hj, w⟩ := mem_ball.mp sb
  exact fact_B free (outN_subset xX) (layer_subset tY) tx (w.mono outN_subset)
    (sink_full_row free hq reg hu hY hs tY) (.refl t) (by omega)

include free hq reg hu hY in
/-- The `X`-heads of a target lie in `X \ near (q - 3)`. -/
theorem tgt_heads_row {x : ℕ} (hx : x ∈ tgt D V u) :
    outN D (outN D V u) x ⊆ (outN D V u \ near D V u (q - 3)).erase x := by
  intro h hh
  obtain ⟨hX, xh⟩ := mem_outN.mp hh
  have xX := (mem_filter.mp hx).1
  refine mem_erase.mpr ⟨fun e => ?_, mem_sdiff.mpr ⟨hX, fun hn => tgt_not_near_row free hq reg hu hY hx ?_⟩⟩
  · rw [e] at xh
    exact loopfree free (by omega) (outN_subset xX) xh
  · have := near_step xX hX xh hn
    rwa [show q - 3 + 1 = q - 2 by omega] at this

include free hq in
/-- A tail omitted by its target and by every head of its target. -/
theorem tail_om_row {t x : ℕ} (tY : t ∈ layer D V 2 u) (xV : x ∈ V) (tx : D t x = true) :
    t ∈ om D (layer D V 2 u) x ∧ ∀ h, h ∈ V → D x h = true → t ∈ om D (layer D V 2 u) h := by
  have tV := layer_subset tY
  refine ⟨mem_om.mpr ⟨tY, fun xt => digonfree free (by omega) tV xV tx xt⟩,
    fun h hV xh => mem_om.mpr ⟨tY, fun ht => ?_⟩⟩
  exact free t 3 (by norm_num) (by omega) (.step xV tx (.step hV xh (.step tV ht (.refl t))))

include free hq reg hu hY in
/-- **Lemma 5, a target reaches a sink (generic).** -/
theorem case_reach_row (hO : oSet D V u = layer D V 2 u) {x0 s0 m : ℕ} (hx0 : x0 ∈ tgt D V u)
    (s0s : s0 ∈ snk D V u) (sb : s0 ∈ ball D (outN D V u) x0 m) : False := by
  have XV : outN D V u ⊆ V := outN_subset
  have hXc : (outN D V u).card = q + 3 := reg u hu
  have QX : tgt D V u ⊆ outN D V u := filter_subset _ _
  obtain ⟨n3, z, hz⟩ := near_chain_row (by omega) s0s sb (QX hx0)
    (tgt_not_near_row free hq reg hu hY hx0)
  obtain ⟨hz4, hz3⟩ := mem_sdiff.mp hz
  have QM : tgt D V u ⊆ outN D V u \ near D V u (q - 3) := fun x hx =>
    mem_sdiff.mpr ⟨QX hx, fun h => tgt_not_near_row free hq reg hu hY hx (near_mono (by omega) h)⟩
  have zMQ : z ∈ (outN D V u \ near D V u (q - 3)) \ tgt D V u :=
    mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨near_sub hz4, hz3⟩, fun h => tgt_not_near_row free hq reg hu hY h hz4⟩
  have cM : (outN D V u \ near D V u (q - 3)).card = (outN D V u).card - (near D V u (q - 3)).card :=
    card_sdiff_of_subset near_sub
  have n3X := card_le_card (near_sub (D := D) (V := V) (u := u) (k := q - 3))
  have cMQ : ((outN D V u \ near D V u (q - 3)) \ tgt D V u).card =
      (outN D V u \ near D V u (q - 3)).card - (tgt D V u).card := card_sdiff_of_subset QM
  have pos : 1 ≤ ((outN D V u \ near D V u (q - 3)) \ tgt D V u).card := card_pos.mpr ⟨z, zMQ⟩
  have qM := card_le_card QM
  -- every target omits at most four labels (`|M| ≤ 5`)
  have heads4 : ∀ x ∈ tgt D V u, (outN D (outN D V u) x).card ≤ 4 := by
    intro x hx
    have := card_le_card (tgt_heads_row free hq reg hu hY hx)
    rw [card_erase_of_mem (QM hx)] at this
    omega
  have cover : layer D V 2 u ⊆ (tgt D V u).biUnion (om D (layer D V 2 u)) := by
    intro a ha
    obtain ⟨t, x, j, hx, -, tx, w⟩ := o_cover hO ha
    have xX := QX hx
    have small : (om D (layer D V 2 u) x).card + 0 + 2 ≤ q := by
      have := om_le_row free hq reg hu hY xX
      have := heads4 x hx
      omega
    exact mem_biUnion.mpr ⟨x, hx, fact_C free layer_subset (XV xX) tx (.refl x) small ha w⟩
  have rowb : ∀ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ≤
      (outN D (tgt D V u) x).card + ((outN D V u \ near D V u (q - 3)) \ tgt D V u).card := by
    intro x hx
    have h1 := om_le_row free hq reg hu hY (QX hx)
    have sub : outN D (outN D V u) x ⊆
        outN D (tgt D V u) x ∪ ((outN D V u \ near D V u (q - 3)) \ tgt D V u) := by
      intro h hh
      have hM := mem_of_mem_erase (tgt_heads_row free hq reg hu hY hx hh)
      by_cases hq' : h ∈ tgt D V u
      · exact mem_union_left _ (mem_outN.mpr ⟨hq', (mem_outN.mp hh).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hM, hq'⟩)
    have := (card_le_card sub).trans (card_union_le _ _)
    omega
  have sumb : ∑ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ≤
      ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card +
        (tgt D V u).card * ((outN D V u \ near D V u (q - 3)) \ tgt D V u).card := by
    calc _ ≤ ∑ x ∈ tgt D V u, ((outN D (tgt D V u) x).card +
          ((outN D V u \ near D V u (q - 3)) \ tgt D V u).card) := sum_le_sum rowb
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have cu := card_le_card cover
  have cb := card_biUnion_le (s := tgt D V u) (t := om D (layer D V 2 u))
  have arc := arc_count (free.mono_set (QX.trans XV)) (by omega : 2 ≤ q)
  -- overlaps
  have excess : ((tgt D V u).biUnion (om D (layer D V 2 u))).card + 2 ≤
        ∑ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ∨
      (((tgt D V u).biUnion (om D (layer D V 2 u))).card + 1 ≤
        ∑ x ∈ tgt D V u, (om D (layer D V 2 u) x).card ∧
        ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card ≤ (tgt D V u).card) ∨
      ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card = 0 := by
    by_cases two : ∃ x ∈ tgt D V u, 2 ≤ (outN D (tgt D V u) x).card
    · obtain ⟨x, hx, h2⟩ := two
      obtain ⟨b1, hb1, b2, hb2, n12⟩ := one_lt_card.mp (show 1 < (outN D (tgt D V u) x).card by omega)
      obtain ⟨b1Q, xb1⟩ := mem_outN.mp hb1
      obtain ⟨b2Q, xb2⟩ := mem_outN.mp hb2
      obtain ⟨xX, t, tY, tx⟩ := mem_filter.mp hx
      have om3 := tail_om_row free hq tY (XV xX) tx
      have nb : ∀ b, D x b = true → x ≠ b := fun b xb e => by
        rw [← e] at xb; exact loopfree free (by omega) (XV xX) xb
      exact Or.inl (bu_two hx b1Q b2Q (nb b1 xb1) (nb b2 xb2) n12 om3.1
        (om3.2 _ (XV (QX b1Q)) xb1) (om3.2 _ (XV (QX b2Q)) xb2))
    · push Not at two
      have le1 : ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card ≤ (tgt D V u).card := by
        calc _ ≤ ∑ _x ∈ tgt D V u, 1 := sum_le_sum (fun x hx => by have := two x hx; omega)
          _ = _ := by rw [sum_const, smul_eq_mul, mul_one]
      by_cases one : ∃ x ∈ tgt D V u, 1 ≤ (outN D (tgt D V u) x).card
      · obtain ⟨x, hx, h1⟩ := one
        obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (outN D (tgt D V u) x).card by omega)
        obtain ⟨bQ, xb⟩ := mem_outN.mp hb
        obtain ⟨xX, t, tY, tx⟩ := mem_filter.mp hx
        have om3 := tail_om_row free hq tY (XV xX) tx
        have nb : x ≠ b := fun e => by
          rw [← e] at xb; exact loopfree free (by omega) (XV xX) xb
        exact Or.inr (Or.inl ⟨bu_one hx bQ nb om3.1 (om3.2 _ (XV (QX bQ)) xb), le1⟩)
      · push Not at one
        refine Or.inr (Or.inr (sum_eq_zero (fun x hx => by have := one x hx; omega)))
  rw [hY] at cu
  obtain ⟨k, hk⟩ : ∃ k, (tgt D V u).card = k := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, ∑ x ∈ tgt D V u, (outN D (tgt D V u) x).card = E := ⟨_, rfl⟩
  obtain ⟨mq, hmq⟩ : ∃ mq, ((outN D V u \ near D V u (q - 3)) \ tgt D V u).card = mq := ⟨_, rfl⟩
  rw [hk, hE, hmq] at sumb
  rw [hk, hE] at arc
  rw [hE, hk] at excess
  rw [hmq] at pos cMQ
  rw [hk] at cMQ qM
  have hk4 : k ≤ 4 := by omega
  interval_cases k <;> omega

include free hq reg hu hY in
/-- **Lemma 5, no target reaches a sink (generic).** -/
theorem case_far_row (hO : oSet D V u = layer D V 2 u)
    (hnone : ¬ ∃ x ∈ tgt D V u, ∃ s ∈ snk D V u, ∃ k, s ∈ ball D (outN D V u) x k) : False := by
  have XV : outN D V u ⊆ V := outN_subset
  have hXc : (outN D V u).card = q + 3 := reg u hu
  have RX : far D V u ⊆ outN D V u := far_sub
  have frR : QFree D (far D V u) q := free.mono_set (RX.trans XV)
  have degR : ∀ c ∈ far D V u, 1 ≤ (outN D (far D V u) c).card := fun c hc => far_deg hc
  have RC := card_le_card RX
  have QX : tgt D V u ⊆ outN D V u := filter_subset _ _
  have tgtR : ∀ x ∈ tgt D V u, x ∈ far D V u := fun x hx =>
    mem_far.mpr ⟨QX hx, fun ⟨s, hs, k, sb⟩ => hnone ⟨x, hx, s, hs, k, sb⟩⟩
  have om1 : ∀ e ∈ lone D (far D V u), (om D (layer D V 2 u) e).card ≤ 1 := by
    intro e he
    have eR := lone_subset he
    have := om_le_row free hq reg hu hY (RX eR)
    rw [← far_out eR] at this
    have := (mem_lone.mp he).2
    omega
  have cover : layer D V 2 u ⊆ (lone D (far D V u)).biUnion (om D (layer D V 2 u)) := by
    intro a ha
    obtain ⟨t, x, j, hx, -, tx, w⟩ := o_cover hO ha
    obtain ⟨e, eb, el⟩ := lone_within frR (by omega) degR (k := 2) (by omega) (by omega) (by omega)
      (tgtR x hx)
    obtain ⟨-, i, hi, we⟩ := mem_ball.mp eb
    have small : (om D (layer D V 2 u) e).card + i + 2 ≤ q := by
      have := om1 e el
      omega
    exact mem_biUnion.mpr ⟨e, el, fact_C free layer_subset (XV (QX hx)) tx
      (we.mono (RX.trans XV)) small ha w⟩
  have sumle : ∑ e ∈ lone D (far D V u), (om D (layer D V 2 u) e).card ≤
      (lone D (far D V u)).card := by
    calc _ ≤ ∑ _e ∈ lone D (far D V u), 1 := sum_le_sum om1
      _ = _ := by rw [sum_const, smul_eq_mul, mul_one]
  have cu := card_le_card cover
  have cb := card_biUnion_le (s := lone D (far D V u)) (t := om D (layer D V 2 u))
  have LR := card_le_card (lone_subset (D := D) (S := far D V u))
  rw [hY] at cu
  by_cases full : (lone D (far D V u)).card = q + 3
  · have LX : lone D (far D V u) = outN D V u :=
      eq_of_subset_of_card_le (lone_subset.trans RX) (by omega)
    obtain ⟨a, ha⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
    obtain ⟨t, x, j, hx, tY, tx, -⟩ := o_cover hO ha
    have xL : x ∈ lone D (far D V u) := by rw [LX]; exact QX hx
    obtain ⟨hR, xh⟩ := hd_mem degR xL
    have hL : hd D (far D V u) x ∈ lone D (far D V u) := by rw [LX]; exact RX hR
    have om3 := tail_om_row free hq tY (XV (QX hx)) tx
    have nb : x ≠ hd D (far D V u) x := fun e => by
      rw [← e] at xh; exact loopfree free (by omega) (XV (QX hx)) xh
    have := bu_one xL hL nb om3.1 (om3.2 _ (XV (RX hR)) xh)
    omega
  · omega

include free hq reg hu hY in
/-- **G1, Lemma 5 on the row `r = q + 3` (generic, `6 ≤ q`, `|Y| = q + 3`).** Some row of `Y`
reaches no tail inside `Y`. -/
theorem lemma5_row : oSet D V u ≠ layer D V 2 u := by
  intro hO
  by_cases h : ∃ x ∈ tgt D V u, ∃ s ∈ snk D V u, ∃ k, s ∈ ball D (outN D V u) x k
  · obtain ⟨x, hx, s, hs, k, sb⟩ := h
    exact case_reach_row free hq reg hu hY hO hx hs sb
  · exact case_far_row free hq reg hu hY hO h

end five

/-- **G2, the nonthin supplier law on the row `r = q + 3` (generic, `6 ≤ q`).** A root with
layers `(q + 3, q + 2)` has at least two rows of `zRows D V Z` with `|B_3| ≥ 3(q + 3) + 1`. -/
theorem fat_supplier_row (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) (hu : u ∈ V)
    (hY : (layer D V 2 u).card = q + 3) (hZc : (layer D V 3 u).card = q + 2) :
    2 ≤ ((zRows D V (layer D V 3 u)).filter
      (fun s => 3 * (q + 3) + 1 ≤ (ball D V s 3).card)).card :=
  SupplierRow.fat_supplier_row free hq reg hu hY hZc (a_nonempty (lemma5_row free hq reg hu hY))

/-- **G2 in the shape of `Laws54.s2` (generic).** -/
theorem s2_row (free : QFree D V q) (hq : 6 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 3) :
    ∀ u ∈ V, ¬ Thin D V (q + 3) u → (layer D V 2 u).card = q + 3 →
      (layer D V 3 u).card = q + 2 →
      2 ≤ ((zRows D V (layer D V 3 u)).filter
        (fun s => 3 * (q + 3) + 1 ≤ (ball D V s 3).card)).card :=
  fun _ hu _ hY hZ => fat_supplier_row free hq reg hu hY hZ

/-! ### G3: the instances at `q = 6` -/

/-- `SupplierFat54.lemma5` as the instance `q = 6` of G1. -/
theorem lemma5_six (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (hY : (layer D V 2 u).card = 9) : oSet D V u ≠ layer D V 2 u :=
  lemma5_row (q := 6) free le_rfl reg hu hY

/-- `SupplierFat54.s2` (same statement) as the instance `q = 6` of G2. -/
theorem s2_six (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    ∀ u ∈ V, ¬ Thin D V 9 u → (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
      2 ≤ (Supplier54.zSet D V (layer D V 3 u)).card := by
  intro u hu _ hY hZ
  have t := fat_supplier_row (q := 6) free le_rfl reg hu hY hZ
  refine t.trans (card_le_card (fun s hs => ?_))
  obtain ⟨hz, hb⟩ := mem_filter.mp hs
  obtain ⟨sV, a, b, c⟩ := mem_filter.mp hz
  exact mem_filter.mpr ⟨sV, by omega, a, b, c⟩

#print axioms near_chain_row
#print axioms om_le_row
#print axioms tgt_not_near_row
#print axioms case_reach_row
#print axioms case_far_row
#print axioms lemma5_row
#print axioms fat_supplier_row
#print axioms s2_row
#print axioms lemma5_six
#print axioms s2_six

end LeanCH.BR.AncestorRow
