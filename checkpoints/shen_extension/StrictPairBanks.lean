import checkpoints.shen_extension.ReachLedgerCatalog

/-!
# Strict pair banks: the slack forms of the reach ledger

Lean 4.35.0. Every theorem is stated for an arbitrary digraph `D`, label set `V`, cutoff `q`,
degree `r`, order `n = |V|` and radii. No order, cutoff or degree is fixed in this file.

The inequalities of `ReachLedger` (`parent_cap`, `supplier_cap`, `budget`, `class_count`,
`class_roots`) are here restated with their slack written out as explicit counts. When an
inequality is tight, the slack counts vanish, and the labelled facts of the paper (all parents
tight, banks disjoint, missing pairs inside classes) are the zero-slack corollaries.

## Sets

* `level D V i a`: rows whose `i`-ball has exactly `a` labels; `above D V i a`: more than `a`.
* The second shell `ball v 2 \ ball v 1` is written out; its classes are the fibres of
  `R.image (fun v => ball D V v 2 \ ball D V v 1)`.
* `idle D S T`: the rows of `T` with no head in `S`.

## Slack laws

* `parent_slack`: `indeg v + |ball v i| + #(labels outside the ball that are not parents) = |V|`.
* `supplier_slack`: rows of `T` heading `S`, rows outside `T` heading `S`, and rows heading two
  labels of `S`, together, are at most the indegree sum of `S`.
* `supplier_cap_slack`: the same against the forward balls of `S`.
* `level_slack`: `m` rows `m` above the floor cost `2 m` each out of the unspent budget.
* `class_slack`: `2 |R| + Σ (m-1)(m-2) + #(gaps leaving a class) ≤ 2 #classes + Σ_R gaps`.
* `class_count_slack`: rows of `H` complete for no root are paid on top of `(q+1) #classes`.

## Zero-slack corollaries

* `parents_full`, `suppliers_inside`, `suppliers_single`, `class_zero`, `gaps_inside`.

## Profile law and regimes

* `profile_law`: floor `2 r` at radius two, degree exactly `r`, cutoff `q ≥ 4`. With `S` the rows
  two above the floor, `R` the tight rows heading no row of `S`, and `c` the second-shell classes
  of `R`: one inequality binding order, the third balls of `S`, `|S|`, the excess `e`, `c` and all
  seven slack counts; `(q+1) c` plus unused tied rows within the tied rows; and the exact budget.
* `strict_count_regime`: the profile law closes every `(q, r, n, s)` with
  `n(n+1) + 2sn + 2⌊(n(n+1) - 4rn - 4s - 2x)/(2(q+1))⌋ < 2(n + s b + k + s + x) + 4rn`.
* `regular_of_lower`: for `r ≤ 2 q` the first-layer regularity hypothesis is automatic from
  `NoHost q 2`.
* `four_diagonal`, `four_diagonal_lower`: on `4 r` labels every such host has two strict rows.

## Catalog

* `Slack D V q` from `QFree D V q` (`slack_packet`, rule set `CHGraphFamilies`): parent slack,
  supplier cap slack and level slack at every admissible radius.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.StrictPairBanks
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### Sets -/

/-- Rows whose `i`-ball has exactly `a` labels. -/
noncomputable def level (D : CH.Digraph) (V : Finset ℕ) (i a : ℕ) : Finset ℕ :=
  V.filter (fun v => (ball D V v i).card = a)

/-- Rows whose `i`-ball has more than `a` labels. -/
noncomputable def above (D : CH.Digraph) (V : Finset ℕ) (i a : ℕ) : Finset ℕ :=
  V.filter (fun v => a < (ball D V v i).card)

/-- The rows of `T` with no head in `S`. -/
noncomputable def idle (D : CH.Digraph) (S T : Finset ℕ) : Finset ℕ :=
  T.filter (fun v => outN D S v = ∅)

/-! ### Parent slack -/

/-- **Parent slack.** Parents, the forward ball and the labels outside both partition the labels. -/
theorem parent_slack {i v : ℕ} (free : QFree D V q) (hi : i + 1 ≤ q) (vv : v ∈ V) :
    (inN D V v).card + (ball D V v i).card + ((V \ ball D V v i) \ inN D V v).card = V.card := by
  classical
  have sub1 : inN D V v ⊆ V \ ball D V v i := fun x hx =>
    mem_sdiff.mpr ⟨(mem_inN.mp hx).1, fun hb => no_back_arc free vv hb hi (mem_inN.mp hx).2⟩
  have sub2 : ball D V v i ⊆ V := ball_subset
  have c1 := card_sdiff_of_subset sub1
  have c2 := card_sdiff_of_subset sub2
  have l1 := card_le_card sub1
  have l2 := card_le_card sub2
  omega

/-- Zero parent slack: every label outside the forward ball is a parent. -/
theorem parents_full {j : ℕ} {S : Finset ℕ}
    (zero : ∑ s ∈ S, ((V \ ball D V s j) \ inN D V s).card = 0) {s w : ℕ} (ss : s ∈ S)
    (wv : w ∈ V) (off : w ∉ ball D V s j) : w ∈ inN D V s := by
  have e := (sum_eq_zero_iff.mp zero) s ss
  by_contra h
  have mem : w ∈ (V \ ball D V s j) \ inN D V s := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨wv, off⟩, h⟩
  rw [card_eq_zero.mp e] at mem
  simp at mem

/-! ### Supplier slack -/

theorem heading_split {S T : Finset ℕ} (tv : T ⊆ V) :
    (V.filter (fun v => outN D S v ≠ ∅)).card =
      (T.filter (fun v => outN D S v ≠ ∅)).card
        + ((V \ T).filter (fun v => outN D S v ≠ ∅)).card := by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff), ← filter_union,
    union_sdiff_of_subset tv]

/-- **Supplier slack.** Rows of `T` heading `S`, rows outside `T` heading `S`, and rows heading at
least two labels of `S` are together paid by the indegrees of `S`. -/
theorem supplier_slack {S T : Finset ℕ} (tv : T ⊆ V) :
    (T.filter (fun v => outN D S v ≠ ∅)).card + ((V \ T).filter (fun v => outN D S v ≠ ∅)).card
      + (V.filter (fun v => 2 ≤ (outN D S v).card)).card ≤ ∑ s ∈ S, (inN D V s).card := by
  classical
  have dc : ∑ s ∈ S, (inN D V s).card = ∑ v ∈ V, (outN D S v).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun s v => D v s = true)
  have each : ∀ v ∈ V, ((if outN D S v ≠ ∅ then 1 else 0)
      + (if 2 ≤ (outN D S v).card then 1 else 0)) ≤ (outN D S v).card := by
    intro v _
    by_cases e : outN D S v = ∅
    · simp [e]
    · have pos : 0 < (outN D S v).card := card_pos.mpr (nonempty_iff_ne_empty.mpr e)
      split_ifs <;> omega
  have total := sum_le_sum each
  rw [sum_add_distrib, ← card_filter, ← card_filter] at total
  rw [← heading_split tv, dc]
  exact total

/-- **Supplier cap slack.** Against the forward balls of `S`: the parent slacks of `S`, the rows
outside `T` heading `S` and the rows heading two labels of `S` all count. -/
theorem supplier_cap_slack {j : ℕ} (free : QFree D V q) (hj : j + 1 ≤ q) {S T : Finset ℕ}
    (sv : S ⊆ V) (tv : T ⊆ V) :
    (T.filter (fun v => outN D S v ≠ ∅)).card + ((V \ T).filter (fun v => outN D S v ≠ ∅)).card
      + (V.filter (fun v => 2 ≤ (outN D S v).card)).card
      + ∑ s ∈ S, ((V \ ball D V s j) \ inN D V s).card + ∑ s ∈ S, (ball D V s j).card
      ≤ S.card * V.card := by
  have a := supplier_slack (D := D) (S := S) tv
  have b : ∑ s ∈ S, ((inN D V s).card + (ball D V s j).card
      + ((V \ ball D V s j) \ inN D V s).card) = ∑ _s ∈ S, V.card :=
    sum_congr rfl (fun s ss => parent_slack free hj (sv ss))
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul] at b
  omega

/-- Zero slack outside `T`: every parent of `S` lies in `T`. -/
theorem suppliers_inside {S T : Finset ℕ}
    (zero : ((V \ T).filter (fun v => outN D S v ≠ ∅)).card = 0) {s p : ℕ} (ss : s ∈ S)
    (hp : p ∈ inN D V s) : p ∈ T := by
  obtain ⟨pv, arc⟩ := mem_inN.mp hp
  by_contra pt
  have mem : p ∈ (V \ T).filter (fun v => outN D S v ≠ ∅) := by
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨pv, pt⟩, fun e => ?_⟩
    have hs : s ∈ outN D S p := mem_outN.mpr ⟨ss, arc⟩
    rw [e] at hs
    simp at hs
  rw [card_eq_zero.mp zero] at mem
  simp at mem

/-- Zero slack on double rows: no row heads two labels of `S`. -/
theorem suppliers_single {S : Finset ℕ}
    (zero : (V.filter (fun v => 2 ≤ (outN D S v).card)).card = 0) {s s' : ℕ} (ss : s ∈ S)
    (ss' : s' ∈ S) (ne : s ≠ s') : Disjoint (inN D V s) (inN D V s') := by
  classical
  rw [disjoint_left]
  intro p hp hp'
  obtain ⟨pv, arc⟩ := mem_inN.mp hp
  have arc' := (mem_inN.mp hp').2
  have two : 2 ≤ (outN D S p).card := by
    have sub : ({s, s'} : Finset ℕ) ⊆ outN D S p := by
      intro x hx
      rcases mem_insert.mp hx with e | e
      · rw [e]; exact mem_outN.mpr ⟨ss, arc⟩
      · rw [mem_singleton.mp e]; exact mem_outN.mpr ⟨ss', arc'⟩
    have := card_le_card sub
    rwa [card_pair ne] at this
  have mem : p ∈ V.filter (fun v => 2 ≤ (outN D S v).card) := mem_filter.mpr ⟨pv, two⟩
  rw [card_eq_zero.mp zero] at mem
  simp at mem

/-! ### Budget slack -/

/-- **Level slack.** Rows at least `m` above the floor cost `2 m` each out of the unspent
budget, next to the gaps. -/
theorem level_slack {i a m : ℕ} (free : QFree D V q) (hi : i + i ≤ q)
    (floor : ∀ v ∈ V, a ≤ (ball D V v i).card) :
    2 * (m * (V.filter (fun v => a + m ≤ (ball D V v i).card)).card)
      + ∑ v ∈ V, (gap D V i i v).card + V.card * (a + a) ≤ V.card * (V.card + 1) := by
  have spend := budget free hi floor floor
  have sub : ∑ v ∈ V.filter (fun v => a + m ≤ (ball D V v i).card), ((ball D V v i).card - a)
      ≤ ∑ v ∈ V, ((ball D V v i).card - a) := sum_le_sum_of_subset (filter_subset _ _)
  have low : ∑ _v ∈ V.filter (fun v => a + m ≤ (ball D V v i).card), m
      ≤ ∑ v ∈ V.filter (fun v => a + m ≤ (ball D V v i).card), ((ball D V v i).card - a) :=
    sum_le_sum (fun v hv => by have := (mem_filter.mp hv).2; omega)
  rw [sum_const, smul_eq_mul] at low
  have comm : m * (V.filter (fun v => a + m ≤ (ball D V v i).card)).card
      = (V.filter (fun v => a + m ≤ (ball D V v i).card)).card * m := Nat.mul_comm _ _
  omega

/-- Three bands below, at and above one level. -/
theorem level_split (c : ℕ → ℕ) (a : ℕ) (S : Finset ℕ) (floor : ∀ v ∈ S, a ≤ c v) :
    (S.filter (fun v => c v = a)).card + (S.filter (fun v => c v = a + 1)).card
      + (S.filter (fun v => a + 1 < c v)).card = S.card := by
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib, ← sum_add_distrib,
    card_eq_sum_ones]
  refine sum_congr rfl (fun v vs => ?_)
  have := floor v vs
  split_ifs <;> omega

theorem count_split (c : ℕ → ℕ) (a : ℕ) (S : Finset ℕ) :
    (S.filter (fun v => a < c v)).card =
      (S.filter (fun v => c v = a + 1)).card + (S.filter (fun v => a + 1 < c v)).card := by
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  refine sum_congr rfl (fun v _ => ?_)
  split_ifs <;> omega

/-! ### Class slack -/

theorem pair_arith (m : ℕ) (h : 1 ≤ m) : 2 * m + (m - 1) * (m - 2) ≤ 2 + m * (m - 1) := by
  rcases m with _ | _ | j
  · omega
  · simp
  · have e1 : j + 1 + 1 - 1 = j + 1 := by omega
    have e2 : j + 1 + 1 - 2 = j := by omega
    rw [e1, e2]
    have : 2 * (j + 1 + 1) + (j + 1) * j = 2 + (j + 1 + 1) * (j + 1) := by ring
    omega

/-- A root of a class: the rest of its class, then its gaps outside the class. -/
theorem class_row {r : ℕ} {R : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (rv : R ⊆ V)
    (deg : ∀ v ∈ R, (outN D V v).card = r) {v : ℕ} (vr : v ∈ R) :
    (R.filter (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card - 1
      + (gap D V 2 2 v \ R.filter
          (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card
      ≤ (gap D V 2 2 v).card := by
  classical
  have vin : v ∈ R.filter (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1) :=
    mem_filter.mpr ⟨vr, rfl⟩
  have inc : (R.filter (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).erase v
      ⊆ gap D V 2 2 v := by
    intro w hw
    obtain ⟨ne, hw⟩ := mem_erase.mp hw
    obtain ⟨wr, same⟩ := mem_filter.mp hw
    exact same_shell_gapped free hq (rv vr) (rv wr) ne ((deg v vr).trans (deg w wr).symm) same.symm
  have dis : Disjoint
      ((R.filter (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).erase v)
      (gap D V 2 2 v \ R.filter
        (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)) :=
    disjoint_left.mpr (fun w h1 h2 => (mem_sdiff.mp h2).2 (mem_of_mem_erase h1))
  have out : gap D V 2 2 v \ R.filter
      (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1) ⊆ gap D V 2 2 v :=
    sdiff_subset
  have le := card_le_card (union_subset inc out)
  rw [card_union_of_disjoint dis, card_erase_of_mem vin] at le
  exact le

/-- **Class slack.** The sharp form of `class_roots`: classes of three or more roots and gaps that
leave a class are paid on top of the base count. -/
theorem class_slack {r : ℕ} {R : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (rv : R ⊆ V)
    (deg : ∀ v ∈ R, (outN D V v).card = r) :
    2 * R.card
      + ∑ Y ∈ R.image (fun v => ball D V v 2 \ ball D V v 1),
          ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 1)
            * ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 2)
      + ∑ v ∈ R, (gap D V 2 2 v \ R.filter
          (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card
      ≤ 2 * (R.image (fun v => ball D V v 2 \ ball D V v 1)).card
        + ∑ v ∈ R, (gap D V 2 2 v).card := by
  classical
  have maps : ∀ v ∈ R, (fun v => ball D V v 2 \ ball D V v 1) v
      ∈ R.image (fun v => ball D V v 2 \ ball D V v 1) := fun v hv => mem_image_of_mem _ hv
  have each : ∀ Y ∈ R.image (fun v => ball D V v 2 \ ball D V v 1),
      2 * (R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card
        + ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 1)
          * ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 2)
        + ∑ v ∈ R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y),
            (gap D V 2 2 v \ R.filter
              (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card
      ≤ 2 + ∑ v ∈ R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y), (gap D V 2 2 v).card := by
    intro Y hY
    obtain ⟨v0, v0r, e0⟩ := mem_image.mp hY
    have pos : 1 ≤ (R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card :=
      card_pos.mpr ⟨v0, mem_filter.mpr ⟨v0r, e0⟩⟩
    have row : ∀ v ∈ R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y),
        ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 1)
          + (gap D V 2 2 v \ R.filter
              (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card
        ≤ (gap D V 2 2 v).card := by
      intro v hv
      have r0 := class_row (r := r) free hq rv deg (mem_filter.mp hv).1
      have e : ball D V v 2 \ ball D V v 1 = Y := (mem_filter.mp hv).2
      rw [e] at r0
      rw [e]
      exact r0
    have total := sum_le_sum row
    rw [sum_add_distrib, sum_const, smul_eq_mul] at total
    have ar := pair_arith _ pos
    omega
  have total := sum_le_sum each
  simp only [sum_add_distrib] at total
  rw [sum_const, smul_eq_mul, ← mul_sum, ← card_eq_sum_card_image,
    sum_fiberwise_of_maps_to maps, sum_fiberwise_of_maps_to maps] at total
  omega

/-- Zero class slack: classes have at most two roots and every gap of a root stays in its class. -/
theorem class_zero {R : Finset ℕ}
    (big : ∑ Y ∈ R.image (fun v => ball D V v 2 \ ball D V v 1),
          ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 1)
            * ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 2) = 0)
    (cross : ∑ v ∈ R, (gap D V 2 2 v \ R.filter
          (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card = 0) :
    (∀ v ∈ R, (R.filter
        (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card ≤ 2) ∧
      (∀ v ∈ R, gap D V 2 2 v ⊆ R.filter
        (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)) := by
  classical
  refine ⟨fun v vr => ?_, fun v vr => ?_⟩
  · have e := (sum_eq_zero_iff.mp big) _ (mem_image_of_mem (fun v => ball D V v 2 \ ball D V v 1) vr)
    rcases Nat.mul_eq_zero.mp e with h | h <;> omega
  · have e := (sum_eq_zero_iff.mp cross) v vr
    exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp e)

/-- Zero gap slack outside a set: rows outside it miss no pair. -/
theorem gaps_inside {R : Finset ℕ} (zero : ∑ v ∈ V \ R, (gap D V 2 2 v).card = 0) {v : ℕ}
    (vv : v ∈ V) (vr : v ∉ R) : gap D V 2 2 v = ∅ :=
  card_eq_zero.mp ((sum_eq_zero_iff.mp zero) v (mem_sdiff.mpr ⟨vv, vr⟩))

/-- **Class count slack.** Rows of `H` that are complete for no root are paid on top of the
`q + 1` rows owned by each class. -/
theorem class_count_slack {k r c : ℕ} {R H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card) (exact : ∀ y ∈ H, (outN D V y).card ≤ r)
    (cap : ∀ y ∈ H, (ball D V y 2).card ≤ c)
    (size : ∀ v ∈ R, (ball D V v (k+1) \ ball D V v k).card + 1 = r)
    (tight : ∀ v ∈ R, (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2)
    (live : ∀ v ∈ R, ∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x)
    (high : ∀ v ∈ R, ∀ x ∈ ball D V v k,
      ball D V v (k+1) \ ball D V v k ⊆ outN D V x → x ∈ H) :
    (q + 1) * (R.image (fun v => ball D V v (k+1) \ ball D V v k)).card
      + (H \ R.biUnion (fun v => (ball D V v k).filter
          (fun x => ball D V v (k+1) \ ball D V v k ⊆ outN D V x))).card ≤ H.card := by
  classical
  have cc := class_count (H := H ∩ R.biUnion (fun v => (ball D V v k).filter
      (fun x => ball D V v (k+1) \ ball D V v k ⊆ outN D V x))) free hq degree
    (fun y hy => exact y (mem_inter.mp hy).1) (fun y hy => cap y (mem_inter.mp hy).1) size tight
    live (fun v vr x xk full => mem_inter.mpr
      ⟨high v vr x xk full, mem_biUnion.mpr ⟨v, vr, mem_filter.mpr ⟨xk, full⟩⟩⟩)
  have split := card_sdiff_add_card_inter H (R.biUnion (fun v => (ball D V v k).filter
      (fun x => ball D V v (k+1) \ ball D V v k ⊆ outN D V x)))
  omega

/-! ### Profile law -/

/-- **Regular first layers from the degree-two quota.** A root of degree `r ≤ 2 q` never has a
first layer keeping two heads inside on every row. -/
theorem regular_of_lower {r v : ℕ} (lower : NoHost q 2) (free : QFree D V q) (hr : r ≤ 2 * q)
    (hr1 : 1 ≤ r) (vv : v ∈ V) (one : (ball D V v 1).card = r + 1) :
    ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card := by
  intro paid
  have vB : v ∈ ball D V v 1 := self_mem_ball vv
  have card := card_erase_add_one vB
  exact fragment_exit lower free ((erase_subset _ _).trans ball_subset)
    (card_pos.mp (by omega)) (by omega) paid

/-- **Profile law.** Cutoff `q ≥ 4`, degree exactly `r`, floor `2 r` at radius two, and the cap
`3 r ≤ |ball v 3| + 1` on tight rows. `S` is `above D V 2 (2r+1)`, `T` is `level D V 2 (2r)`,
`R = idle D S T`, and `c` counts the second-shell classes of `R`.

1. Order, third balls of `S`, `|S|` and the excess `e`, with the supplier slacks (parent slack of
   `S`, non-tight suppliers, double suppliers) counted twice and the class slacks (big classes,
   gaps leaving a class, gaps outside `R`) once, are paid by `2 c + n(n+1) + 2 |S| n - 4 r n`.
2. `(q + 1) c` plus the tied rows complete for no root are at most the tied rows.
3. The exact radius-two budget. -/
theorem profile_law {r : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hr : 1 ≤ r)
    (exact : ∀ v ∈ V, (outN D V v).card = r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ level D V 2 (2 * r), 3 * r ≤ (ball D V v 3).card + 1)
    (regular : ∀ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card) :
    2 * (V.card + ∑ s ∈ above D V 2 (2 * r + 1), (ball D V s 3).card
        + (above D V 2 (2 * r + 1)).card + ∑ v ∈ V, ((ball D V v 2).card - (2 * r + 2))
        + ∑ s ∈ above D V 2 (2 * r + 1), ((V \ ball D V s 3) \ inN D V s).card
        + ((V \ level D V 2 (2 * r)).filter
            (fun v => outN D (above D V 2 (2 * r + 1)) v ≠ ∅)).card
        + (V.filter (fun v => 2 ≤ (outN D (above D V 2 (2 * r + 1)) v).card)).card)
      + ∑ Y ∈ (idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).image
            (fun v => ball D V v 2 \ ball D V v 1),
          (((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).filter
              (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 1)
            * (((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).filter
              (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 2)
      + ∑ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
          (gap D V 2 2 v \ (idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).filter
            (fun w => ball D V w 2 \ ball D V w 1 = ball D V v 2 \ ball D V v 1)).card
      + ∑ v ∈ V \ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)), (gap D V 2 2 v).card
      + V.card * (4 * r)
    ≤ 2 * ((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).image
            (fun v => ball D V v 2 \ ball D V v 1)).card
      + V.card * (V.card + 1) + 2 * ((above D V 2 (2 * r + 1)).card * V.card)
    ∧ (q + 1) * ((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).image
            (fun v => ball D V v 2 \ ball D V v 1)).card
      + (level D V 2 (2 * r + 1) \ (idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).biUnion
          (fun v => (ball D V v 1).filter (fun x => ball D V v 2 \ ball D V v 1 ⊆ outN D V x))).card
      ≤ (level D V 2 (2 * r + 1)).card
    ∧ 2 * ((level D V 2 (2 * r + 1)).card + (above D V 2 (2 * r + 1)).card
        + (above D V 2 (2 * r + 1)).card + ∑ v ∈ V, ((ball D V v 2).card - (2 * r + 2)))
      + ∑ v ∈ V, (gap D V 2 2 v).card + V.card * (4 * r) = V.card * (V.card + 1) := by
  classical
  have degree : ∀ y ∈ V, r ≤ (outN D V y).card := fun y hy => (exact y hy).ge
  have Tv : level D V 2 (2 * r) ⊆ V := filter_subset _ _
  have Sv : above D V 2 (2 * r + 1) ⊆ V := filter_subset _ _
  have Rv : idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)) ⊆ V :=
    (filter_subset _ _).trans Tv
  have root : ∀ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
      v ∈ V ∧ (ball D V v 1).card = r + 1 ∧ (ball D V v 2 \ ball D V v 1).card + 1 = r ∧
        3 * r ≤ (ball D V v 3).card + 1 ∧
        ∀ x ∈ ball D V v 1, (ball D V x 2).card ≤ 2 * r + 1 := by
    intro v hv
    obtain ⟨hT, noS⟩ := mem_filter.mp hv
    obtain ⟨vv, tight⟩ := mem_filter.mp hT
    have one : (ball D V v 1).card = r + 1 := by rw [ball_one free (by omega) vv, exact v vv]
    have incl : ball D V v 1 ⊆ ball D V v 2 := ball_mono_radius (by omega)
    have sh := card_sdiff_of_subset incl
    have le := card_le_card incl
    refine ⟨vv, one, by omega, floor3 v hT, ?_⟩
    intro x hx
    rcases (mem_ball_one vv).mp hx with e | hx
    · rw [e]; omega
    · by_contra big
      have bad : x ∈ outN D (above D V 2 (2 * r + 1)) v :=
        mem_outN.mpr ⟨mem_filter.mpr ⟨(mem_outN.mp hx).1, by omega⟩, (mem_outN.mp hx).2⟩
      rw [noS] at bad
      simp at bad
  have live : ∀ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
      ∃ x ∈ ball D V v 1, ball D V v 2 \ ball D V v 1 ⊆ outN D V x := by
    intro v hv
    obtain ⟨vv, one, sh, _, _⟩ := root v hv
    have cf := complete_or_fragment (t := 2) (k := 1) (v := v) free degree vv (by omega)
    simp only [Nat.reduceAdd] at cf
    rcases cf (by omega) with h | h
    · exact h
    · exact absurd h (regular v hv)
  have high : ∀ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
      ∀ x ∈ ball D V v 1, ball D V v 2 \ ball D V v 1 ⊆ outN D V x →
      x ∈ level D V 2 (2 * r + 1) := by
    intro v hv x xk full
    obtain ⟨vv, one, sh, f3, capv⟩ := root v hv
    have room : (ball D V v 2 \ ball D V v 1).card < r := by omega
    have fl := complete_floor (k := 1) free (by omega) degree room xk full
    simp only [Nat.reduceAdd] at fl
    have c := capv x xk
    exact mem_filter.mpr ⟨ball_subset xk, by omega⟩
  have cc := class_count_slack (k := 1) (r := r) (c := 2 * r + 1)
    (R := idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)))
    (H := level D V 2 (2 * r + 1)) free (by omega) degree
    (fun y hy => (exact y (mem_filter.mp hy).1).le) (fun y hy => (mem_filter.mp hy).2.le)
    (fun v hv => (root v hv).2.2.1)
    (fun v hv => by
      obtain ⟨_, one, sh, f3, _⟩ := root v hv
      simp only [Nat.reduceAdd]
      omega)
    live high
  simp only [Nat.reduceAdd] at cc
  have cs := class_slack (r := r) free (by omega) Rv (fun v hv => exact v (Rv hv))
  have sup := supplier_cap_slack (j := 3) free (by omega) Sv Tv
  have tsplit : (level D V 2 (2 * r)).card + (level D V 2 (2 * r + 1)).card
      + (above D V 2 (2 * r + 1)).card = V.card :=
    level_split (fun v => (ball D V v 2).card) (2 * r) V floor2
  have Lsplit : (idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).card
      + ((level D V 2 (2 * r)).filter
          (fun v => outN D (above D V 2 (2 * r + 1)) v ≠ ∅)).card
      = (level D V 2 (2 * r)).card := card_filter_add_card_filter_not _
  have lv := levels (fun v => (ball D V v 2).card) (2 * r) 2 V
  rw [sum_range_succ, sum_range_one] at lv
  simp only [add_zero] at lv
  have osplit : (V.filter (fun v => 2 * r < (ball D V v 2).card)).card
      = (level D V 2 (2 * r + 1)).card + (above D V 2 (2 * r + 1)).card :=
    count_split (fun v => (ball D V v 2).card) (2 * r) V
  have ea : (V.filter (fun v => 2 * r + 1 < (ball D V v 2).card)).card
      = (above D V 2 (2 * r + 1)).card := rfl
  have bud := budget free (by omega : 2 + 2 ≤ q) floor2 floor2
  have gsplit := sum_sdiff Rv (f := fun v => (gap D V 2 2 v).card)
  have four : V.card * (2 * r + 2 * r) = V.card * (4 * r) := by ring
  refine ⟨by omega, by omega, by omega⟩

/-- **Strict count regime.** Under the profile law, a host with `s` strict rows, third balls of
`S` summing to at least `s b + k`, and excess at least `x` is impossible whenever
`n(n+1) + 2sn + 2⌊(n(n+1) - 4rn - 4s - 2x) / (2(q+1))⌋ < 2(n + s b + k + s + x) + 4rn`. -/
theorem strict_count_regime {r b n s k x : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hr : 1 ≤ r)
    (exact : ∀ v ∈ V, (outN D V v).card = r) (size : V.card = n)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, b ≤ (ball D V v 3).card) (hb : 3 * r ≤ b + 1)
    (regular : ∀ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card)
    (count : (above D V 2 (2 * r + 1)).card = s)
    (third : s * b + k ≤ ∑ v ∈ above D V 2 (2 * r + 1), (ball D V v 3).card)
    (excess : x ≤ ∑ v ∈ V, ((ball D V v 2).card - (2 * r + 2)))
    (arith : n * (n + 1) + 2 * (s * n)
        + 2 * ((n * (n + 1) - n * (4 * r) - 4 * s - 2 * x) / (2 * (q + 1)))
      < 2 * (n + s * b + k + s + x) + n * (4 * r)) : False := by
  obtain ⟨law, cls, bud⟩ := profile_law free hq hr exact floor2
    (fun v hv => by have := floor3 v (mem_filter.mp hv).1; omega) regular
  rw [size, count] at law bud
  have div : ((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).image
      (fun v => ball D V v 2 \ ball D V v 1)).card
      ≤ (n * (n + 1) - n * (4 * r) - 4 * s - 2 * x) / (2 * (q + 1)) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have : ((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).image
        (fun v => ball D V v 2 \ ball D V v 1)).card * (2 * (q + 1))
        = 2 * ((q + 1) * ((idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r))).image
        (fun v => ball D V v 2 \ ball D V v 1)).card) := by ring
    omega
  omega

/-- The same regime with first-layer regularity supplied by the degree-two quota (`r ≤ 2 q`). -/
theorem strict_count_regime_lower {r b n s k x : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (hr : 1 ≤ r) (exact : ∀ v ∈ V, (outN D V v).card = r) (size : V.card = n)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, b ≤ (ball D V v 3).card) (hb : 3 * r ≤ b + 1)
    (lower : NoHost q 2) (hr2 : r ≤ 2 * q)
    (count : (above D V 2 (2 * r + 1)).card = s)
    (third : s * b + k ≤ ∑ v ∈ above D V 2 (2 * r + 1), (ball D V v 3).card)
    (excess : x ≤ ∑ v ∈ V, ((ball D V v 2).card - (2 * r + 2)))
    (arith : n * (n + 1) + 2 * (s * n)
        + 2 * ((n * (n + 1) - n * (4 * r) - 4 * s - 2 * x) / (2 * (q + 1)))
      < 2 * (n + s * b + k + s + x) + n * (4 * r)) : False := by
  refine strict_count_regime free hq hr exact size floor2 floor3 hb (fun v hv => ?_) count third
    excess arith
  have vv : v ∈ V := (mem_filter.mp (mem_filter.mp hv).1).1
  exact regular_of_lower lower free hr2 hr vv (by rw [ball_one free (by omega) vv, exact v vv])

/-- **Four-diagonal.** On `4 r` labels, with floors `2 r` and `3 r - 1` at radii two and three
and regular first layers, at least two rows sit two above the radius-two floor. -/
theorem four_diagonal {r : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hr : 1 ≤ r)
    (exact : ∀ v ∈ V, (outN D V v).card = r) (size : V.card = 4 * r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, 3 * r ≤ (ball D V v 3).card + 1)
    (regular : ∀ v ∈ idle D (above D V 2 (2 * r + 1)) (level D V 2 (2 * r)),
      ¬ ∀ x ∈ (ball D V v 1).erase v, 2 ≤ (outN D ((ball D V v 1).erase v) x).card) :
    2 ≤ (above D V 2 (2 * r + 1)).card := by
  by_contra! few
  have third : (above D V 2 (2 * r + 1)).card * (3 * r - 1) + 0
      ≤ ∑ v ∈ above D V 2 (2 * r + 1), (ball D V v 3).card := by
    have low : ∑ _v ∈ above D V 2 (2 * r + 1), (3 * r - 1)
        ≤ ∑ v ∈ above D V 2 (2 * r + 1), (ball D V v 3).card :=
      sum_le_sum (fun v hv => by have := floor3 v (mem_filter.mp hv).1; omega)
    rw [sum_const, smul_eq_mul] at low
    omega
  refine strict_count_regime (b := 3 * r - 1) (k := 0) (x := 0) free hq hr exact size floor2
    (fun v hv => by have := floor3 v hv; omega) (by omega) regular rfl third (Nat.zero_le _) ?_
  have e1 : 4 * r * (4 * r + 1) = 4 * r * (4 * r) + 4 * r := by ring
  have hd : (4 * r * (4 * r + 1) - 4 * r * (4 * r) - 4 * (above D V 2 (2 * r + 1)).card - 2 * 0)
      / (2 * (q + 1))
      ≤ (4 * r * (4 * r + 1) - 4 * r * (4 * r) - 4 * (above D V 2 (2 * r + 1)).card - 2 * 0)
      / 10 := Nat.div_le_div_left (by omega) (by omega)
  rcases (show (above D V 2 (2 * r + 1)).card = 0 ∨ (above D V 2 (2 * r + 1)).card = 1 by omega)
    with h | h <;> rw [h] at hd ⊢ <;> omega

/-- Four-diagonal with regularity from the degree-two quota, for `r ≤ 2 q`. -/
theorem four_diagonal_lower {r : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hr : 1 ≤ r)
    (exact : ∀ v ∈ V, (outN D V v).card = r) (size : V.card = 4 * r)
    (floor2 : ∀ v ∈ V, 2 * r ≤ (ball D V v 2).card)
    (floor3 : ∀ v ∈ V, 3 * r ≤ (ball D V v 3).card + 1)
    (lower : NoHost q 2) (hr2 : r ≤ 2 * q) :
    2 ≤ (above D V 2 (2 * r + 1)).card := by
  refine four_diagonal free hq hr exact size floor2 floor3 (fun v hv => ?_)
  have vv : v ∈ V := (mem_filter.mp (mem_filter.mp hv).1).1
  exact regular_of_lower lower free hr2 hr vv (by rw [ball_one free (by omega) vv, exact v vv])

/-! ### Catalog -/

/-- The slack forms that the cutoff alone gives, at every admissible radius. -/
structure Slack (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) : Prop where
  parents : ∀ i v, i + 1 ≤ q → v ∈ V →
    (inN D V v).card + (ball D V v i).card + ((V \ ball D V v i) \ inN D V v).card = V.card
  suppliers : ∀ j (S T : Finset ℕ), j + 1 ≤ q → S ⊆ V → T ⊆ V →
    (T.filter (fun v => outN D S v ≠ ∅)).card + ((V \ T).filter (fun v => outN D S v ≠ ∅)).card
      + (V.filter (fun v => 2 ≤ (outN D S v).card)).card
      + ∑ s ∈ S, ((V \ ball D V s j) \ inN D V s).card + ∑ s ∈ S, (ball D V s j).card
      ≤ S.card * V.card
  levels : ∀ i a m, i + i ≤ q → (∀ v ∈ V, a ≤ (ball D V v i).card) →
    2 * (m * (V.filter (fun v => a + m ≤ (ball D V v i).card)).card)
      + ∑ v ∈ V, (gap D V i i v).card + V.card * (a + a) ≤ V.card * (V.card + 1)

@[aesop safe forward (immediate := [free]) (rule_sets := [CHGraphFamilies])]
theorem slack_packet (free : QFree D V q) : Slack D V q where
  parents := fun _ _ hi vv => parent_slack free hi vv
  suppliers := fun _ _ _ hj sv tv => supplier_cap_slack free hj sv tv
  levels := fun _ _ _ hi floor => level_slack free hi floor

#print axioms slack_packet
#print axioms parent_slack
#print axioms parents_full
#print axioms heading_split
#print axioms supplier_slack
#print axioms supplier_cap_slack
#print axioms suppliers_inside
#print axioms suppliers_single
#print axioms level_slack
#print axioms level_split
#print axioms count_split
#print axioms pair_arith
#print axioms class_row
#print axioms class_slack
#print axioms class_zero
#print axioms gaps_inside
#print axioms class_count_slack
#print axioms regular_of_lower
#print axioms profile_law
#print axioms strict_count_regime
#print axioms strict_count_regime_lower
#print axioms four_diagonal
#print axioms four_diagonal_lower
end LeanCH.BR.StrictPairBanks
