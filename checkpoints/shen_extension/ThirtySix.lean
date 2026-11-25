import checkpoints.shen_extension.HostTwo
import checkpoints.shen_extension.ThinRule
import checkpoints.shen_extension.CollarBound

/-!
# Order 36 at degree nine, cutoff four: the counting, with the local laws as hypotheses

Setting: `QFree D V 4`, every out-degree exactly `9`, `|V| = 36`. Write `w v` for
`(layer D V 2 v).card` (labels at distance exactly two), `T` for the rows with `w ≤ 8` ("tight")
and `H = V \ T` ("high").

Proved here, with no hypothesis beyond the setting:

* `wide7` (F1): `w ≥ 7` everywhere (a root with `w ≤ 6` keeps minimum out-degree three on its
  nine heads, against `FatShort.order_deg`).
* `budget` (F2): `2 ∑ w + ∑ |gap 2 2| = 612`, i.e. `∑ (w - 8) + G = 18` with `G` the unordered
  radius-two gap pairs (`ReachLedger.ledger` at radii `(2, 2)`).
* `ball3_wide`, `ball3_wider`: rows with `w ≥ 9` have `|B 3| ≥ 25`, rows with `w ≥ 10` have
  `|B 3| ≥ 26` (the reach climb `ShapeClimbAvoid.layersA` for the patterns `thinA 9`,
  `thinA 10`, kernel-checked). Hence in-degree `≤ 11`, resp. `≤ 10` (`indeg_wide`,
  `indeg_wider`).
* `high_count` (step (b)): with Law A, `|H| ≥ 16`. Only in-degree `≤ 11` on `H` is used
  (`8 |T| ≤ 11 |H|`), so the Floor is not needed here.
* `no_seven` (step (c)): with Law A, no row has `w = 7`. Classes of such roots by head set:
  `∑_x (18 [p x > 0] + p x (p x - 1)) ≤ 36 + 2 ∑ p x` with `p x` the number of such roots
  heading `x`, against `p (p - 1) ≥ 2 p - 2 [p > 0]`.
* `residual` (step (d) and most of (e)): with Law A and L2, the only survivor has `|H| = 16`,
  no gap pair at all, exactly two rows `z` with `w ≥ 10` (both `w = 10`), and every tight row
  heading exactly one of them. Uses `indeg ≤ 10` at `w ≥ 10` (proved), not the Floor.

Closing the residual:

* **`no36`** (Law A and L2 only, no Floor): in the residual each `z` has exactly ten parents,
  all tight; they lie in the reverse two-ball of `z`, which has `16` other labels (no gaps);
  a tight label sends at most one arc to tight labels (Law A), so those ten rows have total
  in-degree `≤ 10 + 6 · 9 = 64` (`parent_indeg`) and `T` has total in-degree `≤ 128`. But
  the high rows send at least `144 - (14 · 11 - 20 · 7) = 130` arcs into `T`.
* `no36_floor`: the candidate's step (e), kept for reference: with the Floor (in-degree `≤ 10`
  on every row with `w ≥ 9`), equality in `160 = 8 |T| ≤ (arcs into H) ≤ 160` and a digon.

`no36_min`, `no36_floor_min`: the same for minimum out-degree nine
(`CollarBound.exists_regular`), the laws quantified over all regular `4`-free digraphs on `V`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ThirtySix
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)
open HostTwo (inN)

/-! ### The hypotheses -/

/-- **Law A** at `(r, q) = (9, 4)`: a row with second layer `8` has at most one head with second
layer `≤ 8`. -/
def LawA (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ u ∈ V, (layer D V 2 u).card + 1 = 9 →
    ((outN D V u).filter (fun x => (layer D V 2 x).card + 1 ≤ 9)).card ≤ 1

/-- Ordered radius-two gap pairs among the heads of `u` (twice the unordered count). -/
noncomputable def headGaps (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : ℕ :=
  ∑ x ∈ outN D V u, (gap D V 2 2 x ∩ outN D V u).card

/-- **Head laws.** No row with second layer `8` whose heads all have second layer `≤ c`, at most
`k` of them `≥ 10`, and at most `g` ordered gap pairs among them.
`HeadLaw D V 9 0 4` is **L2** (at most two unordered gap pairs, all heads `≤ 9`);
(`HeadLaw D V 10 1 0` was a candidate for closing the residual; it is not needed.) -/
def HeadLaw (D : CH.Digraph) (V : Finset ℕ) (c k g : ℕ) : Prop :=
  ∀ u ∈ V, (layer D V 2 u).card + 1 = 9 → (∀ x ∈ outN D V u, (layer D V 2 x).card ≤ c) →
    ((outN D V u).filter (fun x => 10 ≤ (layer D V 2 x).card)).card ≤ k →
    headGaps D V u ≤ g → False

/-- **The Floor**: every row with second layer `≥ 9` has in-degree at most `10`. -/
def Floor10 (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ v ∈ V, 9 ≤ (layer D V 2 v).card → (inN D V v).card ≤ 10

/-! ### The reach floors (kernel-checked climb) -/

section floors
open BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer RecursivePrefixBudget
open ShapeClimbAt (library_bankAt)

/-- Floors of the roots with second layer `≥ t` at `(q, r) = (4, 9)`, radii `0 … 3`. -/
def wideFloors (t : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersA (ShapeClimbAvoid.thinA t) (FatShort.fatShortGX 4 9) 4 9
    (library 4 (ThinRule.bankDegree 9)) (ThinRule.floorsH 4 9) 2

def wideFloorsF (t : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersAF (ShapeClimbAvoid.thinA t) (FatShort.fatShortGX 4 9) 4 9
    (library 4 (ThinRule.bankDegree 9)) (ThinRule.floorsHF 4 9) 2

theorem wideFloorsF_eq (t : ℕ) : wideFloorsF t = wideFloors t := by
  simp only [wideFloorsF, wideFloors, ShapeClimbAvoid.layersAF_eq, ThinRule.floorsHF_eq]

theorem wideFloors_sound (t i : ℕ) :
    ShapeClimbAvoid.AvoidFloor 4 9 (ShapeClimbAvoid.thinA t) i ((wideFloors t).getD i 0) := by
  have pf : 0 < projectionFloor := Nat.succ_pos _
  have known : ∀ q' t, t ≤ ThinRule.bankDegree 9 → NoHost q' t := fun q' t ht =>
    ShapeClimbMono.lower_hosts_every q' t (by
      have := ht.trans (min_le_right (9 - 1) (projectionFloor - 1))
      omega)
  have cr : ThinRule.bankDegree 9 < 9 := lt_of_le_of_lt (min_le_left ..) (by omega)
  have bank := library_bankAt (r := 9) (by omega : 2 ≤ 4) cr (known 4)
  have seeds := ShapeClimbMono.seedAt_sound (q := 4) (K := 4 - 4/2) cr known
  have floors : ∀ i, Floor 4 9 i ((ThinRule.floorsH 4 9).getD i 0) :=
    (ShapeClimbX.layersX_sound (FatShort.fatShortGX_sound 4 9) (by omega) bank seeds
      (4 - 4/2) (by omega)).2
  exact (ShapeClimbAvoid.layersA_sound (FatShort.fatShortGX_sound 4 9) (by omega) bank floors
    2 (by omega)).2 i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floor25F : 25 ≤ (wideFloorsF 9).getD 3 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floor26F : 26 ≤ (wideFloorsF 10).getD 3 0 := by decide +kernel

end floors

variable {D : CH.Digraph} {V : Finset ℕ}

/-- A row with second layer `≥ 9` has at least `25` labels within three steps. -/
theorem ball3_wide (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (h : 9 ≤ (layer D V 2 u).card) : 25 ≤ (ball D V u 3).card := by
  have f := floor25F
  rw [wideFloorsF_eq] at f
  exact f.trans (wideFloors_sound 9 3 D V free reg u hu (ShapeClimbAvoid.fat_avoids_thin h))

/-- A row with second layer `≥ 10` has at least `26` labels within three steps. -/
theorem ball3_wider (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (h : 10 ≤ (layer D V 2 u).card) : 26 ≤ (ball D V u 3).card := by
  have f := floor26F
  rw [wideFloorsF_eq] at f
  exact f.trans (wideFloors_sound 10 3 D V free reg u hu (ShapeClimbAvoid.fat_avoids_thin h))

theorem indeg_wide (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) {u : ℕ} (hu : u ∈ V) (h : 9 ≤ (layer D V 2 u).card) :
    (inN D V u).card ≤ 11 := by
  have := HostTwo.indeg_ball free (by norm_num) hu (j := 3) (by norm_num)
  have := ball3_wide free reg hu h
  omega

theorem indeg_wider (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) {u : ℕ} (hu : u ∈ V) (h : 10 ≤ (layer D V 2 u).card) :
    (inN D V u).card ≤ 10 := by
  have := HostTwo.indeg_ball free (by norm_num) hu (j := 3) (by norm_num)
  have := ball3_wider free reg hu h
  omega

/-! ### (F1), (F2), (F3) -/

/-- **(F1)** Every second layer has at least `7` labels. -/
theorem wide7 (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) : 7 ≤ (layer D V 2 u).card := by
  by_contra h
  push Not at h
  have inner := DipCost.layer_host (X := outN D V u) (Y := layer D V 2 u) (c := 3)
    (fun x hx => (reg x (outN_subset hx)).ge) (head_keep free (by norm_num) hu) (by omega)
  obtain ⟨x, hx⟩ : (outN D V u).Nonempty := card_pos.mp (by rw [reg u hu]; omega)
  have := FatShort.order_deg (free.mono_set (outN_subset (D := D) (W := V) (y := u)))
    (by norm_num) 3 (by norm_num) inner ⟨x, hx⟩
  rw [reg u hu] at this
  omega

theorem ball2_card (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) : (ball D V u 2).card = (layer D V 2 u).card + 10 :=
  (ThinSuppliers.balls_by_layers free (by norm_num) reg hu).2.1

/-- **(F2) The pair budget.** `2 ∑ w + ∑ |gap| = 612`. -/
theorem budget (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 36) :
    2 * ∑ v ∈ V, (layer D V 2 v).card + ∑ v ∈ V, (gap D V 2 2 v).card = 612 := by
  have L := ReachLedger.ledger (D := D) (V := V) (i := 2) (j := 2) free (by norm_num)
  have e : ∑ v ∈ V, (ball D V v 2).card = ∑ v ∈ V, (layer D V 2 v).card + V.card * 10 := by
    rw [sum_congr rfl (fun v hv => ball2_card free reg hv), sum_add_distrib, sum_const,
      smul_eq_mul]
  rw [e, n] at L
  omega

/-- **(F3)** The heads of a row with second layer `7` have second layer `≥ 10`. -/
theorem seven_heads (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (h7 : (layer D V 2 u).card ≤ 7) {x : ℕ} (hx : x ∈ outN D V u) :
    10 ≤ (layer D V 2 x).card := by
  have fat := HostTwo.two_head_fat (r := 9) free (by norm_num) hu (fun v hv => (reg v hv).ge)
    (by rw [reg u hu]) (by omega) (by norm_num) (by norm_num) hx
  have := ball2_card free reg (outN_subset hx)
  omega

/-- Two rows with second layer `7` heading a common label are mutual gaps. -/
theorem seven_twins (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u u' x : ℕ}
    (hu : u ∈ V) (hu' : u' ∈ V) (h7 : (layer D V 2 u).card ≤ 7) (h7' : (layer D V 2 u').card ≤ 7)
    (ne : u ≠ u') (hx : D u x = true) (hx' : D u' x = true) (xV : x ∈ V) :
    u' ∈ gap D V 2 2 u := by
  have eq := (HostTwo.banks_equal (q := 4) (r := 9) free (by norm_num) hu hu'
    (by rw [reg u hu]) (by rw [reg u' hu']) (fun y hy => (reg y (outN_subset hy)).ge)
    (fun y hy => (reg y (outN_subset hy)).ge) (by omega) (by omega)
    (mem_outN.mpr ⟨xV, hx⟩) (mem_outN.mpr ⟨xV, hx'⟩)).2
  exact CollarLedger.twin_gap free hu hu' ne eq (by norm_num) (by norm_num)

/-! ### Step (b): at least sixteen high rows -/

theorem supply (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) (lawA : LawA D V)
    {u : ℕ} (hu : u ∈ V) (ht : (layer D V 2 u).card ≤ 8) :
    8 ≤ ((V \ V.filter (fun v => (layer D V 2 v).card ≤ 8)).filter (fun v => D u v = true)).card := by
  have sub : (outN D V u).filter (fun x => ¬ ((layer D V 2 x).card + 1 ≤ 9)) ⊆
      (V \ V.filter (fun v => (layer D V 2 v).card ≤ 8)).filter (fun v => D u v = true) := by
    intro x hx
    obtain ⟨xo, xw⟩ := mem_filter.mp hx
    obtain ⟨xV, ux⟩ := mem_outN.mp xo
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨xV, fun h => xw (by have := (mem_filter.mp h).2; omega)⟩, ux⟩
  have split := card_filter_add_card_filter_not (s := outN D V u)
    (fun x => (layer D V 2 x).card + 1 ≤ 9)
  rw [reg u hu] at split
  have c := card_le_card sub
  have w7 := wide7 free reg hu
  rcases (show (layer D V 2 u).card = 7 ∨ (layer D V 2 u).card + 1 = 9 by omega) with e | e
  · have empty : (outN D V u).filter (fun x => (layer D V 2 x).card + 1 ≤ 9) = ∅ := by
      refine filter_eq_empty_iff.mpr (fun x hx => ?_)
      have := seven_heads free reg hu (by omega) hx
      omega
    rw [empty, card_empty] at split
    omega
  · have := lawA u hu e
    omega

/-- **Step (b).** Law A gives at least `16` rows with second layer `≥ 9`. -/
theorem high_count (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) (lawA : LawA D V) :
    16 ≤ (V \ V.filter (fun v => (layer D V 2 v).card ≤ 8)).card := by
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  have count := HostTwo.supplier_count (D := D) (V := V) (T := T) (a := 8) (c := 11)
    (filter_subset _ _) (fun u hu => supply free reg lawA (mem_filter.mp hu).1 (mem_filter.mp hu).2)
    (fun v hv => by
      obtain ⟨vV, vT⟩ := mem_sdiff.mp hv
      exact indeg_wide free reg n vV (by
        by_contra h
        exact vT (mem_filter.mpr ⟨vV, by omega⟩)))
  have parts := card_sdiff_add_card_eq_card (filter_subset (fun v => (layer D V 2 v).card ≤ 8) V)
  rw [← hT] at parts
  omega

/-! ### Step (c): no second layer of seven -/

/-- Per row: the second-layer sum against the floors `16`, `18` and the bank indicator. -/
theorem row_lower {a t : ℕ} (h7 : 7 ≤ a) (bt : t = 1 → 10 ≤ a) (tb : t ≤ 1) :
    16 + 2 * (if 9 ≤ a then 1 else 0) + 2 * t ≤ 2 * a + 2 * (if a = 7 then 1 else 0) := by
  rcases Nat.lt_or_ge a 10 with h | h
  · have : t = 0 := by
      rcases (show t = 0 ∨ t = 1 by omega) with e | e
      · exact e
      · have := bt e; omega
    subst this
    split_ifs <;> omega
  · split_ifs <;> omega

theorem pair_lower (p : ℕ) :
    2 * p + 16 * (if 0 < p then 1 else 0) ≤ 18 * (if 0 < p then 1 else 0) + p * (p - 1) := by
  rcases Nat.lt_or_ge p 3 with h | h
  · interval_cases p <;> simp
  · have : 2 * p ≤ p * (p - 1) := by
      have : 2 ≤ p - 1 := by omega
      calc 2 * p = p * 2 := by ring
        _ ≤ p * (p - 1) := Nat.mul_le_mul_left p this
    split_ifs <;> omega

/-- **Step (c).** With Law A, no row has second layer `7`. -/
theorem no_seven (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) (lawA : LawA D V) : ∀ u ∈ V, 8 ≤ (layer D V 2 u).card := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨u0, hu0, h0⟩ := hne
  set R := V.filter (fun v => (layer D V 2 v).card = 7) with hR
  have u0R : u0 ∈ R := mem_filter.mpr ⟨hu0, by have := wide7 free reg hu0; omega⟩
  set P : ℕ → Finset ℕ := fun x => R.filter (fun u => D u x = true) with hP
  set t : ℕ → ℕ := fun x => if 0 < (P x).card then 1 else 0 with ht
  set g : ℕ → ℕ := fun v => (gap D V 2 2 v).card with hg
  have RV : R ⊆ V := filter_subset _ _
  -- a banked label is fat
  have tfat : ∀ x ∈ V, t x = 1 → 10 ≤ (layer D V 2 x).card := by
    intro x xV tx
    have pos : 0 < (P x).card := by
      by_contra h
      simp only [ht, h, ite_false] at tx
      omega
    obtain ⟨u, hu⟩ := card_pos.mp pos
    obtain ⟨uR, ux⟩ := mem_filter.mp hu
    obtain ⟨uV, u7⟩ := mem_filter.mp uR
    exact seven_heads free reg uV (by omega) (mem_outN.mpr ⟨xV, ux⟩)
  -- (A) the second-layer sum
  have A : ∑ v ∈ V, (16 + 2 * (if 9 ≤ (layer D V 2 v).card then 1 else 0) + 2 * t v) ≤
      ∑ v ∈ V, (2 * (layer D V 2 v).card + 2 * (if (layer D V 2 v).card = 7 then 1 else 0)) :=
    sum_le_sum (fun v hv => row_lower (wide7 free reg hv) (tfat v hv)
      (by simp only [ht]; split_ifs <;> omega))
  simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum] at A
  have cH : ∑ v ∈ V, (if 9 ≤ (layer D V 2 v).card then 1 else 0) =
      (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card := by
    rw [card_filter]
  have cR : ∑ v ∈ V, (if (layer D V 2 v).card = 7 then 1 else 0) = R.card := by
    rw [hR, card_filter]
  have Hc : (V \ V.filter (fun v => (layer D V 2 v).card ≤ 8)) =
      V.filter (fun v => 9 ≤ (layer D V 2 v).card) := by
    ext v
    simp only [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨vV, h⟩
      exact ⟨vV, by by_contra h'; exact h ⟨vV, by omega⟩⟩
    · rintro ⟨vV, h⟩
      exact ⟨vV, fun ⟨_, h'⟩ => by omega⟩
  have high := high_count free reg n lawA
  rw [Hc] at high
  rw [cH, cR, n] at A
  have bud := budget free reg n
  -- (B) gaps of the sevens
  have B : ∑ u ∈ R, g u ≤ ∑ v ∈ V, g v := sum_le_sum_of_subset RV
  -- (C) twins are gaps
  have perx : ∀ x ∈ V, (P x).card * ((P x).card - 1) ≤ ∑ u ∈ P x, g u := by
    intro x xV
    have each : ∀ u ∈ P x, (P x).card - 1 ≤ g u := by
      intro u hu
      have sub : (P x).erase u ⊆ gap D V 2 2 u := by
        intro u' hu'
        obtain ⟨ne, hu'P⟩ := mem_erase.mp hu'
        obtain ⟨u'R, u'x⟩ := mem_filter.mp hu'P
        obtain ⟨uR, ux⟩ := mem_filter.mp hu
        obtain ⟨uV, u7⟩ := mem_filter.mp uR
        obtain ⟨u'V, u'7⟩ := mem_filter.mp u'R
        exact seven_twins free reg uV u'V (by omega) (by omega) (Ne.symm ne) ux u'x xV
      have := card_le_card sub
      rw [card_erase_of_mem hu] at this
      exact this
    have := sum_le_sum each
    rw [sum_const, smul_eq_mul] at this
    exact this
  have swap : ∑ x ∈ V, ∑ u ∈ P x, g u = ∑ u ∈ R, 9 * g u := by
    simp only [hP, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun u uR => ?_)
    rw [← sum_filter]
    have : V.filter (fun x => D u x = true) = outN D V u := rfl
    rw [this, sum_const, reg u (RV uR), smul_eq_mul]
  have C : ∑ x ∈ V, (P x).card * ((P x).card - 1) ≤ 9 * ∑ u ∈ R, g u := by
    rw [mul_sum, ← swap]
    exact sum_le_sum perx
  -- (D) the arcs out of the sevens
  have Dd : ∑ x ∈ V, (P x).card = 9 * R.card := by
    have := HostTwo.arcs_between (D := D) R V
    rw [← this]
    rw [sum_congr rfl (fun u uR => by
      have : V.filter (fun x => D u x = true) = outN D V u := rfl
      rw [this, reg u (RV uR)])]
    rw [sum_const, smul_eq_mul, mul_comm]
  -- (E) per label
  have E : ∑ x ∈ V, (2 * (P x).card + 16 * t x) ≤ ∑ x ∈ V, (18 * t x + (P x).card * ((P x).card - 1)) :=
    sum_le_sum (fun x _ => pair_lower (P x).card)
  simp only [sum_add_distrib, ← mul_sum] at E
  -- (F) the banks of `u0` are nine labels
  have F : 9 ≤ ∑ x ∈ V, t x := by
    have sub := sum_le_sum_of_subset (f := t) (outN_subset (D := D) (W := V) (y := u0))
    have one : ∑ x ∈ outN D V u0, t x = 9 := by
      rw [sum_congr rfl (fun x hx => (show t x = 1 by
        have : 0 < (P x).card := card_pos.mpr ⟨u0, mem_filter.mpr ⟨u0R, (mem_outN.mp hx).2⟩⟩
        simp only [ht, this, ite_true])), sum_const, smul_eq_mul, mul_one, reg u0 hu0]
    omega
  have g0 : ∑ v ∈ V, g v = ∑ v ∈ V, (gap D V 2 2 v).card := rfl
  omega

/-! ### Steps (d) and (e): the residual configuration -/

/-- The gap mass among heads is at most the total gap mass. -/
theorem headGaps_le {u : ℕ} :
    headGaps D V u ≤ ∑ v ∈ V, (gap D V 2 2 v).card := by
  unfold headGaps
  calc ∑ x ∈ outN D V u, (gap D V 2 2 x ∩ outN D V u).card
      ≤ ∑ x ∈ outN D V u, (gap D V 2 2 x).card :=
        sum_le_sum (fun x _ => card_le_card inter_subset_left)
    _ ≤ ∑ v ∈ V, (gap D V 2 2 v).card := sum_le_sum_of_subset outN_subset

/-- The budget once every row has second layer `≥ 8`: `2 |H| + 2 ∑ (w - 9) + ∑ |gap| ≤ 36`. -/
theorem budget8 (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 36)
    (eight : ∀ u ∈ V, 8 ≤ (layer D V 2 u).card) :
    2 * (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card +
      2 * ∑ v ∈ V, ((layer D V 2 v).card - 9) + ∑ v ∈ V, (gap D V 2 2 v).card ≤ 36 := by
  have A : ∑ v ∈ V, (16 + 2 * (if 9 ≤ (layer D V 2 v).card then 1 else 0) +
      2 * ((layer D V 2 v).card - 9)) ≤ ∑ v ∈ V, 2 * (layer D V 2 v).card :=
    sum_le_sum (fun v hv => by have := eight v hv; split_ifs <;> omega)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum] at A
  rw [← card_filter, n] at A
  have := budget free reg n
  omega

theorem high_eq (V : Finset ℕ) (D : CH.Digraph) :
    (V \ V.filter (fun v => (layer D V 2 v).card ≤ 8)) =
      V.filter (fun v => 9 ≤ (layer D V 2 v).card) := by
  ext v
  simp only [mem_sdiff, mem_filter]
  constructor
  · rintro ⟨vV, h⟩
    exact ⟨vV, by by_contra h'; exact h ⟨vV, by omega⟩⟩
  · rintro ⟨vV, h⟩
    exact ⟨vV, fun ⟨_, h'⟩ => by omega⟩

/-- **The residual.** With Law A and L2 (`HeadLaw D V 9 0 4`): `|H| = 16`, no gap pair at all,
every row with second layer `≥ 9` has second layer `9` or `10`, exactly two have `10`, and every
row with second layer `8` heads exactly one of those two. -/
theorem residual (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) (lawA : LawA D V) (l2 : HeadLaw D V 9 0 4) :
    (∀ u ∈ V, 8 ≤ (layer D V 2 u).card) ∧
    (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card = 16 ∧
    ∑ v ∈ V, (gap D V 2 2 v).card = 0 ∧
    (∀ v ∈ V, (layer D V 2 v).card ≤ 10) ∧
    (V.filter (fun v => 10 ≤ (layer D V 2 v).card)).card = 2 ∧
    (∀ u ∈ V, (layer D V 2 u).card ≤ 8 →
      ((outN D V u).filter (fun x => 10 ≤ (layer D V 2 x).card)).card = 1) := by
  classical
  have eight := no_seven free reg n lawA
  have high := high_count free reg n lawA
  rw [high_eq] at high
  have b8 := budget8 free reg n eight
  have Tc : (V.filter (fun v => (layer D V 2 v).card ≤ 8)).card +
      (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card = 36 := by
    have := card_sdiff_add_card_eq_card (filter_subset (fun v => (layer D V 2 v).card ≤ 8) V)
    rw [high_eq, n] at this
    omega
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  set Z := V.filter (fun v => 10 ≤ (layer D V 2 v).card) with hZ
  -- every tight row heads a row of `Z`
  have hit : ∀ u ∈ T, 1 ≤ (Z.filter (fun z => D u z = true)).card := by
    intro u hu
    obtain ⟨uV, u8⟩ := mem_filter.mp hu
    by_contra none
    push Not at none
    have empty : Z.filter (fun z => D u z = true) = ∅ := card_eq_zero.mp (by omega)
    refine l2 u uV (by have := eight u uV; omega) (fun x hx => ?_) ?_ ?_
    · by_contra big
      push Not at big
      have : x ∈ Z.filter (fun z => D u z = true) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨outN_subset hx, by omega⟩, (mem_outN.mp hx).2⟩
      rw [empty] at this
      simp at this
    · refine le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun x hx h => ?_)))
      have : x ∈ Z.filter (fun z => D u z = true) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨outN_subset hx, h⟩, (mem_outN.mp hx).2⟩
      rw [empty] at this
      simp at this
    · have := headGaps_le (D := D) (V := V) (u := u)
      omega
  -- count the arcs from `T` to `Z`
  have arcs := HostTwo.arcs_between (D := D) T Z
  have lowT : T.card ≤ ∑ u ∈ T, (Z.filter (fun z => D u z = true)).card := by
    have := sum_le_sum hit
    simpa using this
  have capZ : ∑ z ∈ Z, (T.filter (fun u => D u z = true)).card ≤ ∑ _z ∈ Z, 10 := by
    refine sum_le_sum (fun z hz => ?_)
    obtain ⟨zV, zw⟩ := mem_filter.mp hz
    refine le_trans (card_le_card (fun u hu => ?_)) (indeg_wider free reg n zV zw)
    obtain ⟨uT, uz⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨(mem_filter.mp uT).1, uz⟩
  rw [sum_const, smul_eq_mul] at capZ
  -- `|Z| ≤ ∑ (w - 9)`
  have Zle : Z.card ≤ ∑ v ∈ V, ((layer D V 2 v).card - 9) := by
    rw [hZ, card_filter]
    exact sum_le_sum (fun v _ => by split_ifs <;> omega)
  have Z2 : Z.card = 2 := by omega
  have H16 : (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card = 16 := by omega
  have excess : ∑ v ∈ V, ((layer D V 2 v).card - 9) = 2 := by omega
  have g0 : ∑ v ∈ V, (gap D V 2 2 v).card = 0 := by omega
  -- each row of `Z` has second layer exactly `10`, every other row at most `9`
  have Zsum : ∑ v ∈ V, ((layer D V 2 v).card - 9) =
      ∑ v ∈ V, (if 10 ≤ (layer D V 2 v).card then 1 else 0) +
        ∑ v ∈ V, ((layer D V 2 v).card - 10) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun v _ => by split_ifs <;> omega)
  rw [← card_filter, ← hZ, Z2, excess] at Zsum
  have top : ∀ v ∈ V, (layer D V 2 v).card ≤ 10 := by
    intro v hv
    by_contra h
    have : (layer D V 2 v).card - 10 ≤ ∑ v ∈ V, ((layer D V 2 v).card - 10) :=
      single_le_sum (f := fun v => (layer D V 2 v).card - 10) (fun _ _ => Nat.zero_le _) hv
    omega
  refine ⟨eight, H16, g0, top, Z2, fun u uV u8 => ?_⟩
  have uT : u ∈ T := mem_filter.mpr ⟨uV, u8⟩
  -- every tight row heads exactly one row of `Z`
  have each : ∀ u ∈ T, (Z.filter (fun z => D u z = true)).card = 1 := by
    by_contra bad
    push Not at bad
    obtain ⟨u', u'T, ne⟩ := bad
    have gt : ∑ u ∈ T, 1 < ∑ u ∈ T, (Z.filter (fun z => D u z = true)).card :=
      sum_lt_sum hit ⟨u', u'T, by have := hit u' u'T; omega⟩
    simp only [sum_const, smul_eq_mul, mul_one] at gt
    omega
  have := each u uT
  have eqf : (outN D V u).filter (fun x => 10 ≤ (layer D V 2 x).card) =
      Z.filter (fun z => D u z = true) := by
    ext x
    simp only [mem_filter, mem_outN, hZ]
    tauto
  rw [eqf]
  exact this

/-! ### Closing the residual -/

/-- **Order 36 with the Floor.** Law A, L2 and the Floor exclude a `4`-free out-regular digraph of
degree nine on `36` labels. -/
theorem no36_floor (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) (lawA : LawA D V) (l2 : HeadLaw D V 9 0 4) (floor : Floor10 D V) :
    False := by
  classical
  obtain ⟨eight, H16, -, -, -, -⟩ := residual free reg n lawA l2
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  set H := V \ T with hH
  have Hc : H.card = 16 := by rw [hH, hT, high_eq]; exact H16
  have Tc : T.card = 20 := by
    have := card_sdiff_add_card_eq_card (filter_subset (fun v => (layer D V 2 v).card ≤ 8) V)
    rw [← hT, ← hH] at this
    omega
  have memH : ∀ v, v ∈ H ↔ v ∈ V ∧ 9 ≤ (layer D V 2 v).card := by
    intro v
    rw [hH, hT, high_eq, mem_filter]
  have memT : ∀ v, v ∈ T ↔ v ∈ V ∧ (layer D V 2 v).card ≤ 8 := fun v => mem_filter
  have sup : ∀ t ∈ T, 8 ≤ (H.filter (fun v => D t v = true)).card :=
    fun t ht => supply free reg lawA (mem_filter.mp ht).1 (mem_filter.mp ht).2
  have arcs := HostTwo.arcs_between (D := D) T H
  have parent : ∀ h ∈ H, (T.filter (fun u => D u h = true)).card ≤ (inN D V h).card := by
    intro h hh
    refine card_le_card (fun u hu => ?_)
    obtain ⟨uT, uh⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨(memT u).mp uT |>.1, uh⟩
  have cap : ∀ h ∈ H, (inN D V h).card ≤ 10 := fun h hh => floor h ((memH h).mp hh).1 ((memH h).mp hh).2
  have upper : ∑ h ∈ H, (T.filter (fun u => D u h = true)).card ≤ 160 := by
    have := sum_le_sum (fun h hh => (parent h hh).trans (cap h hh))
    rw [sum_const, smul_eq_mul, Hc] at this
    exact this
  -- (α) every tight row has exactly eight high heads
  have alpha : ∀ t ∈ T, (H.filter (fun v => D t v = true)).card = 8 := by
    by_contra bad
    push Not at bad
    obtain ⟨t, ht, ne⟩ := bad
    have gt : ∑ _t ∈ T, 8 < ∑ t ∈ T, (H.filter (fun v => D t v = true)).card :=
      sum_lt_sum sup ⟨t, ht, by have := sup t ht; omega⟩
    rw [sum_const, smul_eq_mul, Tc] at gt
    omega
  -- (β) no arc inside `H`
  have beta : ∀ h ∈ H, ∀ h' ∈ H, ¬ D h' h = true := by
    intro h hh h' hh' arc
    have strict : (T.filter (fun u => D u h = true)).card < (inN D V h).card := by
      refine card_lt_card ⟨fun u hu => ?_, fun sub => ?_⟩
      · obtain ⟨uT, uh⟩ := mem_filter.mp hu
        exact mem_filter.mpr ⟨(memT u).mp uT |>.1, uh⟩
      · have := sub (mem_filter.mpr ⟨((memH h').mp hh').1, arc⟩ : h' ∈ inN D V h)
        have h'T := (mem_filter.mp this).1
        exact (mem_sdiff.mp hh').2 h'T
    have lt : ∑ h ∈ H, (T.filter (fun u => D u h = true)).card < ∑ _h ∈ H, 10 :=
      sum_lt_sum (fun h hh => (parent h hh).trans (cap h hh))
        ⟨h, hh, lt_of_lt_of_le strict (cap h hh)⟩
    rw [sum_const, smul_eq_mul, Hc] at lt
    have := sum_le_sum sup
    rw [sum_const, smul_eq_mul, Tc] at this
    omega
  -- a tight row `t`, its eight high heads `P` and its tight head `t'`
  obtain ⟨t, ht⟩ : T.Nonempty := card_pos.mp (by omega)
  obtain ⟨tV, t8⟩ := (memT t).mp ht
  have t8' : (layer D V 2 t).card = 8 := le_antisymm t8 (eight t tV)
  set P := H.filter (fun v => D t v = true) with hPdef
  have Pc : P.card = 8 := alpha t ht
  have Pout : P ⊆ outN D V t := fun v hv =>
    mem_outN.mpr ⟨((memH v).mp (mem_filter.mp hv).1).1, (mem_filter.mp hv).2⟩
  -- the tight heads of `t`: exactly one
  have tightOut : ((outN D V t).filter (fun v => v ∈ T)).card = 1 := by
    have split := card_filter_add_card_filter_not (s := outN D V t) (fun v => v ∈ T)
    have eqP : (outN D V t).filter (fun v => ¬ v ∈ T) = P := by
      ext v
      simp only [mem_filter, mem_outN, hPdef, hH, mem_sdiff]
      tauto
    rw [eqP, Pc, reg t tV] at split
    omega
  obtain ⟨t', ht'⟩ := card_eq_one.mp tightOut
  have t'mem : t' ∈ (outN D V t).filter (fun v => v ∈ T) := by rw [ht']; exact mem_singleton_self _
  obtain ⟨t'out, t'T⟩ := mem_filter.mp t'mem
  have onlyT : ∀ v ∈ outN D V t, v ∈ T → v = t' := by
    intro v hv vT
    have : v ∈ (outN D V t).filter (fun v => v ∈ T) := mem_filter.mpr ⟨hv, vT⟩
    rw [ht'] at this
    exact mem_singleton.mp this
  obtain ⟨p, hp⟩ : P.Nonempty := card_pos.mp (by omega)
  have pH : p ∈ H := (mem_filter.mp hp).1
  have pV : p ∈ V := ((memH p).mp pH).1
  have tp : D t p = true := (mem_filter.mp hp).2
  -- the heads of `p` are tight and avoid `t`
  have pOutT : ∀ x ∈ outN D V p, x ∈ T := by
    intro x hx
    by_contra xT
    exact beta x (mem_sdiff.mpr ⟨(mem_outN.mp hx).1, xT⟩) p pH (mem_outN.mp hx).2
  have notT : t ∉ outN D V p := fun h =>
    digonfree free (by norm_num) tV pV tp (mem_outN.mp h).2
  -- labels two steps from `t` outside its 1-ball
  have inLayer : ∀ x ∈ V, (∃ y ∈ outN D V t, D y x = true) → x ≠ t → x ∉ outN D V t →
      x ∈ layer D V 2 t := by
    intro x xV ⟨y, hy, yx⟩ xt xo
    refine mem_layer.mpr ⟨ball_step (mem_ball_one_of_out hy) xV yx, fun h => ?_⟩
    rcases (mem_ball_one tV).mp h with e | e
    · exact xt e
    · exact xo e
  have pLayer : ∀ x ∈ outN D V p, x ≠ t' → x ∈ layer D V 2 t := by
    intro x hx xt'
    refine inLayer x (mem_outN.mp hx).1 ⟨p, Pout hp, (mem_outN.mp hx).2⟩
      (fun e => notT (e ▸ hx)) (fun xo => xt' (onlyT x xo (pOutT x hx)))
  -- `p` heads `t'`
  have pt' : D p t' = true := by
    by_contra no
    have sub : outN D V p ⊆ layer D V 2 t := fun x hx =>
      pLayer x hx (fun e => no (e ▸ (mem_outN.mp hx).2))
    have := card_le_card sub
    rw [reg p pV] at this
    omega
  have t'p : outN D V p \ {t'} ⊆ layer D V 2 t := fun x hx =>
    pLayer x (mem_sdiff.mp hx).1 (fun e => (mem_sdiff.mp hx).2 (mem_singleton.mpr e))
  have t'in : t' ∈ outN D V p := mem_outN.mpr ⟨(mem_outN.mp t'out).1, pt'⟩
  have c8 : (outN D V p \ {t'}).card = 8 := by
    rw [card_sdiff_of_subset (singleton_subset_iff.mpr t'in), reg p pV, card_singleton]
  have full : outN D V p \ {t'} = layer D V 2 t :=
    eq_of_subset_of_card_le t'p (by omega)
  -- the high heads of `t'` lie in `P`
  have t'V : t' ∈ V := (mem_outN.mp t'out).1
  have t'T' := (memT t').mp t'T
  have intoP : H.filter (fun v => D t' v = true) ⊆ P := by
    intro h hh
    obtain ⟨hH', t'h⟩ := mem_filter.mp hh
    by_contra hP
    have hV := ((memH h).mp hH').1
    have hl : h ∈ layer D V 2 t := inLayer h hV ⟨t', t'out, t'h⟩
      (fun e => (mem_sdiff.mp hH').2 (e ▸ ht))
      (fun ho => hP (mem_filter.mpr ⟨hH', (mem_outN.mp ho).2⟩))
    rw [← full] at hl
    exact (mem_sdiff.mp hH').2 (pOutT h (mem_sdiff.mp hl).1)
  have eqP : H.filter (fun v => D t' v = true) = P :=
    eq_of_subset_of_card_le intoP (by rw [alpha t' t'T, Pc])
  have pin : p ∈ H.filter (fun v => D t' v = true) := by rw [eqP]; exact hp
  have t'p' : D t' p = true := (mem_filter.mp pin).2
  exact digonfree free (by norm_num) pV t'V pt' t'p'

/-- The tight parents of a row of `Z` in the residual: they lie in its reverse two-ball, which
has `16` other labels; a tight label sends at most one arc into them (Law A), any other at most
nine. So the rows of `T` heading `z` have total in-degree at most `10 + 6 · 9 = 64`. -/
theorem parent_indeg (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) (lawA : LawA D V) (eight : ∀ u ∈ V, 8 ≤ (layer D V 2 u).card)
    (g0 : ∑ v ∈ V, (gap D V 2 2 v).card = 0) {z : ℕ} (zV : z ∈ V)
    (z10 : (layer D V 2 z).card = 10)
    (ten : ((V.filter (fun v => (layer D V 2 v).card ≤ 8)).filter (fun u => D u z = true)).card = 10) :
    ∑ t ∈ (V.filter (fun v => (layer D V 2 v).card ≤ 8)).filter (fun u => D u z = true),
      (inN D V t).card ≤ 64 := by
  classical
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  set P := T.filter (fun u => D u z = true) with hP
  set R := (reverseBall D V z 2).erase z with hR
  -- the reverse two-ball has `17` labels
  have gz : (gap D V 2 2 z).card = 0 := by
    have : (gap D V 2 2 z).card ≤ ∑ v ∈ V, (gap D V 2 2 v).card :=
      single_le_sum (f := fun v => (gap D V 2 2 v).card) (fun _ _ => Nat.zero_le _) zV
    omega
  have row := ReachLedger.row_ledger (i := 2) (j := 2) free (by norm_num) zV
  rw [ball2_card free reg zV, z10, gz, n] at row
  have zR : z ∈ reverseBall D V z 2 :=
    ReachLedger.mem_reverse.mpr ⟨zV, self_mem_ball zV⟩
  have Rc : R.card = 16 := by rw [hR, card_erase_of_mem zR]; omega
  have PT : P ⊆ T := filter_subset _ _
  have TV : T ⊆ V := filter_subset _ _
  -- parents of rows of `P` lie in `R`
  have intoR : ∀ v ∈ V, ∀ t ∈ P, D v t = true → v ∈ R := by
    intro v vV t tP vt
    obtain ⟨tT, tz⟩ := mem_filter.mp tP
    have tV := TV tT
    refine mem_erase.mpr ⟨fun e => ?_, ReachLedger.mem_reverse.mpr ⟨vV, ?_⟩⟩
    · subst e
      exact digonfree free (by norm_num) vV tV vt tz
    · exact ball_step (ball_step (self_mem_ball vV) tV vt) zV tz
  have PR : P ⊆ R := by
    intro t tP
    obtain ⟨tT, tz⟩ := mem_filter.mp tP
    have tV := TV tT
    refine mem_erase.mpr ⟨fun e => ?_, ReachLedger.mem_reverse.mpr ⟨tV, ?_⟩⟩
    · have := (mem_filter.mp tT).2
      rw [e] at this
      omega
    · exact ball_mono_radius (by norm_num : 1 ≤ 2) (ball_step (self_mem_ball tV) zV tz)
  -- count from the tails
  have swap : ∑ t ∈ P, (inN D V t).card = ∑ v ∈ V, (P.filter (fun t => D v t = true)).card :=
    (HostTwo.arcs_between (D := D) V P).symm
  have restrict : ∑ v ∈ V, (P.filter (fun t => D v t = true)).card =
      ∑ v ∈ R, (P.filter (fun t => D v t = true)).card := by
    refine (sum_subset (fun v hv => (ReachLedger.mem_reverse.mp (mem_erase.mp hv).2).1)
      (fun v vV vR => ?_)).symm
    exact card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun t tP vt => vR (intoR v vV t tP vt)))
  have each : ∀ v ∈ R, (P.filter (fun t => D v t = true)).card ≤ if v ∈ T then 1 else 9 := by
    intro v vR
    have vV : v ∈ V := (ReachLedger.mem_reverse.mp (mem_erase.mp vR).2).1
    split_ifs with vT
    · have v8 : (layer D V 2 v).card + 1 = 9 := by
        have := (mem_filter.mp vT).2
        have := eight v vV
        omega
      refine le_trans (card_le_card (fun t ht => ?_)) (lawA v vV v8)
      obtain ⟨tP, vt⟩ := mem_filter.mp ht
      have tT := PT tP
      exact mem_filter.mpr ⟨mem_outN.mpr ⟨TV tT, vt⟩, by have := (mem_filter.mp tT).2; omega⟩
    · refine le_trans (card_le_card (fun t ht => ?_)) (reg v vV).le
      obtain ⟨tP, vt⟩ := mem_filter.mp ht
      exact mem_outN.mpr ⟨TV (PT tP), vt⟩
  have bound := sum_le_sum each
  rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at bound
  have split := card_filter_add_card_filter_not (s := R) (fun v => v ∈ T)
  have big : P.card ≤ (R.filter (fun v => v ∈ T)).card :=
    card_le_card (fun t tP => mem_filter.mpr ⟨PR tP, PT tP⟩)
  rw [Rc] at split
  rw [swap, restrict]
  omega

/-- **Order 36.** Law A and L2 exclude a `4`-free out-regular digraph of degree nine on `36`
labels. No Floor: in the residual, the two rows `z` with second layer `10` have ten tight
parents each, whose in-degrees total at most `2 · 64 = 128`; but the sixteen high rows send at
least `144 - (154 - 140) = 130` arcs to tight rows (in-degree `≤ 11` on the fourteen rows with
second layer `9`, at least seven of their heads per tight row). -/
theorem no36 (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) (lawA : LawA D V) (l2 : HeadLaw D V 9 0 4) : False := by
  classical
  obtain ⟨eight, H16, g0, top, Z2, one⟩ := residual free reg n lawA l2
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  set H := V \ T with hH
  set Z := V.filter (fun v => 10 ≤ (layer D V 2 v).card) with hZ
  set N := H.filter (fun v => v ∉ Z) with hN
  have TV : T ⊆ V := filter_subset _ _
  have memH : ∀ v, v ∈ H ↔ v ∈ V ∧ 9 ≤ (layer D V 2 v).card := by
    intro v
    rw [hH, hT, high_eq, mem_filter]
  have Hc : H.card = 16 := by rw [hH, hT, high_eq]; exact H16
  have Tc : T.card = 20 := by
    have := card_sdiff_add_card_eq_card TV
    rw [← hH] at this
    omega
  have ZH : Z ⊆ H := fun v hv => (memH v).mpr ⟨(mem_filter.mp hv).1, by
    have := (mem_filter.mp hv).2; omega⟩
  have Nc : N.card = 14 := by
    have split := card_filter_add_card_filter_not (s := H) (fun v => v ∈ Z)
    have : H.filter (fun v => v ∈ Z) = Z := by
      ext v
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨ZH h, h⟩⟩
    rw [this, Z2, Hc] at split
    rw [hN]
    omega
  -- (1) each tight row heads exactly one row of `Z`
  have oneZ : ∀ t ∈ T, (Z.filter (fun z => D t z = true)).card = 1 := by
    intro t tT
    obtain ⟨tV, t8⟩ := mem_filter.mp tT
    have eqf : (outN D V t).filter (fun x => 10 ≤ (layer D V 2 x).card) =
        Z.filter (fun z => D t z = true) := by
      ext x
      simp only [mem_filter, mem_outN, hZ]
      tauto
    rw [← eqf]
    exact one t tV t8
  -- (2) the rows of `Z` have exactly ten parents, all tight
  have arcsTZ := HostTwo.arcs_between (D := D) T Z
  have sumTZ : ∑ z ∈ Z, (T.filter (fun u => D u z = true)).card = 20 := by
    rw [← arcsTZ, sum_congr rfl oneZ, sum_const, smul_eq_mul, Tc]
  have capZ : ∀ z ∈ Z, (T.filter (fun u => D u z = true)).card ≤ (inN D V z).card ∧
      (inN D V z).card ≤ 10 := by
    intro z hz
    obtain ⟨zV, zw⟩ := mem_filter.mp hz
    refine ⟨card_le_card (fun u hu => ?_), indeg_wider free reg n zV zw⟩
    obtain ⟨uT, uz⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨TV uT, uz⟩
  have tenZ : ∀ z ∈ Z, (T.filter (fun u => D u z = true)).card = 10 := by
    by_contra bad
    push Not at bad
    obtain ⟨z, hz, ne⟩ := bad
    have lt : ∑ z ∈ Z, (T.filter (fun u => D u z = true)).card < ∑ _z ∈ Z, 10 :=
      sum_lt_sum (fun z hz => (capZ z hz).1.trans (capZ z hz).2)
        ⟨z, hz, by have := capZ z hz; omega⟩
    rw [sum_const, smul_eq_mul, Z2] at lt
    omega
  have tightParents : ∀ z ∈ Z, ∀ v ∈ V, D v z = true → v ∈ T := by
    intro z hz v vV vz
    have sub : T.filter (fun u => D u z = true) ⊆ inN D V z := fun u hu =>
      mem_filter.mpr ⟨TV (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
    have eq := eq_of_subset_of_card_le sub (by have := capZ z hz; have := tenZ z hz; omega)
    have : v ∈ inN D V z := mem_filter.mpr ⟨vV, vz⟩
    rw [← eq] at this
    exact (mem_filter.mp this).1
  -- (3) the high rows send at least 130 arcs to tight rows
  have outSplit : ∀ h ∈ H, (T.filter (fun v => D h v = true)).card +
      (H.filter (fun v => D h v = true)).card = 9 := by
    intro h hh
    have split := card_filter_add_card_filter_not (s := outN D V h) (fun v => v ∈ T)
    have e1 : (outN D V h).filter (fun v => v ∈ T) = T.filter (fun v => D h v = true) := by
      ext v
      simp only [mem_filter, mem_outN]
      exact ⟨fun ⟨⟨_, a⟩, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨⟨TV b, a⟩, b⟩⟩
    have e2 : (outN D V h).filter (fun v => v ∉ T) = H.filter (fun v => D h v = true) := by
      ext v
      simp only [mem_filter, mem_outN, hH, mem_sdiff]
      tauto
    rw [e1, e2, reg h ((memH h).mp hh).1] at split
    exact split
  have sumOut : ∑ h ∈ H, (T.filter (fun v => D h v = true)).card +
      ∑ h ∈ H, (H.filter (fun v => D h v = true)).card = 144 := by
    rw [← sum_add_distrib, sum_congr rfl outSplit, sum_const, smul_eq_mul, Hc]
  have arcsHH := HostTwo.arcs_between (D := D) H H
  have inH : ∀ h ∈ H, (H.filter (fun u => D u h = true)).card +
      (if h ∈ Z then 0 else (T.filter (fun u => D u h = true)).card) ≤ if h ∈ Z then 0 else 11 := by
    intro h hh
    obtain ⟨hV, h9⟩ := (memH h).mp hh
    split_ifs with hz
    · have : H.filter (fun u => D u h = true) = ∅ :=
        filter_eq_empty_iff.mpr (fun v vH vh =>
          (mem_sdiff.mp vH).2 (tightParents h hz v (mem_sdiff.mp vH).1 vh))
      rw [this, card_empty]
    · have w9 : (layer D V 2 h).card ≤ 9 := by
        by_contra big
        exact hz (mem_filter.mpr ⟨hV, by omega⟩)
      have disj : Disjoint (H.filter (fun u => D u h = true)) (T.filter (fun u => D u h = true)) :=
        disjoint_filter_filter sdiff_disjoint
      have sub : H.filter (fun u => D u h = true) ∪ T.filter (fun u => D u h = true) ⊆ inN D V h := by
        intro v hv
        rcases mem_union.mp hv with hv | hv
        · exact mem_filter.mpr ⟨(mem_sdiff.mp (mem_filter.mp hv).1).1, (mem_filter.mp hv).2⟩
        · exact mem_filter.mpr ⟨TV (mem_filter.mp hv).1, (mem_filter.mp hv).2⟩
      have c := card_le_card sub
      rw [card_union_of_disjoint disj] at c
      have := indeg_wide free reg n hV h9
      omega
  have sumIn := sum_le_sum inH
  rw [sum_add_distrib, ← arcsHH, sum_ite, sum_ite] at sumIn
  simp only [sum_const_zero, zero_add, sum_const, smul_eq_mul] at sumIn
  have NZ : H.filter (fun h => ¬ h ∈ Z) = N := rfl
  rw [NZ, Nc] at sumIn
  have arcsTN := HostTwo.arcs_between (D := D) T N
  have perT : ∀ t ∈ T, 7 ≤ (N.filter (fun v => D t v = true)).card := by
    intro t tT
    obtain ⟨tV, t8⟩ := mem_filter.mp tT
    have s := supply free reg lawA tV t8
    rw [← hT, ← hH] at s
    have sub : H.filter (fun v => D t v = true) ⊆
        N.filter (fun v => D t v = true) ∪ Z.filter (fun v => D t v = true) := by
      intro v hv
      obtain ⟨vH, tv⟩ := mem_filter.mp hv
      by_cases vz : v ∈ Z
      · exact mem_union_right _ (mem_filter.mpr ⟨vz, tv⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨vH, vz⟩, tv⟩)
    have c := (card_le_card sub).trans (card_union_le _ _)
    have := oneZ t tT
    omega
  have lowTN : 140 ≤ ∑ v ∈ N, (T.filter (fun u => D u v = true)).card := by
    rw [← arcsTN]
    have := sum_le_sum perT
    rw [sum_const, smul_eq_mul, Tc] at this
    omega
  have arcsHT := HostTwo.arcs_between (D := D) H T
  have low : 130 ≤ ∑ t ∈ T, (H.filter (fun u => D u t = true)).card := by
    rw [← arcsHT]
    omega
  -- (4) but the tight rows have total in-degree at most 128
  have upT : ∑ t ∈ T, (H.filter (fun u => D u t = true)).card ≤ ∑ t ∈ T, (inN D V t).card :=
    sum_le_sum (fun t _ => card_le_card (fun u hu =>
      mem_filter.mpr ⟨(mem_sdiff.mp (mem_filter.mp hu).1).1, (mem_filter.mp hu).2⟩))
  have fiber : ∑ t ∈ T, (inN D V t).card =
      ∑ z ∈ Z, ∑ t ∈ T.filter (fun u => D u z = true), (inN D V t).card := by
    have e1 : ∑ t ∈ T, (inN D V t).card =
        ∑ t ∈ T, ∑ _z ∈ Z.filter (fun z => D t z = true), (inN D V t).card := by
      refine sum_congr rfl (fun t tT => ?_)
      rw [sum_const, oneZ t tT, one_smul]
    rw [e1]
    simp only [sum_filter]
    exact sum_comm
  have perZ : ∀ z ∈ Z, ∑ t ∈ T.filter (fun u => D u z = true), (inN D V t).card ≤ 64 := by
    intro z hz
    obtain ⟨zV, zw⟩ := mem_filter.mp hz
    exact parent_indeg free reg n lawA eight g0 zV (le_antisymm (top z zV) zw) (tenZ z hz)
  have up := sum_le_sum perZ
  rw [sum_const, smul_eq_mul, Z2, ← fiber] at up
  omega

/-! ### Minimum out-degree nine -/

/-- Laws quantified over every out-regular `4`-free digraph on `V`. -/
def Laws (V : Finset ℕ) (P : CH.Digraph → Finset ℕ → Prop) : Prop :=
  ∀ E : CH.Digraph, QFree E V 4 → (∀ v ∈ V, (outN E V v).card = 9) → P E V

theorem no36_floor_min {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 4)
    (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 36)
    (lawA : Laws V LawA) (l2 : Laws V (fun E V => HeadLaw E V 9 0 4)) (floor : Laws V Floor10) :
    False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no36_floor freeE regE n (lawA E freeE regE) (l2 E freeE regE) (floor E freeE regE)

theorem no36_min {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 4)
    (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 36)
    (lawA : Laws V LawA) (l2 : Laws V (fun E V => HeadLaw E V 9 0 4)) : False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no36 freeE regE n (lawA E freeE regE) (l2 E freeE regE)

#print axioms floor25F
#print axioms floor26F
#print axioms wide7
#print axioms budget
#print axioms high_count
#print axioms no_seven
#print axioms residual
#print axioms no36_floor
#print axioms parent_indeg
#print axioms no36
#print axioms no36_floor_min
#print axioms no36_min
end LeanCH.BR.ThirtySix
