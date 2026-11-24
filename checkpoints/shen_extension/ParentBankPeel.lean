import checkpoints.shen_extension.ReachLedgerCatalog

/-!
# Padding, deletion, growth floors and the peeled parent bank

Lean 4.35.0. Every statement is generic in the graph `D`, the label set `V`, the order `n`, the
cutoff `q`, the degree `r`, the radii and the bank size `s`. No number is fixed here.

## Regime theorems (each concludes `False`)

* `pad_regime`: an exclusion at order `n` excludes every nonempty order `m ≤ n` at the same
  cutoff and degree (fresh labels point at every old label; nothing points at a fresh label).
  `noHost_of_excluded`: an exclusion at order `q t`, degree `t`, is the lower quota `NoHost q t`.
* `deletion_regime`: `0 < n ≤ q (r - 1) + 1` closes from `NoHost q (r - 1)` (one deletion).
* `growth_regime`: `n ≤ floorTable q r i + floorTable q r j` with `i + j ≤ q` closes from the
  lower quotas `NoHost q t`, `t < r` (the two-ball ledger on the growth floors).
* `bank_indegree`: at the band `n = q (r - 1) + 2`, a bank size `s ≤ q (r - 1)` with
  `(n - floorTable q r (q - 2) - 1 - s) ⌊r²/4⌋ + peelCap q r s < s (n - s)` forbids every root of
  indegree at least `s`.
* `bank_regime`: the same arithmetic with `s ≤ r` closes outright (some root has indegree `r`).

## The steps behind them

* `pad`: the padded graph itself.
* `growthFloor`, `floorTable`: `g(m) = min (m + r - ⌊(m-1)/q⌋) (q (r-1) + 1)` and its iterates
  from `0`; `growthFloor_mono`: `g` is monotone.
* `floor_step`: `|ball v (k+1)| ≥ g(|ball v k| - 1) + 1` (the induced-child rule with quota
  `⌊(m-1)/q⌋ + 1`, or the saturation `m > q (r-1)`).
* `floor_table`: `|ball v k| ≥ floorTable q r k + 1` for every `k ≤ q`.
* `bank_outside`, `parent_outside`: a parent of `a`, and a parent of a parent of `a`, lies outside
  the closed `(q-2)`-ball of `a`.
* `cross_cover`: at the band every cross pair of a bank `S ⊆ inN a` and its complement is covered
  by an exact row outside the `(q-2)`-ball: `s (n - s) ≤ ∑ p_c (r - p_c)`.
* `rowCap`, `quarter`: `p (r - p) ≤ rowCap r b` for `p ≤ b`, and `rowCap r b ≤ ⌊r²/4⌋`.
* `peel_sum`: peeling a bank of `s` labels by rows with at most `⌊(m-1)/q⌋` heads in the remaining
  `m` labels: `∑_{c ∈ S} Φ(|N_S c|) ≤ ∑_{i < s} Φ(i + ⌊(s-1-i)/q⌋)` for every monotone `Φ`.
* `bank_capacity`: demand against peeled capacity,
  `s (n - s) ≤ (|R| - s) ⌊r²/4⌋ + peelCap q r s`, `R` the complement of the `(q-2)`-ball.
* `root_indegree`: some label has indegree at least the minimum outdegree.
* Catalog: `Floors D V q r` from `floors_packet` (free, degree, lower quotas).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.ParentBankPeel
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger

variable {D : CH.Digraph} {V : Finset ℕ} {q r n : ℕ}

/-! ### Padding -/

/-- No `q`-free graph of minimum outdegree `r` on exactly `n` labels. -/
def Excluded (q r n : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (W : Finset ℕ), W.card = n → QFree E W q → ¬ ∀ x ∈ W, r ≤ (outN E W x).card

/-- The padded digraph: arcs only into `V`; old rows keep their old arcs, fresh rows see all of `V`. -/
def padArc (D : CH.Digraph) (V : Finset ℕ) : CH.Digraph :=
  fun a b => decide (b ∈ V) && (decide (a ∉ V) || D a b)

theorem pad_walk {W : Finset ℕ} {a b m : ℕ} (w : Walk (padArc D V) W a b m) :
    a ∈ V → Walk D V a b m := by
  induction w with
  | refl a => intro _; exact .refl a
  | @step a b c k _ hab _ ih =>
    intro av
    simp only [padArc, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hab
    obtain ⟨bv, h⟩ := hab
    have arc : D a b = true := by
      rcases h with h | h
      · exact absurd av h
      · exact h
    exact .step bv arc (ih bv)

theorem pad_free {W : Finset ℕ} (free : QFree D V q) : QFree (padArc D V) W q := by
  intro a l h1 hl w
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  obtain ⟨y, _, _, last⟩ := w.unsnoc
  simp only [padArc, Bool.and_eq_true, decide_eq_true_eq] at last
  exact free a (k + 1) h1 hl (pad_walk w last.1)

/-- **Padding.** A `q`-free graph of minimum outdegree `r` on at most `n` labels extends to one on
exactly `n` labels. -/
theorem pad (free : QFree D V q) (live : V.Nonempty) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (le : V.card ≤ n) :
    ∃ (E : CH.Digraph) (W : Finset ℕ), W.card = n ∧ QFree E W q ∧ ∀ x ∈ W, r ≤ (outN E W x).card := by
  classical
  have far : ∀ x ∈ V, x < V.sup id + 1 := fun x hx => Nat.lt_succ_of_le (le_sup (f := id) hx)
  refine ⟨padArc D V, V ∪ (range (n - V.card)).image (fun i => V.sup id + 1 + i), ?_,
    pad_free free, ?_⟩
  · have dis : Disjoint V ((range (n - V.card)).image (fun i => V.sup id + 1 + i)) := by
      rw [disjoint_left]
      intro x xv hx
      obtain ⟨i, _, e⟩ := mem_image.mp hx
      have := far x xv
      omega
    rw [card_union_of_disjoint dis, card_image_of_injective _ (add_right_injective _), card_range]
    omega
  · obtain ⟨v0, v0V⟩ := live
    have big : r ≤ V.card := (degree v0 v0V).trans (card_le_card outN_subset)
    intro x hx
    by_cases xv : x ∈ V
    · refine (degree x xv).trans (card_le_card (fun z hz => ?_))
      obtain ⟨zv, arc⟩ := mem_outN.mp hz
      refine mem_outN.mpr ⟨mem_union_left _ zv, ?_⟩
      simp [padArc, zv, arc]
    · refine big.trans (card_le_card (fun z zv => ?_))
      refine mem_outN.mpr ⟨mem_union_left _ zv, ?_⟩
      simp [padArc, zv, xv]

/-- **Padding regime.** An exclusion at order `n` excludes every nonempty smaller order. -/
theorem pad_regime {m : ℕ} (top : Excluded q r n) (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (size : V.card = m) (arith : 0 < m ∧ m ≤ n) :
    False := by
  obtain ⟨E, W, card, efree, edeg⟩ := pad free (card_pos.mp (show 0 < V.card by omega)) degree
    (show V.card ≤ n by omega)
  exact top E W card efree edeg

/-- An exclusion at order `q t` and degree `t` is the lower quota. -/
theorem noHost_of_excluded {t : ℕ} (top : Excluded q t (q*t)) : NoHost q t :=
  fun _ _ live small free paid => pad_regime top free paid rfl ⟨card_pos.mpr live, small⟩

/-! ### One deletion -/

/-- **Deletion regime.** `0 < n ≤ q (r-1) + 1` closes from the quota one degree down. -/
theorem deletion_regime (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (size : V.card = n) (lower : NoHost q (r-1)) (hr : 2 ≤ r) (arith : 0 < n ∧ n ≤ q*(r-1)+1) :
    False := by
  have h := BypassBankReplay.order_floor lower hr free (card_pos.mp (by omega)) degree
  omega

/-! ### Growth floors -/

/-- One step of the floor recursion, in punctured units. -/
def growthFloor (q r m : ℕ) : ℕ := min (m + r - (m - 1) / q) (q * (r - 1) + 1)

/-- The iterated floors from `0`: `floorTable q r k` other labels within `k` steps. -/
def floorTable (q r : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => growthFloor q r (floorTable q r k)

theorem div_succ_le (hq : 1 ≤ q) (m : ℕ) : (m + 1) / q ≤ m / q + 1 :=
  calc (m + 1) / q ≤ (m + q) / q := Nat.div_le_div_right (by omega)
    _ = m / q + 1 := Nat.add_div_right m (by omega)

theorem growthFloor_succ (hq : 1 ≤ q) (m : ℕ) : growthFloor q r m ≤ growthFloor q r (m + 1) := by
  unfold growthFloor
  have h1 : m / q ≤ (m - 1) / q + 1 := by
    rcases Nat.eq_zero_or_pos m with e | pos
    · subst e
      simp
    · have := div_succ_le hq (m - 1)
      rwa [Nat.sub_add_cancel pos] at this
  have h2 : (m - 1) / q ≤ m - 1 := Nat.div_le_self _ _
  have h3 : m / q ≤ m := Nat.div_le_self _ _
  rw [show m + 1 - 1 = m by omega]
  omega

theorem growthFloor_mono (hq : 1 ≤ q) {a b : ℕ} (h : a ≤ b) : growthFloor q r a ≤ growthFloor q r b :=
  monotone_nat_of_le_succ (fun m => growthFloor_succ hq m) h

/-- **Floor step.** The punctured `k`-ball of `m` labels has no arc back to the root; while
`m ≤ q (r-1)` the quota `⌊(m-1)/q⌋ + 1` forces a row with that many fewer heads inside. -/
theorem floor_step {v k : ℕ} (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (lower : ∀ t, t < r → NoHost q t) (hq : 1 ≤ q) (hr : 1 ≤ r) (vv : v ∈ V)
    (hk : 1 ≤ k) (kq : k + 1 ≤ q) :
    growthFloor q r ((ball D V v k).card - 1) + 1 ≤ (ball D V v (k+1)).card := by
  have one := ball_one free hq vv
  have deg := degree v vv
  have b1k := card_le_card (ball_mono_radius (D := D) (W := V) (u := v) hk)
  have kk1 := card_le_card (ball_mono_radius (D := D) (W := V) (u := v) (show k ≤ k + 1 by omega))
  unfold growthFloor
  by_cases big : q * (r - 1) < (ball D V v k).card - 1
  · have := min_le_right ((ball D V v k).card - 1 + r - ((ball D V v k).card - 1 - 1) / q)
      (q * (r - 1) + 1)
    omega
  · have dm := Nat.div_add_mod ((ball D V v k).card - 1 - 1) q
    have ml := Nat.mod_lt ((ball D V v k).card - 1 - 1) (show q > 0 by omega)
    have tr : ((ball D V v k).card - 1 - 1) / q < r - 1 :=
      Nat.lt_of_mul_lt_mul_left (a := q) (by omega)
    have small : (ball D V v k).card ≤ q * (((ball D V v k).card - 1 - 1) / q + 1) + 1 := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have grow := ball_growth (lower _ (by omega)) free degree hr vv hk kq small
    have := min_le_left ((ball D V v k).card - 1 + r - ((ball D V v k).card - 1 - 1) / q)
      (q * (r - 1) + 1)
    have h2 : ((ball D V v k).card - 1 - 1) / q ≤ (ball D V v k).card - 1 - 1 := Nat.div_le_self _ _
    omega

/-- **Floor table.** Every closed `k`-ball, `k ≤ q`, holds at least `floorTable q r k + 1` labels. -/
theorem floor_table {v : ℕ} (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (lower : ∀ t, t < r → NoHost q t) (hq : 1 ≤ q) (hr : 1 ≤ r) (vv : v ∈ V) :
    ∀ k, k ≤ q → floorTable q r k + 1 ≤ (ball D V v k).card := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [floorTable, zero_add]
    exact card_pos.mpr ⟨v, self_mem_ball vv⟩
  | succ k ih =>
    intro kq
    show growthFloor q r (floorTable q r k) + 1 ≤ _
    rcases Nat.eq_zero_or_pos k with e | pos
    · subst e
      have one := ball_one free hq vv
      have deg := degree v vv
      simp only [floorTable, growthFloor, Nat.zero_sub, Nat.zero_div, zero_add, Nat.sub_zero]
      omega
    · have h := ih (by omega)
      have step := floor_step free degree lower hq hr vv pos kq
      have mono := growthFloor_mono (r := r) hq (show floorTable q r k ≤ (ball D V v k).card - 1 by omega)
      omega

/-- **Growth regime.** The two-ball ledger on the growth floors: `n ≤ F_i + F_j`, `i + j ≤ q`. -/
theorem growth_regime {i j : ℕ} (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (size : V.card = n) (lower : ∀ t, t < r → NoHost q t) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hij : i + j ≤ q) (arith : 0 < n ∧ n ≤ floorTable q r i + floorTable q r j) : False := by
  have h := card_ge_of_two_balls free hij
    (fun v vv => floor_table free degree lower hq hr vv i (by omega))
    (fun v vv => floor_table free degree lower hq hr vv j (by omega)) (card_pos.mp (by omega))
  omega

/-! ### The parent bank -/

theorem bank_outside {a p : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (av : a ∈ V)
    (pa : D p a = true) : p ∉ ball D V a (q-2) := by
  intro h
  obtain ⟨_, j, hj, w⟩ := mem_ball.mp h
  exact free a (j + 1) (by omega) (by omega) (w.snoc av pa)

theorem parent_outside {a p c : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (av : a ∈ V) (pv : p ∈ V)
    (pa : D p a = true) (cp : D c p = true) : c ∉ ball D V a (q-2) := by
  intro h
  obtain ⟨_, j, hj, w⟩ := mem_ball.mp h
  exact free a (j + 1 + 1) (by omega) (by omega) ((w.snoc pv cp).snoc av pa)

/-- **Cross cover.** At the band order, every pair of a bank label and an outside label has a
common exact parent, and that parent lies outside the `(q-2)`-ball of the root. -/
theorem cross_cover {a : ℕ} {S : Finset ℕ} (lower : NoHost q (r-1)) (free : QFree D V q)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (band : V.card = q*(r-1)+2) (av : a ∈ V) (sa : S ⊆ inN D V a) :
    S.card * (V.card - S.card) ≤
      ∑ c ∈ (V \ ball D V a (q-2)).filter (fun c => (outN D V c).card = r),
        (outN D S c).card * (r - (outN D S c).card) := by
  classical
  have sv : S ⊆ V := fun x hx => (mem_inN.mp (sa hx)).1
  have cover : S ×ˢ (V \ S) ⊆ ((V \ ball D V a (q-2)).filter (fun c => (outN D V c).card = r)).biUnion
      (fun c => outN D S c ×ˢ outN D (V \ S) c) := by
    intro x hx
    obtain ⟨us, ws⟩ := mem_product.mp hx
    obtain ⟨wv, wn⟩ := mem_sdiff.mp ws
    have ne : x.1 ≠ x.2 := fun e => wn (e ▸ us)
    obtain ⟨c, cv, _, _, cu, cw, cd⟩ := LoneRow.pair_parent lower free (by omega) hr degree band
      (sv us) wv ne
    have off := parent_outside free hq av (sv us) (mem_inN.mp (sa us)).2 cu
    exact mem_biUnion.mpr ⟨c, mem_filter.mpr ⟨mem_sdiff.mpr ⟨cv, off⟩, cd⟩,
      mem_product.mpr ⟨mem_outN.mpr ⟨us, cu⟩, mem_outN.mpr ⟨ws, cw⟩⟩⟩
  have lhs := card_le_card cover
  rw [card_product, card_sdiff_of_subset sv] at lhs
  refine lhs.trans (card_biUnion_le.trans (le_of_eq (sum_congr rfl (fun c hc => ?_))))
  have split := card_outN_union (D := D) (show Disjoint S (V \ S) from disjoint_sdiff) c
  rw [union_sdiff_of_subset sv, (mem_filter.mp hc).2] at split
  rw [card_product]
  congr 1
  omega

/-- Best per-row coverage `max_{p ≤ b} p (r - p)`. -/
def rowCap (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => max (rowCap r b) ((b + 1) * (r - (b + 1)))

/-- The peeled capacity of a bank of `s` labels: row `i` keeps at most `i + ⌊(s-1-i)/q⌋` heads. -/
def peelCap (q r s : ℕ) : ℕ := ∑ i ∈ range s, rowCap r (i + (s - 1 - i) / q)

theorem rowCap_succ (r b : ℕ) : rowCap r b ≤ rowCap r (b + 1) := le_max_left _ _

theorem rowCap_mono (r : ℕ) {a b : ℕ} (h : a ≤ b) : rowCap r a ≤ rowCap r b :=
  monotone_nat_of_le_succ (rowCap_succ r) h

theorem le_rowCap (r : ℕ) {p b : ℕ} (h : p ≤ b) : p * (r - p) ≤ rowCap r b := by
  refine le_trans ?_ (rowCap_mono r h)
  rcases p with _ | p
  · simp
  · exact le_max_right _ _

theorem quarter (r p : ℕ) : p * (r - p) ≤ r * r / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases le_or_gt p r with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    nlinarith [sq_nonneg ((p : ℤ) - d)]
  · rw [Nat.sub_eq_zero_of_le h.le]
    simp

theorem rowCap_le (r b : ℕ) : rowCap r b ≤ r * r / 4 := by
  induction b with
  | zero => simp [rowCap]
  | succ b ih => exact max_le ih (quarter r (b + 1))

/-- **Peel.** A bank of `s` labels is emptied by removing, each time, a row with at most
`⌊(m-1)/q⌋` heads among the `m` labels left. Charged to the original bank, the `i`-th row keeps at
most `i + ⌊(s-1-i)/q⌋` heads, for every monotone price `Φ`. -/
theorem peel_sum (free : QFree D V q) (hq : 1 ≤ q) :
    ∀ (s : ℕ) (S : Finset ℕ), S ⊆ V → S.card = s → (∀ t, q * t < s + q → NoHost q t) →
      ∀ Φ : ℕ → ℕ, (∀ a b, a ≤ b → Φ a ≤ Φ b) →
        ∑ c ∈ S, Φ (outN D S c).card ≤ ∑ i ∈ range s, Φ (i + (s - 1 - i) / q) := by
  intro s
  induction s with
  | zero =>
    intro S _ card _ _ _
    rw [card_eq_zero.mp card]
    simp
  | succ s ih =>
    intro S sv card ranks Φ mono
    classical
    have dm := Nat.div_add_mod s q
    have ml := Nat.mod_lt s (show q > 0 by omega)
    have small : S.card ≤ q * (s / q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have room : q * (s / q + 1) < s + 1 + q := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    obtain ⟨x, xs, short⟩ := fragment_row (ranks _ room) free sv (card_pos.mp (by omega)) small
    have rest := ih (S.erase x) ((erase_subset _ _).trans sv)
      (by rw [card_erase_of_mem xs, card]; rfl) (fun t h => ranks t (by omega))
      (fun p => Φ (p + 1)) (fun a b h => mono _ _ (by omega))
    have each : ∀ c ∈ S.erase x, Φ (outN D S c).card ≤ Φ ((outN D (S.erase x) c).card + 1) := by
      intro c _
      refine mono _ _ ((card_le_card (show outN D S c ⊆ insert x (outN D (S.erase x) c) from ?_)).trans
        (card_insert_le _ _))
      intro z hz
      obtain ⟨zs, arc⟩ := mem_outN.mp hz
      by_cases e : z = x
      · exact e ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, zs⟩, arc⟩)
    rw [← add_sum_erase S _ xs, sum_range_succ', add_comm]
    have head : Φ (outN D S x).card ≤ Φ (0 + (s + 1 - 1 - 0) / q) :=
      mono _ _ (by rw [show s + 1 - 1 - 0 = s by omega]; omega)
    have shift : ∑ i ∈ range s, Φ (i + (s - 1 - i) / q + 1) =
        ∑ i ∈ range s, Φ (i + 1 + (s + 1 - 1 - (i + 1)) / q) := by
      refine sum_congr rfl (fun i _ => ?_)
      rw [show s + 1 - 1 - (i + 1) = s - 1 - i by omega, Nat.add_right_comm]
    have := sum_le_sum each
    omega

/-- **Bank capacity.** Demand of the cross pairs against the peeled capacity of the reverse region
`R = V \ ball a (q-2)`. -/
theorem bank_capacity {a : ℕ} {S : Finset ℕ} (lower : NoHost q (r-1)) (free : QFree D V q)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (band : V.card = q*(r-1)+2) (av : a ∈ V) (sa : S ⊆ inN D V a)
    (ranks : ∀ t, q * t < S.card + q → NoHost q t) :
    S.card * (V.card - S.card) ≤
      ((V \ ball D V a (q-2)).card - S.card) * (r * r / 4) + peelCap q r S.card := by
  classical
  have sv : S ⊆ V := fun x hx => (mem_inN.mp (sa hx)).1
  have sR : S ⊆ V \ ball D V a (q-2) := fun x hx =>
    mem_sdiff.mpr ⟨sv hx, bank_outside free (by omega) av (mem_inN.mp (sa hx)).2⟩
  have cov := cross_cover lower free hq hr degree band av sa
  have bound : ∑ c ∈ (V \ ball D V a (q-2)).filter (fun c => (outN D V c).card = r),
        (outN D S c).card * (r - (outN D S c).card) ≤
      ∑ c ∈ V \ ball D V a (q-2), (if c ∈ S then rowCap r (outN D S c).card else r * r / 4) := by
    refine (sum_le_sum (fun c _ => ?_)).trans (sum_le_sum_of_subset (filter_subset _ _))
    split_ifs
    · exact le_rowCap r le_rfl
    · exact quarter r _
  rw [← sum_sdiff sR] at bound
  have outer : ∑ c ∈ (V \ ball D V a (q-2)) \ S,
      (if c ∈ S then rowCap r (outN D S c).card else r * r / 4) =
        ((V \ ball D V a (q-2)).card - S.card) * (r * r / 4) := by
    rw [sum_congr rfl (fun c hc => (show (if c ∈ S then rowCap r (outN D S c).card else r * r / 4) = r * r / 4
      by simp [(mem_sdiff.mp hc).2])), sum_const, smul_eq_mul,
      card_sdiff_of_subset sR]
  have inner : ∑ c ∈ S, (if c ∈ S then rowCap r (outN D S c).card else r * r / 4) =
      ∑ c ∈ S, rowCap r (outN D S c).card := sum_congr rfl (fun c hc => by simp [hc])
  have peel := peel_sum free (by omega) S.card S sv rfl ranks (rowCap r)
    (fun _ _ h => rowCap_mono r h)
  unfold peelCap
  omega

/-- Some label has indegree at least the minimum outdegree. -/
theorem root_indegree (live : V.Nonempty) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) :
    ∃ a ∈ V, r ≤ (inN D V a).card := by
  have eq : ∑ x ∈ V, (outN D V x).card = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have le : ∑ _v ∈ V, r ≤ ∑ v ∈ V, (inN D V v).card := eq ▸ sum_le_sum degree
  exact exists_le_of_sum_le live le

/-- **Bank indegree regime.** At the band `n = q (r-1) + 2`, a bank size `s ≤ q (r-1)` whose demand
exceeds the peeled capacity forbids every root of indegree at least `s`. -/
theorem bank_indegree {s : ℕ} (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (size : V.card = n) (lower : ∀ t, t < r → NoHost q t) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (band : n = q*(r-1)+2) (fit : s ≤ q*(r-1))
    (arith : (n - (floorTable q r (q-2) + 1) - s) * (r * r / 4) + peelCap q r s < s * (n - s))
    {a : ℕ} (av : a ∈ V) : (inN D V a).card < s := by
  by_contra! many
  obtain ⟨S, sa, card⟩ := exists_subset_card_eq many
  have ranks : ∀ t, q * t < S.card + q → NoHost q t := by
    intro t h
    refine lower t (Nat.lt_of_mul_lt_mul_left (a := q) ?_)
    rw [Nat.mul_sub, Nat.mul_one] at fit
    have : q ≤ q * r := Nat.le_mul_of_pos_right q (by omega)
    omega
  have cap := bank_capacity (lower (r-1) (by omega)) free hq hr degree (size.trans band) av sa ranks
  have fl := floor_table free degree lower (by omega) (by omega) av (q-2) (by omega)
  have rc : (V \ ball D V a (q-2)).card = V.card - (ball D V a (q-2)).card :=
    card_sdiff_of_subset ball_subset
  have mono := Nat.mul_le_mul_right (r * r / 4)
    (show (V \ ball D V a (q-2)).card - S.card ≤ n - (floorTable q r (q-2) + 1) - s by omega)
  rw [card, size] at cap
  rw [card] at mono
  omega

/-- **Bank regime.** At the band `n = q (r-1) + 2`, a bank size `s ≤ r` whose demand exceeds the
peeled capacity closes outright. -/
theorem bank_regime {s : ℕ} (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (size : V.card = n) (lower : ∀ t, t < r → NoHost q t) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (band : n = q*(r-1)+2) (hs : s ≤ r)
    (arith : (n - (floorTable q r (q-2) + 1) - s) * (r * r / 4) + peelCap q r s < s * (n - s)) :
    False := by
  obtain ⟨a, av, big⟩ := root_indegree (card_pos.mp (by omega)) degree
  have fit : s ≤ q * (r - 1) := by
    have := Nat.mul_le_mul_right (r - 1) hq
    omega
  have := bank_indegree free degree size lower hq hr band fit arith av
  omega

/-! ### Catalog -/

/-- The growth floors at every root and every radius up to the cutoff. -/
structure Floors (D : CH.Digraph) (V : Finset ℕ) (q r : ℕ) : Prop where
  table : ∀ v ∈ V, ∀ k, k ≤ q → floorTable q r k + 1 ≤ (ball D V v k).card

@[aesop safe forward (immediate := [free,degree,lower,hq,hr]) (rule_sets := [CHGraphFamilies])]
theorem floors_packet (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (lower : ∀ t, t < r → NoHost q t) (hq : 1 ≤ q) (hr : 1 ≤ r) : Floors D V q r :=
  ⟨fun _ vv => floor_table free degree lower hq hr vv⟩

#print axioms pad_walk
#print axioms pad_free
#print axioms pad
#print axioms pad_regime
#print axioms noHost_of_excluded
#print axioms deletion_regime
#print axioms growthFloor_mono
#print axioms floor_step
#print axioms floor_table
#print axioms growth_regime
#print axioms bank_outside
#print axioms parent_outside
#print axioms cross_cover
#print axioms le_rowCap
#print axioms quarter
#print axioms rowCap_le
#print axioms peel_sum
#print axioms bank_capacity
#print axioms root_indegree
#print axioms bank_indegree
#print axioms bank_regime
#print axioms floors_packet
end LeanCH.BR.ParentBankPeel
