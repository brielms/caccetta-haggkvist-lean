import checkpoints.shen_extension.ThinSuppliers
import checkpoints.shen_extension.FifthStripAllTop

/-!
# The top orders at degree nine: thin savers are paid, the fat savers remain

Setting: every out-degree exactly `r`, no closed walk of length `1..q`. A root is *thin*
(`ThinSuppliers.Thin`) when its second layer has `r - 1` labels. The *score* of a row at radii
`(i, j)`, `i + j ≤ q`, is `|B i| + |B j|`, the *level* `|V| + 1`; by `ReachLedger.ledger` the
scores plus the gap sizes sum to `|V| (|V| + 1)`.

Generic (all `q`, `r`):

* `grow_from`: in a `q`-free set of minimum out-degree one, a row with `d` heads has at least
  `min (d + k) (q + 1)` labels within `k ≥ 1` steps (a closed ball has at least `q + 1`).
* `no_short_thin_sharp`: `ThinSuppliers.no_short_thin` with the sharper supplier bound. A complete
  head `x` of a short thin root `u`, serving `s` classes, has an `X`-head `b` with at least `s`
  heads in `X` (`supplier_gain`), so `|B_X k b| ≥ min (s + k) (q + 1)` (`grow_from`), and by
  `complete_ball` its score is at least
  `|B (i+1) u| + |B (j+1) u| + min (s + i - 1) (q + 1) + min (s + j - 1) (q + 1) - 2r`.
  If that is `≥ |V| + 1 + s` for every `1 ≤ s ≤ r` (`bankrow`), rows that are not thin reach the
  level, thin rows fall short by at most `δ` and `m (δ + 1) < m² + (2q + 2 - r)` for all `m`, then
  every thin row reaches the level. (The unsharpened `no_short_thin` misses `n = 54` by one.)

Instances at `r = 9` (floors and the fat condition are named hypotheses; see the report):

* `no54_of_fat` (`q = 6`, radii `(3, 3)`, level 55): thin rows are paid; if every row that is not
  thin has `|B 3| ≥ 28`, contradiction by parity (`2 |B 3| ≠ 55`).
* `no72_of_fat` (`q = 8`, radii `(4, 4)`, level 73): the same with `|B 4| ≥ 37`.
* `no62_of_fat` (`q = 7`, radii `(3, 4)`, level 63): thin rows are paid; if every row that is not
  thin scores `≥ 63`, every row scores exactly 63, a complete head of a thin root would score
  `≥ 65`, so no row is thin, every two-ball has `≥ 19` labels and Seymour (`reach_seymour`)
  gives a four-ball of `≥ 37`, i.e. a three-ball of `≤ 26` at a row that is not thin.
* `no63_of_fat` (`q = 7`, level 64): the same, with the endgame law `End63` (a row that is not
  thin with score 64 and `|B 4| ≥ 37` forces some row to score `≥ 65`; paper, Appendix 29).

So each order reduces to its *fat savers*: rows that are not thin and fall below the level
(`54`: `(|B2|,|B3|) = (≥19, 27)`; `62`: `(|B3|,|B4|) = (27, 35)`; `63`: `(27,35)`, `(27,36)`,
`(28,35)`; `72`: `|B4| = 36`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TopRow
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)
open ThinSuppliers (Thin complete complete_subset x_heads_r complete_count complete_ball
  supplier_gain twins_gap_r)

variable {D : CH.Digraph} {q : ℕ}

/-! ### Growth from the first layer -/

/-- In a `q`-free set of minimum out-degree one, `min (d + k) (q + 1) ≤ |B k x|` for `k ≥ 1`,
`d` the number of heads of `x`. -/
theorem grow_from {S : Finset ℕ} {x : ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) (hx : x ∈ S) :
    ∀ k, 1 ≤ k → min ((outN D S x).card + k) (q + 1) ≤ (ball D S x k).card := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [ReachLedger.ball_one free hq hx]
    omega
  | succ k hk ih =>
    have sub : ball D S x k ⊆ ball D S x (k+1) := ball_mono_radius (Nat.le_succ k)
    have le := card_le_card sub
    by_cases big : q + 1 ≤ (ball D S x k).card
    · omega
    · by_contra small
      have eq : ball D S x k = ball D S x (k+1) := eq_of_subset_of_card_le sub (by omega)
      have closed : ∀ v ∈ ball D S x k, outN D (ball D S x k) v = outN D S v := by
        intro v hv
        ext w
        simp only [mem_outN]
        constructor
        · exact fun h => ⟨ball_subset h.1, h.2⟩
        · exact fun h => ⟨eq ▸ ball_step hv h.1 h.2, h.2⟩
      have order := DipCost.order_one q D (ball D S x k) (free.mono_set ball_subset)
        (fun v hv => by rw [closed v hv]; exact deg v (ball_subset hv)) ⟨x, self_mem_ball hx⟩
      omega

/-! ### The sharp thin count -/

section count
variable {V : Finset ℕ}

/-- **No short thin root, sharp supplier bound.** `3 ≤ q`, `r ≤ 2q - 1`, radii `i + j ≤ q`,
`2 ≤ i`, `2 ≤ j`. Rows that are not thin reach the level `|V| + 1`; thin rows fall short by at
most `δ`; every short thin row `v` has, for every `1 ≤ s ≤ r`,
`|V| + 1 + s + 2r ≤ |B (i+1) v| + |B (j+1) v| + min (s + i - 1) (q + 1) + min (s + j - 1) (q + 1)`;
and `m (δ + 1) < m² + (2q + 2 - r)` for every `m`. Then every thin row reaches the level.
Savers: the short thin roots; classes: second layers; banks: complete heads; `π = 1`. -/
theorem no_short_thin_sharp {r i j δ : ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q) (reg : ∀ v ∈ V, (outN D V v).card = r) (hij : i + j ≤ q)
    (hi : 2 ≤ i) (hj : 2 ≤ j)
    (fat : ∀ v ∈ V, ¬ Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card)
    (short : ∀ v ∈ V, Thin D V r v →
      V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card + δ)
    (bankrow : ∀ v ∈ V, Thin D V r v →
      (ball D V v i).card + (ball D V v j).card < V.card + 1 → ∀ s, 1 ≤ s → s ≤ r →
      V.card + 1 + s + 2 * r ≤ (ball D V v (i + 1)).card + (ball D V v (j + 1)).card +
        min (s + (i - 1)) (q + 1) + min (s + (j - 1)) (q + 1))
    (pay : ∀ m, m * (δ + 1) < m * m + (2 * q + 2 - r)) :
    ∀ v ∈ V, Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card := by
  classical
  set S := V.filter (fun v => Thin D V r v ∧
    (ball D V v i).card + (ball D V v j).card < V.card + 1) with hS
  set cls : ℕ → ℕ := fun u => (S.filter (fun w => layer D V 2 w = layer D V 2 u)).sup id
    with hcls
  have rep : ∀ u ∈ S, cls u ∈ S ∧ layer D V 2 (cls u) = layer D V 2 u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (S.filter (fun w => layer D V 2 w = layer D V 2 u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : cls u = w := he
    rw [this]
    exact mem_filter.mp hw
  have cong : ∀ u u', layer D V 2 u = layer D V 2 u' → cls u = cls u' := by
    intro u u' h
    simp only [hcls, h]
  have sv : S ⊆ V := filter_subset _ _
  have ofS : ∀ u ∈ S, u ∈ V ∧ Thin D V r u ∧
      (ball D V u i).card + (ball D V u j).card < V.card + 1 := fun u hu => mem_filter.mp hu
  have empty : S = ∅ := by
    refine BankCount.bank_count (b := 2 * q + 2 - r) (cls := cls)
      (bank := fun c => complete D V c) (π := 1) (δ := δ) free hij sv
      (fun u _ => complete_subset.trans outN_subset)
      (fun u hu => ?_) (fun u hu => ?_) (fun v hv vS => ?_) (fun x hx hp => ?_)
      (fun u hu u' hu' hc ne => ?_) (fun m => by rw [mul_one]; exact pay m)
    · obtain ⟨wV, wt, -⟩ := ofS _ (rep u hu).1
      have := complete_count free (by omega) reg wV wt (by omega)
      omega
    · obtain ⟨uV, ut, -⟩ := ofS u hu
      exact short u uV ut
    · by_cases vt : Thin D V r v
      · by_contra low
        exact vS (mem_filter.mpr ⟨hv, vt, by omega⟩)
      · exact fat v hv vt
    · set R := (S.image cls).filter (fun c => x ∈ complete D V c) with hR
      change 0 < R.card at hp
      change V.card + 1 + 1 * R.card ≤ _
      have Rrep : ∀ c ∈ R, c ∈ S ∧ x ∈ complete D V c := by
        intro c hc
        obtain ⟨cI, xc⟩ := mem_filter.mp hc
        obtain ⟨u, hu, rfl⟩ := mem_image.mp cI
        exact ⟨(rep u hu).1, xc⟩
      have RV : R ⊆ V := fun c hc => sv (Rrep c hc).1
      have inj : ∀ c ∈ R, ∀ c' ∈ R, layer D V 2 c = layer D V 2 c' → c = c' := by
        intro c hc c' hc' e
        obtain ⟨u, hu, rfl⟩ := mem_image.mp (mem_filter.mp hc).1
        obtain ⟨u', hu', rfl⟩ := mem_image.mp (mem_filter.mp hc').1
        rw [(rep u hu).2, (rep u' hu').2] at e
        exact cong u u' e
      obtain ⟨c, hc⟩ := card_pos.mp hp
      obtain ⟨cS, xc⟩ := Rrep c hc
      obtain ⟨cV, ct, clow⟩ := ofS c cS
      have xX := complete_subset xc
      obtain ⟨b0, hb0⟩ := card_pos.mp (x_heads_r free (by omega) reg cV ct x xX)
      have gain := supplier_gain free hq reg hr RV (fun w hw => (ofS w (Rrep w hw).1).2.1)
        (fun w hw => (Rrep w hw).2) inj hc hb0
      have bi := complete_ball free (by omega) reg cV ct xc hb0 (j := i) (by omega) (by omega)
      have bj := complete_ball free (by omega) reg cV ct xc hb0 (j := j) (by omega) (by omega)
      have XV : outN D V c ⊆ V := outN_subset
      have b0X := (mem_outN.mp hb0).1
      have gi := grow_from (free.mono_set XV) (by omega) (x_heads_r free (by omega) reg cV ct)
        b0X (i - 1) (by omega)
      have gj := grow_from (free.mono_set XV) (by omega) (x_heads_r free (by omega) reg cV ct)
        b0X (j - 1) (by omega)
      have dle : (outN D (outN D V c) b0).card ≤ r := by
        rw [← reg c cV]
        exact card_le_card outN_subset
      have mi : min (R.card + (i - 1)) (q + 1) ≤
          min ((outN D (outN D V c) b0).card + (i - 1)) (q + 1) :=
        min_le_min_right _ (by omega)
      have mj : min (R.card + (j - 1)) (q + 1) ≤
          min ((outN D (outN D V c) b0).card + (j - 1)) (q + 1) :=
        min_le_min_right _ (by omega)
      have := bankrow c cV ct clow R.card hp (by omega)
      omega
    · have same : layer D V 2 u = layer D V 2 u' := by
        rw [← (rep u hu).2, ← (rep u' hu').2, hc]
      exact twins_gap_r free (by omega) reg (sv hu) (sv hu') (Ne.symm ne) same
        (by omega) (by omega)
  intro v hv vt
  by_contra low
  have : v ∈ S := mem_filter.mpr ⟨hv, vt, by omega⟩
  rw [empty] at this
  simp at this

/-- Every row at the level, with the ledger: every score is exactly the level and there is no
gap. -/
theorem all_at_level {i j : ℕ} (free : QFree D V q) (hij : i + j ≤ q)
    (lev : ∀ v ∈ V, V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card) :
    ∀ v ∈ V, (ball D V v i).card + (ball D V v j).card = V.card + 1 := by
  have L := ReachLedger.ledger (D := D) (V := V) free hij
  intro v hv
  by_contra ne
  have lt : ∑ _w ∈ V, (V.card + 1) < ∑ w ∈ V, ((ball D V w i).card + (ball D V w j).card) :=
    sum_lt_sum lev ⟨v, hv, by have := lev v hv; omega⟩
  rw [sum_const, smul_eq_mul, sum_add_distrib] at lt
  omega

/-- A complete head of a thin root scores at least `|B (i+1) u| + |B (j+1) u| + i + j - 2r + 1`
at radii `(i, j)` (`2 ≤ i, j`, `i, j ≤ q`). -/
theorem complete_score {u r i j : ℕ} (free : QFree D V q) (hq : 3 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = r) (hu : u ∈ V) (thin : Thin D V r u)
    (hi : 2 ≤ i) (hj : 2 ≤ j) (hiq : i ≤ q) (hjq : j ≤ q) {x : ℕ} (hx : x ∈ complete D V u) :
    (ball D V u (i + 1)).card + (ball D V u (j + 1)).card +
        min (1 + (i - 1)) (q + 1) + min (1 + (j - 1)) (q + 1) ≤
      (ball D V x i).card + (ball D V x j).card + 2 * r := by
  have xX := complete_subset hx
  obtain ⟨b0, hb0⟩ := card_pos.mp (x_heads_r free (by omega) reg hu thin x xX)
  have bi := complete_ball free (by omega) reg hu thin hx hb0 (j := i) (by omega) hiq
  have bj := complete_ball free (by omega) reg hu thin hx hb0 (j := j) (by omega) hjq
  have XV : outN D V u ⊆ V := outN_subset
  have b0X := (mem_outN.mp hb0).1
  have d1 := x_heads_r free (by omega) reg hu thin b0 b0X
  have gi := grow_from (free.mono_set XV) (by omega) (x_heads_r free (by omega) reg hu thin)
    b0X (i - 1) (by omega)
  have gj := grow_from (free.mono_set XV) (by omega) (x_heads_r free (by omega) reg hu thin)
    b0X (j - 1) (by omega)
  have mi : min (1 + (i - 1)) (q + 1) ≤
      min ((outN D (outN D V u) b0).card + (i - 1)) (q + 1) := min_le_min_right _ (by omega)
  have mj : min (1 + (j - 1)) (q + 1) ≤
      min ((outN D (outN D V u) b0).card + (j - 1)) (q + 1) := min_le_min_right _ (by omega)
  omega

/-- A thin root has a complete head (`r ≤ 2q`). -/
theorem complete_nonempty {u r : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = r) (hu : u ∈ V) (thin : Thin D V r u) (hr : r ≤ 2 * q) :
    (complete D V u).Nonempty := by
  have := complete_count free hq reg hu thin hr
  have r1 : 1 ≤ r := by unfold Thin at thin; omega
  exact card_pos.mp (by have := complete_subset (D := D) (V := V) (u := u); omega)

end count

/-! ### The instances at `r = 9` -/

section nine
variable {V : Finset ℕ}

theorem pay_le {δ b : ℕ} (h : ∀ m ≤ δ + 2, m * (δ + 1) < m * m + b) :
    ∀ m, m * (δ + 1) < m * m + b := by
  intro m
  rcases Nat.lt_or_ge m (δ + 3) with hm | hm
  · exact h m (by omega)
  · have : (δ + 2) * m ≤ m * m := by
      have := Nat.mul_le_mul_right m (show δ + 2 ≤ m by omega)
      linarith
    nlinarith

/-- **Order 54 reduces to the fat savers.** `q = 6`, `r = 9`, radii `(3, 3)`, level `55`.
Floors: `|B 3| ≥ 26` everywhere and `|B 4| ≥ 34` at thin rows with `|B 3| ≤ 27`. If every row
that is not thin has `|B 3| ≥ 28`, there is no such digraph. -/
theorem no54_of_fat (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 54)
    (f3 : ∀ v ∈ V, 26 ≤ (ball D V v 3).card)
    (f4thin : ∀ v ∈ V, Thin D V 9 v → (ball D V v 3).card ≤ 27 → 34 ≤ (ball D V v 4).card)
    (fat : ∀ v ∈ V, ¬ Thin D V 9 v → 28 ≤ (ball D V v 3).card) : False := by
  have thin := no_short_thin_sharp (i := 3) (j := 3) (δ := 3) free (by norm_num) (by norm_num)
    reg (by norm_num) (by norm_num) (by norm_num)
    (fun v hv nt => by have := fat v hv nt; omega)
    (fun v hv _ => by have := f3 v hv; omega)
    (fun v hv vt low s s1 s9 => by
      show V.card + 1 + s + 2 * 9 ≤ (ball D V v 4).card + (ball D V v 4).card +
        min (s + 2) 7 + min (s + 2) 7
      have := f4thin v hv vt (by omega)
      omega)
    (pay_le (fun m hm => by interval_cases m <;> norm_num))
  have L := ReachLedger.ledger (D := D) (V := V) (i := 3) (j := 3) free (by norm_num)
  have each : ∀ v ∈ V, 56 ≤ (ball D V v 3).card + (ball D V v 3).card := by
    intro v hv
    by_cases vt : Thin D V 9 v
    · have := thin v hv vt
      omega
    · have := fat v hv vt
      omega
  have s := sum_le_sum each
  rw [sum_const, smul_eq_mul, n, sum_add_distrib] at s
  rw [n] at L
  omega

/-- **Order 72 reduces to the fat savers.** `q = 8`, `r = 9`, radii `(4, 4)`, level `73`.
Floors: `|B 4| ≥ 35`, `|B 5| ≥ 43`. If every row that is not thin has `|B 4| ≥ 37`, there is no
such digraph. -/
theorem no72_of_fat (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 72)
    (f4 : ∀ v ∈ V, 35 ≤ (ball D V v 4).card)
    (f5 : ∀ v ∈ V, 43 ≤ (ball D V v 5).card)
    (fat : ∀ v ∈ V, ¬ Thin D V 9 v → 37 ≤ (ball D V v 4).card) : False := by
  have thin := no_short_thin_sharp (i := 4) (j := 4) (δ := 3) free (by norm_num) (by norm_num)
    reg (by norm_num) (by norm_num) (by norm_num)
    (fun v hv nt => by have := fat v hv nt; omega)
    (fun v hv _ => by have := f4 v hv; omega)
    (fun v hv vt low s s1 s9 => by
      show V.card + 1 + s + 2 * 9 ≤ (ball D V v 5).card + (ball D V v 5).card +
        min (s + 3) 9 + min (s + 3) 9
      have := f5 v hv
      omega)
    (pay_le (fun m hm => by interval_cases m <;> norm_num))
  have L := ReachLedger.ledger (D := D) (V := V) (i := 4) (j := 4) free (by norm_num)
  have each : ∀ v ∈ V, 74 ≤ (ball D V v 4).card + (ball D V v 4).card := by
    intro v hv
    by_cases vt : Thin D V 9 v
    · have := thin v hv vt
      omega
    · have := fat v hv vt
      omega
  have s := sum_le_sum each
  rw [sum_const, smul_eq_mul, n, sum_add_distrib] at s
  rw [n] at L
  omega

/-- Floors at `q = 7`, `r = 9` used by `no62_of_fat`, `no63_of_fat` (inclusive balls):
`|B 2| ≥ 18`, `|B 3| ≥ 26`, `|B 4| ≥ 34`, `|B 5| ≥ 41` everywhere; `|B 4| + |B 5| ≥ 76` at thin
rows; `|B 3| ≥ 27` at rows that are not thin. -/
structure Floors7 (D : CH.Digraph) (V : Finset ℕ) : Prop where
  f2 : ∀ v ∈ V, 18 ≤ (ball D V v 2).card
  f3 : ∀ v ∈ V, 26 ≤ (ball D V v 3).card
  f4 : ∀ v ∈ V, 34 ≤ (ball D V v 4).card
  f5 : ∀ v ∈ V, 41 ≤ (ball D V v 5).card
  thin45 : ∀ v ∈ V, Thin D V 9 v → 76 ≤ (ball D V v 4).card + (ball D V v 5).card
  fat3 : ∀ v ∈ V, ¬ Thin D V 9 v → 27 ≤ (ball D V v 3).card

/-- At `q = 7` with every row at the level `L + 1 ∈ {63, 64}`: no row is thin. A complete head of
a thin root scores at least `|B 4 u| + |B 5 u| + 7 - 18 ≥ 65`. -/
theorem no_thin7 {L : ℕ} (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (fl : Floors7 D V) (hL : L ≤ 63)
    (lev : ∀ v ∈ V, (ball D V v 3).card + (ball D V v 4).card = L + 1) :
    ∀ v ∈ V, ¬ Thin D V 9 v := by
  intro u hu thin
  obtain ⟨x, hx⟩ := complete_nonempty free (by norm_num) reg hu thin (by norm_num)
  have xV : x ∈ V := outN_subset (complete_subset hx)
  have sc := complete_score (i := 3) (j := 4) free (by norm_num) reg hu thin (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx
  have := fl.thin45 u hu thin
  have := lev x xV
  norm_num at sc
  omega

/-- Two-ball cards at `r = 9`. -/
theorem ball2_nine {q : ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) {v : ℕ} (hv : v ∈ V) :
    (ball D V v 2).card = (layer D V 2 v).card + 10 :=
  (ThinSuppliers.balls_by_layers free hq reg hv).2.1

/-- At `q = 7` with every row at the level `L + 1` and no thin row: some row has
`|B 4| ≥ 37` (Seymour on the two-step reach graph; every two-ball has `≥ 19` labels). -/
theorem seymour7 (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (fl : Floors7 D V) (ne : V.Nonempty) (nothin : ∀ v ∈ V, ¬ Thin D V 9 v) :
    ∃ v ∈ V, 37 ≤ (ball D V v 4).card := by
  by_contra none
  push Not at none
  have two : ∀ v ∈ V, 19 ≤ (ball D V v 2).card := by
    intro v hv
    have := fl.f2 v hv
    have := ball2_nine free (by norm_num) reg hv
    have := nothin v hv
    unfold Thin at this
    omega
  have := reach_seymour (k := 2) (f := 19) (A := 36) free (by norm_num) ne two
    (fun v hv => by show (ball D V v 4).card ≤ 36; have := none v hv; omega)
  omega

/-- **Order 62 reduces to the fat savers.** `q = 7`, radii `(3, 4)`, level `63`. If every row
that is not thin scores at least `63`, there is no such digraph: the thin rows are paid
(`no_short_thin_sharp`), every row then scores exactly `63` (`all_at_level`), no row is thin
(`no_thin7`), and Seymour gives a row with `|B 4| ≥ 37`, so `|B 3| ≤ 26 < 27`. -/
theorem no62_of_fat (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 62) (fl : Floors7 D V)
    (fat : ∀ v ∈ V, ¬ Thin D V 9 v → 63 ≤ (ball D V v 3).card + (ball D V v 4).card) :
    False := by
  have thin := no_short_thin_sharp (i := 3) (j := 4) (δ := 3) free (by norm_num) (by norm_num)
    reg (by norm_num) (by norm_num) (by norm_num)
    (fun v hv nt => by have := fat v hv nt; omega)
    (fun v hv _ => by have := fl.f3 v hv; have := fl.f4 v hv; omega)
    (fun v hv vt low s s1 s9 => by
      show V.card + 1 + s + 2 * 9 ≤ (ball D V v 4).card + (ball D V v 5).card +
        min (s + 2) 8 + min (s + 3) 8
      have := fl.thin45 v hv vt
      omega)
    (pay_le (fun m hm => by interval_cases m <;> norm_num))
  have lev := all_at_level (i := 3) (j := 4) free (by norm_num) (fun v hv => by
    by_cases vt : Thin D V 9 v
    · exact thin v hv vt
    · have := fat v hv vt; omega)
  rw [n] at lev
  have nothin := no_thin7 (L := 62) free reg fl (by norm_num) lev
  have ne : V.Nonempty := card_pos.mp (by omega)
  obtain ⟨v, hv, big⟩ := seymour7 free reg fl ne nothin
  have := lev v hv
  have := fl.fat3 v hv (nothin v hv)
  omega

/-- **The endgame law at 63** (paper, Appendix 29, last paragraph): a row that is not thin,
scores `64` and has `|B 4| ≥ 37` forces a row scoring at least `65`. -/
def End63 (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ v ∈ V, ¬ Thin D V 9 v → (ball D V v 3).card + (ball D V v 4).card = 64 →
    37 ≤ (ball D V v 4).card → ∃ y ∈ V, 65 ≤ (ball D V y 3).card + (ball D V y 4).card

/-- **Order 63 reduces to the fat savers and `End63`.** `q = 7`, radii `(3, 4)`, level `64`. -/
theorem no63_of_fat (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 63) (fl : Floors7 D V) (fin : End63 D V)
    (fat : ∀ v ∈ V, ¬ Thin D V 9 v → 64 ≤ (ball D V v 3).card + (ball D V v 4).card) :
    False := by
  have thin := no_short_thin_sharp (i := 3) (j := 4) (δ := 4) free (by norm_num) (by norm_num)
    reg (by norm_num) (by norm_num) (by norm_num)
    (fun v hv nt => by have := fat v hv nt; omega)
    (fun v hv _ => by have := fl.f3 v hv; have := fl.f4 v hv; omega)
    (fun v hv vt low s s1 s9 => by
      show V.card + 1 + s + 2 * 9 ≤ (ball D V v 4).card + (ball D V v 5).card +
        min (s + 2) 8 + min (s + 3) 8
      have := fl.thin45 v hv vt
      omega)
    (pay_le (fun m hm => by interval_cases m <;> norm_num))
  have lev := all_at_level (i := 3) (j := 4) free (by norm_num) (fun v hv => by
    by_cases vt : Thin D V 9 v
    · exact thin v hv vt
    · have := fat v hv vt; omega)
  rw [n] at lev
  have nothin := no_thin7 (L := 63) free reg fl (by norm_num) lev
  have ne : V.Nonempty := card_pos.mp (by omega)
  obtain ⟨v, hv, big⟩ := seymour7 free reg fl ne nothin
  obtain ⟨y, hy, sy⟩ := fin v hv (nothin v hv) (lev v hv) big
  have := lev y hy
  omega

end nine

#print axioms grow_from
#print axioms no_short_thin_sharp
#print axioms all_at_level
#print axioms complete_score
#print axioms no54_of_fat
#print axioms no72_of_fat
#print axioms no_thin7
#print axioms seymour7
#print axioms no62_of_fat
#print axioms no63_of_fat
end LeanCH.BR.TopRow
