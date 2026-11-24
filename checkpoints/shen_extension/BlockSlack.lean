import Mathlib.Tactic
import LeanCH.BR.BRq3Base

/-!
# Slack is conserved in block products (ideas 10 and 7, 18 November 2026)

Lean 4.35.0. Everything is generic in the cutoff `q`, the degree `R`, the in-degree `r` of the quotient, the
block sizes and the index type.

Part 1 (pure arithmetic, over an index `Finset S`; the `Fintype` case is `S = univ`).
* `sum_inSum`: if every index of `S` has exactly `r` in-neighbours in `S`, then the total quotient
  out-weight `∑ i, ∑ j with adj i j, w j` equals `r * N` (idea 7, exact form).
* `sum_slack`: under the same in-regularity, `∑ slack = (q r + 1) N - |S| (q R + 1)`.
* `sum_slack_boundary`: if moreover `|S| = q r + 1`, then `∑ slack = |S| (N - q R - 1)`.
* `sum_slack_univ`: the same identity for a `Fintype` index with `m = Fintype.card ι`.
* `card_ge_of_slack_nonneg` (corollary a): `|S| = q r + 1` and all slacks `≥ 0` give `q R + 1 ≤ N`.
* `card_ge_of_slack_nonneg_le`: the same with only `q r + 1 ≤ |S|`.
* `slack_eq_zero_of_boundary` (corollary b): if also `N = q R + 1` then every slack is `0`.
* `sum_slack_of_plus_two` (corollary c): if `N = q R + 2` then the slacks sum to `|S|`.
* `card_zero_slack_eq` (corollary c, counting form): if `N = q R + 2`, the number of blocks of slack `0`
  equals `∑ (slack - 1)` over the blocks of nonzero slack (no sign hypothesis needed).
* `slack_eq_one_of_no_zero`: if `N = q R + 2`, all slacks are `≥ 0` and none is `0`, then every slack is `1`.

Part 2 (the block product as an actual digraph on `V : Finset ℕ` with block map `blk`).
* `card_eq_sum_blocks`: `V.card` is the sum of the block sizes.
* `outdeg_split`: the out-degree of `x ∈ V` is its out-degree inside its block plus the sizes of the blocks
  `j ≠ blk x` with `adj (blk x) j`.
* `outdeg_split_irrefl`: if the quotient is irreflexive, the second term is `∑ j with adj (blk x) j, w j`.
* `block_free`: every block inherits `QFree … q` from `V`.
* `slack_nonneg_block`: if the conjecture (`Below q e`) holds at the block's required degree, the block's
  slack is `≥ 0`.
* `closure`: in-regular irreflexive quotient on at least `q r + 1` indices, nonempty blocks, `QFree D V q`,
  minimum out-degree `R` and `Below` at each block's required degree give `q R + 1 ≤ V.card`.
* `closure_uniform`: the same with the hypothesis `∀ e, 1 ≤ e → e ≤ R → Below q e`.
* `boundary_blocks`: under the hypotheses of `closure`, `V.card = q R + 1` forces every block to its own
  boundary, `w i = q * e i + 1` over `ℤ`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BlockSlack

open Finset LeanCH.BR.BRq2 LeanCH.BR.BRq3

section Arith

variable {ι : Type*} (adj : ι → ι → Prop) [DecidableRel adj] (w : ι → ℕ)

/-- Quotient out-weight of `i` inside the index set `S`: `∑ j ∈ S with adj i j, w j`. -/
def inSum (S : Finset ι) (i : ι) : ℕ := ∑ j ∈ S.filter (fun j => adj i j), w j

/-- Required inner out-degree of block `i`: `R - inSum`, over `ℤ`. -/
def req (S : Finset ι) (R : ℕ) (i : ι) : ℤ := (R : ℤ) - (inSum adj w S i : ℤ)

/-- Slack of block `i`: `w i - q * req i - 1`, over `ℤ`. -/
def slack (S : Finset ι) (q R : ℕ) (i : ι) : ℤ := (w i : ℤ) - (q : ℤ) * req adj w S R i - 1

/-- Swapping sums: under in-regularity on `S`, the total quotient out-weight is `r * N`. -/
theorem sum_inSum (S : Finset ι) (r : ℕ) (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) :
    ∑ i ∈ S, inSum adj w S i = r * ∑ j ∈ S, w j := by
  unfold inSum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hin j hj]

/-- The slack identity. -/
theorem sum_slack (S : Finset ι) (q R r : ℕ) (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) :
    ∑ i ∈ S, slack adj w S q R i
      = ((q : ℤ) * r + 1) * ((∑ i ∈ S, w i : ℕ) : ℤ) - (S.card : ℤ) * ((q : ℤ) * R + 1) := by
  have h := sum_inSum adj w S r hin
  have h' : (∑ i ∈ S, (inSum adj w S i : ℤ)) = (r : ℤ) * ∑ i ∈ S, (w i : ℤ) := by exact_mod_cast h
  have e : ∀ i, slack adj w S q R i
      = (w i : ℤ) + (q : ℤ) * (inSum adj w S i : ℤ) - ((q : ℤ) * R + 1) := by
    intro i; simp only [slack, req]; ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, h', Finset.sum_const, nsmul_eq_mul]
  push_cast; ring

/-- The slack identity at a boundary quotient `|S| = q r + 1`. -/
theorem sum_slack_boundary (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : S.card = q * r + 1) :
    ∑ i ∈ S, slack adj w S q R i
      = (S.card : ℤ) * (((∑ i ∈ S, w i : ℕ) : ℤ) - q * R - 1) := by
  rw [sum_slack adj w S q R r hin]
  have : (S.card : ℤ) = (q : ℤ) * r + 1 := by exact_mod_cast hm
  rw [this]; ring

/-- The slack identity over a `Fintype` index, `m = Fintype.card ι`. -/
theorem sum_slack_univ [Fintype ι] (q R r : ℕ)
    (hin : ∀ j, (univ.filter (fun i => adj i j)).card = r) :
    ∑ i, slack adj w univ q R i
      = ((q : ℤ) * r + 1) * ((∑ i, w i : ℕ) : ℤ) - (Fintype.card ι : ℤ) * ((q : ℤ) * R + 1) := by
  rw [sum_slack adj w univ q R r (fun j _ => hin j), card_univ]

/-- Corollary (a): nonnegative slacks over a boundary quotient give `q R + 1 ≤ N`. -/
theorem card_ge_of_slack_nonneg (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : S.card = q * r + 1)
    (hs : ∀ i ∈ S, 0 ≤ slack adj w S q R i) :
    q * R + 1 ≤ ∑ i ∈ S, w i := by
  have hsum := sum_slack_boundary adj w S q R r hin hm
  have hnn : 0 ≤ ∑ i ∈ S, slack adj w S q R i := Finset.sum_nonneg hs
  have hpos : (0 : ℤ) < S.card := by rw [hm]; push_cast; positivity
  by_contra hlt
  push Not at hlt
  have hneg : ((∑ i ∈ S, w i : ℕ) : ℤ) - q * R - 1 < 0 := by
    have : ((∑ i ∈ S, w i : ℕ) : ℤ) < (q : ℤ) * R + 1 := by exact_mod_cast hlt
    linarith
  have := mul_neg_of_pos_of_neg hpos hneg
  linarith

/-- Corollary (a), general size: `q r + 1 ≤ |S|` (rather than equality) and all slacks `≥ 0` still give
`q R + 1 ≤ N`. -/
theorem card_ge_of_slack_nonneg_le (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : q * r + 1 ≤ S.card)
    (hs : ∀ i ∈ S, 0 ≤ slack adj w S q R i) :
    q * R + 1 ≤ ∑ i ∈ S, w i := by
  have hsum := sum_slack adj w S q R r hin
  have hnn : 0 ≤ ∑ i ∈ S, slack adj w S q R i := Finset.sum_nonneg hs
  have hm' : (q : ℤ) * r + 1 ≤ (S.card : ℤ) := by exact_mod_cast hm
  by_contra hlt
  push Not at hlt
  have hN : ((∑ i ∈ S, w i : ℕ) : ℤ) + 1 ≤ (q : ℤ) * R + 1 := by
    have : ∑ i ∈ S, w i + 1 ≤ q * R + 1 := by omega
    exact_mod_cast this
  have hpos : (0 : ℤ) < (q : ℤ) * r + 1 := by positivity
  have hR : (0 : ℤ) ≤ (q : ℤ) * R + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hN hpos.le, mul_le_mul_of_nonneg_right hm' hR]

/-- Corollary (b): at `N = q R + 1`, nonnegative slacks are all zero. -/
theorem slack_eq_zero_of_boundary (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : S.card = q * r + 1)
    (hN : ∑ i ∈ S, w i = q * R + 1) (hs : ∀ i ∈ S, 0 ≤ slack adj w S q R i) :
    ∀ i ∈ S, slack adj w S q R i = 0 := by
  have hsum := sum_slack_boundary adj w S q R r hin hm
  rw [hN] at hsum
  push_cast at hsum
  have h0 : ∑ i ∈ S, slack adj w S q R i = 0 := by rw [hsum]; ring
  exact (Finset.sum_eq_zero_iff_of_nonneg hs).mp h0

/-- Corollary (c): at `N = q R + 2`, the slacks sum to `|S|`. -/
theorem sum_slack_of_plus_two (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : S.card = q * r + 1)
    (hN : ∑ i ∈ S, w i = q * R + 2) :
    ∑ i ∈ S, slack adj w S q R i = S.card := by
  rw [sum_slack_boundary adj w S q R r hin hm, hN]
  push_cast; ring

/-- Corollary (c), counting form: at `N = q R + 2`, the number of blocks of slack `0` equals the excess
`∑ (slack - 1)` over the blocks of nonzero slack. -/
theorem card_zero_slack_eq (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : S.card = q * r + 1)
    (hN : ∑ i ∈ S, w i = q * R + 2) :
    ((S.filter (fun i => slack adj w S q R i = 0)).card : ℤ)
      = ∑ i ∈ S.filter (fun i => slack adj w S q R i ≠ 0), (slack adj w S q R i - 1) := by
  have h2 := sum_slack_of_plus_two adj w S q R r hin hm hN
  have h1 : ∑ i ∈ S, (slack adj w S q R i - 1) = 0 := by
    rw [Finset.sum_sub_distrib, h2, Finset.sum_const, nsmul_eq_mul]; ring
  rw [← Finset.sum_filter_add_sum_filter_not S (fun i => slack adj w S q R i = 0)] at h1
  have hz : ∑ i ∈ S.filter (fun i => slack adj w S q R i = 0), (slack adj w S q R i - 1)
      = -((S.filter (fun i => slack adj w S q R i = 0)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
      Finset.sum_const, nsmul_eq_mul]; ring
  rw [hz] at h1
  linarith

/-- At `N = q R + 2` with nonnegative slacks and no block of slack `0`, every slack is `1`. -/
theorem slack_eq_one_of_no_zero (S : Finset ι) (q R r : ℕ)
    (hin : ∀ j ∈ S, (S.filter (fun i => adj i j)).card = r) (hm : S.card = q * r + 1)
    (hN : ∑ i ∈ S, w i = q * R + 2) (hs : ∀ i ∈ S, 0 ≤ slack adj w S q R i)
    (hnz : ∀ i ∈ S, slack adj w S q R i ≠ 0) :
    ∀ i ∈ S, slack adj w S q R i = 1 := by
  have h2 := sum_slack_of_plus_two adj w S q R r hin hm hN
  have h1 : ∑ i ∈ S, (slack adj w S q R i - 1) = 0 := by
    rw [Finset.sum_sub_distrib, h2, Finset.sum_const, nsmul_eq_mul]; ring
  have hge : ∀ i ∈ S, 0 ≤ slack adj w S q R i - 1 := by
    intro i hi
    have := hs i hi; have := hnz i hi
    omega
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg hge).mp h1 i hi
  linarith

end Arith

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Block `i` of `V`. -/
def B (V : Finset ℕ) (blk : ℕ → ι) (i : ι) : Finset ℕ := V.filter (fun x => blk x = i)

/-- Between different blocks, arcs follow the quotient `adj`. -/
def Follows (D : CH.Digraph) (V : Finset ℕ) (blk : ℕ → ι) (adj : ι → ι → Prop) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, blk x ≠ blk y → (D x y = true ↔ adj (blk x) (blk y))

/-- The conjecture at out-degree `e`, cutoff `q`, for every digraph and every nonempty set. -/
def Below (q e : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), U.Nonempty → QFree E U q → (∀ x ∈ U, e ≤ (outN E U x).card) →
    q * e + 1 ≤ U.card

theorem card_eq_sum_blocks (V : Finset ℕ) (blk : ℕ → ι) :
    V.card = ∑ i, (B V blk i).card :=
  card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)

/-- (2a) Out-degree splits into inner out-degree plus the sizes of the out-neighbouring other blocks. -/
theorem outdeg_split {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] (hF : Follows D V blk adj) {x : ℕ} (hx : x ∈ V) :
    (outN D V x).card = (outN D (B V blk (blk x)) x).card
      + ∑ j ∈ univ.filter (fun j => adj (blk x) j ∧ j ≠ blk x), (B V blk j).card := by
  rw [card_eq_sum_card_fiberwise (f := blk) (t := univ) (fun _ _ => mem_univ _)]
  have hterm : ∀ j, ((outN D V x).filter (fun y => blk y = j)).card
      = (if j = blk x then (outN D (B V blk (blk x)) x).card else 0)
        + (if adj (blk x) j ∧ j ≠ blk x then (B V blk j).card else 0) := by
    intro j
    by_cases hj : j = blk x
    · subst hj
      rw [ite_eq_left rfl, ite_eq_right (fun h => h.2 rfl), add_zero]
      congr 1
      ext y; simp only [outN, B, mem_filter]; tauto
    · rw [ite_eq_right hj, zero_add]
      split_ifs with ha
      · congr 1
        ext y; simp only [outN, B, mem_filter]
        constructor
        · rintro ⟨⟨hy, _⟩, h⟩; exact ⟨hy, h⟩
        · rintro ⟨hy, rfl⟩
          exact ⟨⟨hy, (hF x hx y hy (Ne.symm hj)).2 ha.1⟩, rfl⟩
      · rw [card_eq_zero, filter_eq_empty_iff]
        intro y hy hyj
        rw [mem_outN] at hy
        subst hyj
        exact ha ⟨(hF x hx y hy.1 (Ne.symm hj)).1 hy.2, hj⟩
  rw [sum_congr rfl (fun j _ => hterm j), sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ _),
    ← sum_filter]

/-- (2a) with an irreflexive quotient. -/
theorem outdeg_split_irrefl {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] (hF : Follows D V blk adj) (hirr : ∀ i, ¬ adj i i) {x : ℕ} (hx : x ∈ V) :
    (outN D V x).card = (outN D (B V blk (blk x)) x).card
      + inSum adj (fun i => (B V blk i).card) univ (blk x) := by
  rw [outdeg_split hF hx]
  unfold inSum
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, fun e => by subst e; exact hirr _ h⟩⟩

omit [Fintype ι] in
/-- (2b) Every block inherits cycle-freeness. -/
theorem block_free {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {q : ℕ} (hf : QFree D V q) (i : ι) :
    QFree D (B V blk i) q :=
  hf.mono_set (filter_subset _ _)

/-- Each block has nonnegative slack, given the conjecture at that block's required degree. -/
theorem slack_nonneg_block {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] {q R : ℕ} (hF : Follows D V blk adj) (hirr : ∀ i, ¬ adj i i)
    (free : QFree D V q) (hmin : ∀ x ∈ V, R ≤ (outN D V x).card) (i : ι) (hne : (B V blk i).Nonempty)
    (law : inSum adj (fun i => (B V blk i).card) univ i < R →
      Below q (R - inSum adj (fun i => (B V blk i).card) univ i)) :
    0 ≤ slack adj (fun i => (B V blk i).card) univ q R i := by
  simp only [slack, req]
  by_cases h : inSum adj (fun i => (B V blk i).card) univ i < R
  · have hb := law h D (B V blk i) hne (block_free free i) (fun x hx => by
      have hx' := mem_filter.mp hx
      have hs := outdeg_split_irrefl hF hirr hx'.1
      rw [hx'.2] at hs
      have := hmin x hx'.1
      omega)
    have hc : (((R - inSum adj (fun i => (B V blk i).card) univ i : ℕ)) : ℤ)
        = (R : ℤ) - (inSum adj (fun i => (B V blk i).card) univ i : ℤ) := by
      rw [Nat.cast_sub h.le]
    have hb' : (q : ℤ) * ((R - inSum adj (fun i => (B V blk i).card) univ i : ℕ) : ℤ) + 1
        ≤ ((B V blk i).card : ℤ) := by exact_mod_cast hb
    rw [hc] at hb'
    linarith
  · have hle : (R : ℤ) - (inSum adj (fun i => (B V blk i).card) univ i : ℤ) ≤ 0 := by
      push Not at h; have : (R : ℤ) ≤ (inSum adj (fun i => (B V blk i).card) univ i : ℤ) := by
        exact_mod_cast h
      linarith
    have hq : (q : ℤ) * ((R : ℤ) - (inSum adj (fun i => (B V blk i).card) univ i : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    have hc : (1 : ℤ) ≤ ((B V blk i).card : ℤ) := by exact_mod_cast hne.card_pos
    linarith

/-- (2c) The closure theorem: block products over an in-regular irreflexive quotient on `q r + 1`
indices (or more) satisfy the bound, given the conjecture at each block's required degree. -/
theorem closure {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] {q R r : ℕ} (hF : Follows D V blk adj) (hirr : ∀ i, ¬ adj i i)
    (free : QFree D V q) (hmin : ∀ x ∈ V, R ≤ (outN D V x).card) (hne : ∀ i, (B V blk i).Nonempty)
    (hin : ∀ j, (univ.filter (fun i => adj i j)).card = r) (hm : q * r + 1 ≤ Fintype.card ι)
    (law : ∀ i, inSum adj (fun i => (B V blk i).card) univ i < R →
      Below q (R - inSum adj (fun i => (B V blk i).card) univ i)) :
    q * R + 1 ≤ V.card := by
  rw [card_eq_sum_blocks V blk]
  exact card_ge_of_slack_nonneg_le adj (fun i => (B V blk i).card) univ q R r (fun j _ => hin j)
    (by rw [card_univ]; exact hm)
    (fun i _ => slack_nonneg_block hF hirr free hmin i (hne i) (law i))

/-- (2c) with the uniform hypothesis: the conjecture at every degree `1 ≤ e ≤ R`. -/
theorem closure_uniform {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] {q R r : ℕ} (hF : Follows D V blk adj) (hirr : ∀ i, ¬ adj i i)
    (free : QFree D V q) (hmin : ∀ x ∈ V, R ≤ (outN D V x).card) (hne : ∀ i, (B V blk i).Nonempty)
    (hin : ∀ j, (univ.filter (fun i => adj i j)).card = r) (hm : q * r + 1 ≤ Fintype.card ι)
    (law : ∀ e, 1 ≤ e → e ≤ R → Below q e) :
    q * R + 1 ≤ V.card :=
  closure hF hirr free hmin hne hin hm (fun _ h => law _ (by omega) (by omega))

/-- (2c), induction form (added in audit). `closure_uniform` allows `e = R`, and `Below q R` applied to `V` itself
already gives its conclusion, so it carries no content. Here the conjecture is used only at degrees strictly below
`R`; the price is that every index has an out-neighbour in the quotient. -/
theorem closure_below {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] {q R r : ℕ} (hF : Follows D V blk adj) (hirr : ∀ i, ¬ adj i i)
    (free : QFree D V q) (hmin : ∀ x ∈ V, R ≤ (outN D V x).card) (hne : ∀ i, (B V blk i).Nonempty)
    (hin : ∀ j, (univ.filter (fun i => adj i j)).card = r) (hm : q * r + 1 ≤ Fintype.card ι)
    (hout : ∀ i, ∃ j, adj i j)
    (law : ∀ e, 1 ≤ e → e < R → Below q e) :
    q * R + 1 ≤ V.card :=
  closure hF hirr free hmin hne hin hm (fun i h => by
    obtain ⟨j, hj⟩ := hout i
    have pos : 1 ≤ inSum adj (fun i => (B V blk i).card) univ i := by
      unfold inSum
      have one : 1 ≤ (B V blk j).card := Finset.card_pos.mpr (hne j)
      have le := Finset.single_le_sum (f := fun j => (B V blk j).card)
        (s := univ.filter (fun j => adj i j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      exact one.trans le
    exact law _ (by omega) (by omega))

/-- (2d) At `V.card = q R + 1` every block is at its own boundary: `w i = q * e i + 1` over `ℤ`. -/
theorem boundary_blocks {D : CH.Digraph} {V : Finset ℕ} {blk : ℕ → ι} {adj : ι → ι → Prop}
    [DecidableRel adj] {q R r : ℕ} (hF : Follows D V blk adj) (hirr : ∀ i, ¬ adj i i)
    (free : QFree D V q) (hmin : ∀ x ∈ V, R ≤ (outN D V x).card) (hne : ∀ i, (B V blk i).Nonempty)
    (hin : ∀ j, (univ.filter (fun i => adj i j)).card = r) (hm : Fintype.card ι = q * r + 1)
    (law : ∀ i, inSum adj (fun i => (B V blk i).card) univ i < R →
      Below q (R - inSum adj (fun i => (B V blk i).card) univ i))
    (hV : V.card = q * R + 1) (i : ι) :
    ((B V blk i).card : ℤ) = (q : ℤ) * req adj (fun i => (B V blk i).card) univ R i + 1 := by
  have h0 := slack_eq_zero_of_boundary adj (fun i => (B V blk i).card) univ q R r (fun j _ => hin j)
    (by rw [card_univ, hm]) (by rw [← card_eq_sum_blocks V blk, hV])
    (fun i _ => slack_nonneg_block hF hirr free hmin i (hne i) (law i)) i (mem_univ _)
  simp only [slack] at h0
  linarith

end Block

end LeanCH.BR.BlockSlack

#print axioms LeanCH.BR.BlockSlack.sum_inSum
#print axioms LeanCH.BR.BlockSlack.sum_slack
#print axioms LeanCH.BR.BlockSlack.sum_slack_boundary
#print axioms LeanCH.BR.BlockSlack.sum_slack_univ
#print axioms LeanCH.BR.BlockSlack.card_ge_of_slack_nonneg
#print axioms LeanCH.BR.BlockSlack.card_ge_of_slack_nonneg_le
#print axioms LeanCH.BR.BlockSlack.slack_eq_zero_of_boundary
#print axioms LeanCH.BR.BlockSlack.sum_slack_of_plus_two
#print axioms LeanCH.BR.BlockSlack.card_zero_slack_eq
#print axioms LeanCH.BR.BlockSlack.slack_eq_one_of_no_zero
#print axioms LeanCH.BR.BlockSlack.card_eq_sum_blocks
#print axioms LeanCH.BR.BlockSlack.outdeg_split
#print axioms LeanCH.BR.BlockSlack.outdeg_split_irrefl
#print axioms LeanCH.BR.BlockSlack.block_free
#print axioms LeanCH.BR.BlockSlack.slack_nonneg_block
#print axioms LeanCH.BR.BlockSlack.closure
#print axioms LeanCH.BR.BlockSlack.closure_uniform
#print axioms LeanCH.BR.BlockSlack.boundary_blocks
#print axioms LeanCH.BR.BlockSlack.closure_below
