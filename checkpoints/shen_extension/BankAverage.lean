import checkpoints.shen_extension.RetainedShortfall
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Averaging the shortfall over all banks of three labels

Let `D` have exact outdegree `r` on `V`, with no loops. Erase a set `B` of
three labels. A surviving row `u` keeps `r - |N⁺(u) ∩ B|` heads, so at quota
`r - 1` it is short by `|N⁺(u) ∩ B| - 1` (truncated). Summing this over all
rows and all banks gives an exact identity:

    Σ_B shortfall(V \ B) + |V| · C(r,3) = |V| · C(r,2) · (|V| - 3).

A pair of heads of `u` lies in `|V| - 3` banks that avoid `u`, and a bank
inside `N⁺(u)` was counted three times for a shortfall of two.

Consequently a floor `λ` on the shortfall of every such survivor graph gives

    λ · C(|V|,3) + |V| · C(r,3) ≤ |V| · C(r,2) · (|V| - 3).

At `|V| = 3r` this reads `λ (3r-1)(3r-2) ≤ r (r-1)(8r-7)`, which is below
`(r-1)(3r-1)(3r-2)`. So in the triangle case a shortfall floor of `r - 1` on
`3(r-1)` labels, or any floor above `r(r-1)(8r-7)/((3r-1)(3r-2))`, excludes
a host of degree `r` on `3r` labels. No cutoff other than three enters the
last step, because the banks have three labels.
-/

namespace LeanCH.BR.BankAverage
open Finset BRq2 BRq3 Closure.DeficitLevels

/-- A pair inside `W` lies in `|W| - 2` three-element subsets of `W`. -/
theorem triples_through_pair {W P : Finset ℕ} (sub : P ⊆ W) (two : P.card = 2) :
    ((W.powersetCard 3).filter (P ⊆ ·)).card = W.card - 2 := by
  classical
  have key : (W.powersetCard 3).filter (P ⊆ ·) = (W \ P).image (fun z => insert z P) := by
    ext B
    simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
    constructor
    · rintro ⟨⟨bw, three⟩, pb⟩
      have one : (B \ P).card = 1 := by rw [card_sdiff_of_subset pb]; omega
      obtain ⟨z, hz⟩ := card_eq_one.mp one
      have zm : z ∈ B \ P := by rw [hz]; exact mem_singleton_self z
      refine ⟨z, ⟨bw (mem_sdiff.mp zm).1, (mem_sdiff.mp zm).2⟩, ?_⟩
      calc insert z P = {z} ∪ P := insert_eq z P
        _ = (B \ P) ∪ P := by rw [hz]
        _ = B := sdiff_union_of_subset pb
    · rintro ⟨z, ⟨zw, zp⟩, rfl⟩
      exact ⟨⟨insert_subset zw sub, by rw [card_insert_of_notMem zp, two]⟩, subset_insert z P⟩
  rw [key, card_image_of_injOn, card_sdiff_of_subset sub, two]
  intro a ha b _ eq
  have am : a ∈ insert b P := by
    have : a ∈ insert a P := mem_insert_self a P
    rwa [show insert a P = insert b P from eq] at this
  rcases mem_insert.mp am with h | h
  · exact h
  · exact absurd h (mem_sdiff.mp (mem_coe.mp ha)).2

/-- Pairs of `O` inside the three-element subsets of `W`. -/
theorem pairs_in_triples {W O : Finset ℕ} (sub : O ⊆ W) :
    ∑ B ∈ W.powersetCard 3, ((O ∩ B).card).choose 2 = O.card.choose 2 * (W.card - 2) := by
  classical
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := W.powersetCard 3) (t := O.powersetCard 2) (r := fun B P => P ⊆ B)
  have left : ∀ B ∈ W.powersetCard 3,
      (bipartiteAbove (fun B P => P ⊆ B) (O.powersetCard 2) B).card = ((O ∩ B).card).choose 2 := by
    intro B _
    have eq : bipartiteAbove (fun B P => P ⊆ B) (O.powersetCard 2) B = (O ∩ B).powersetCard 2 := by
      ext P
      simp only [bipartiteAbove, mem_filter, mem_powersetCard, subset_inter_iff]
      tauto
    rw [eq, card_powersetCard]
  have right : ∀ P ∈ O.powersetCard 2,
      (bipartiteBelow (fun B P => P ⊆ B) (W.powersetCard 3) P).card = W.card - 2 := by
    intro P pm
    obtain ⟨po, two⟩ := mem_powersetCard.mp pm
    exact triples_through_pair (po.trans sub) two
  rw [sum_congr rfl left, sum_congr rfl right, sum_const, card_powersetCard, smul_eq_mul] at h
  exact h

/-- Three-element subsets of `W` that lie inside `O`. -/
theorem triples_inside {W O : Finset ℕ} (sub : O ⊆ W) :
    ∑ B ∈ W.powersetCard 3, ((O ∩ B).card).choose 3 = O.card.choose 3 := by
  classical
  have term : ∀ B ∈ W.powersetCard 3, ((O ∩ B).card).choose 3 = if B ⊆ O then 1 else 0 := by
    intro B bm
    have three := (mem_powersetCard.mp bm).2
    by_cases h : B ⊆ O
    · have full : (O ∩ B).card = 3 := by rw [inter_eq_right.mpr h, three]
      simp [h, full]
    · have lt : (O ∩ B).card < 3 := by
        rw [← three]
        exact card_lt_card (ssubset_of_subset_of_ne inter_subset_right
          (fun e => h (inter_eq_right.mp e)))
      simp [h, Nat.choose_eq_zero_of_lt lt]
  rw [sum_congr rfl term, ← card_filter]
  have eq : (W.powersetCard 3).filter (· ⊆ O) = O.powersetCard 3 := by
    ext B
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨_, c⟩, bo⟩; exact ⟨bo, c⟩
    · rintro ⟨bo, c⟩; exact ⟨⟨bo.trans sub, c⟩, bo⟩
  rw [eq, card_powersetCard]

/-- One row: its truncated excess over all banks that avoid it. -/
theorem row_sum {W O : Finset ℕ} (sub : O ⊆ W) :
    (∑ B ∈ W.powersetCard 3, ((O ∩ B).card - 1)) + O.card.choose 3 =
      O.card.choose 2 * (W.card - 2) := by
  rw [← triples_inside sub, ← pairs_in_triples sub, ← sum_add_distrib]
  apply sum_congr rfl
  intro B bm
  have three := (mem_powersetCard.mp bm).2
  have le : (O ∩ B).card ≤ 3 := three ▸ card_le_card inter_subset_right
  generalize (O ∩ B).card = c at le ⊢
  interval_cases c <;> decide

/-- **The exact sum of shortfalls over all banks of three labels.** -/
theorem bank_sum {D : CH.Digraph} {V : Finset ℕ} {r : ℕ} (reg : OutEq r D V)
    (loop : ∀ v ∈ V, D v v ≠ true) :
    (∑ B ∈ V.powersetCard 3, total (r-1) D (V \ B)) + V.card * r.choose 3 =
      V.card * (r.choose 2 * (V.card - 3)) := by
  classical
  have cost_eq : ∀ B ∈ V.powersetCard 3, ∀ u ∈ V \ B,
      cost (r-1) D (V \ B) u = (outN D V u ∩ B).card - 1 := by
    intro B _ u um
    have eq : outN D (V \ B) u = outN D V u \ B := by
      ext x; simp only [mem_outN, mem_sdiff]; tauto
    have part := card_sdiff_add_card_inter (outN D V u) B
    have deg := reg u (mem_sdiff.mp um).1
    unfold cost
    rw [eq]
    omega
  have swap : ∑ B ∈ V.powersetCard 3, total (r-1) D (V \ B) =
      ∑ u ∈ V, ∑ B ∈ (V.erase u).powersetCard 3, ((outN D V u ∩ B).card - 1) := by
    unfold total
    rw [sum_congr rfl (fun B bm => sum_congr rfl (cost_eq B bm))]
    apply sum_comm'
    intro B u
    simp only [mem_powersetCard, mem_sdiff]
    constructor
    · rintro ⟨⟨bv, c⟩, uv, ub⟩
      exact ⟨⟨fun x xb => mem_erase.mpr ⟨fun e => ub (e ▸ xb), bv xb⟩, c⟩, uv⟩
    · rintro ⟨⟨be, c⟩, uv⟩
      exact ⟨⟨fun x xb => (mem_erase.mp (be xb)).2, c⟩, uv,
        fun ub => (mem_erase.mp (be ub)).1 rfl⟩
  have row : ∀ u ∈ V, (∑ B ∈ (V.erase u).powersetCard 3, ((outN D V u ∩ B).card - 1)) +
      r.choose 3 = r.choose 2 * (V.card - 3) := by
    intro u uv
    have sub : outN D V u ⊆ V.erase u := by
      intro x xm
      obtain ⟨xv, ux⟩ := mem_outN.mp xm
      refine mem_erase.mpr ⟨fun e => ?_, xv⟩
      rw [e] at ux
      exact loop u uv ux
    have h := row_sum sub
    rw [reg u uv, card_erase_of_mem uv] at h
    have shift : V.card - 1 - 2 = V.card - 3 := by omega
    rw [shift] at h
    exact h
  have all := sum_congr rfl row
  rw [sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at all
  rw [swap]
  exact all

/-- A common floor on the shortfall of every survivor graph bounds it by the average. -/
theorem floor_bound {D : CH.Digraph} {V : Finset ℕ} {r lam : ℕ} (reg : OutEq r D V)
    (loop : ∀ v ∈ V, D v v ≠ true)
    (floor : ∀ B ∈ V.powersetCard 3, lam ≤ total (r-1) D (V \ B)) :
    lam * V.card.choose 3 + V.card * r.choose 3 ≤ V.card * (r.choose 2 * (V.card - 3)) := by
  rw [← bank_sum reg loop]
  apply Nat.add_le_add_right
  calc lam * V.card.choose 3 = ∑ _B ∈ V.powersetCard 3, lam := by
        rw [sum_const, card_powersetCard, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := sum_le_sum floor

/-- Every digraph on a nonempty set of at most `q t` labels with no directed
cycle of length at most `q` has total shortfall at least `lam` at quota `t`.
With `lam = 1` this is the absence of a host, and with `lam = 2` also of a
near-host. The empty set is left out, because it has zero shortfall. -/
def ShortfallFloor (q t lam : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), U.Nonempty → U.card ≤ q * t → QFree E U q →
    lam ≤ total t E U

/-- The floor on every bank of a host with `3 r` labels. -/
theorem floor_on_banks {D : CH.Digraph} {V : Finset ℕ} {r lam : ℕ} (free : QFree D V 3)
    (size : V.card = 3 * r) (two : 2 ≤ r) (law : ShortfallFloor 3 (r-1) lam) :
    ∀ B ∈ V.powersetCard 3, lam ≤ total (r-1) D (V \ B) := by
  intro B bm
  obtain ⟨bv, three⟩ := mem_powersetCard.mp bm
  have left : (V \ B).card = 3 * r - 3 := by rw [card_sdiff_of_subset bv, three, size]
  exact law D (V \ B) (card_pos.mp (by omega)) (by omega) (free.mono_set sdiff_subset)

/-- The open triangle family `n = 30`, degree ten: a shortfall floor of nine
on `27` labels at quota nine excludes it. -/
theorem thirty_ten {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 3) (reg : OutEq 10 D V)
    (size : V.card = 30) (law : ShortfallFloor 3 9 9) : False := by
  have loop : ∀ v ∈ V, D v v ≠ true := fun v vm => loopfree free (by decide) vm
  have bound := floor_bound reg loop (floor_on_banks (r := 10) free size (by decide) law)
  rw [size] at bound
  revert bound
  decide

theorem two_choose (m : ℕ) : 2 * (m+1).choose 2 = (m+1) * m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have step : (k+2).choose 2 = (k+1).choose 1 + (k+1).choose 2 := Nat.choose_succ_succ' (k+1) 1
    rw [step, Nat.choose_one_right]
    nlinarith

private theorem six_choose (m : ℕ) : 6 * (m+2).choose 3 = (m+2) * (m+1) * m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have step : (k+3).choose 3 = (k+2).choose 2 + (k+2).choose 3 := Nat.choose_succ_succ' (k+2) 2
    have pair := two_choose (k+1)
    rw [step]
    nlinarith

/-- **Triangle case at `n = 3 r`.** A shortfall floor on `3 (r-1)` labels at
quota `r - 1` that exceeds the average over all banks excludes a host of
exact degree `r` on `3 r` labels. The floor `r - 1` qualifies for every
`r ≥ 2`, and from `r = 11` on a smaller floor does. -/
theorem triangle_order {D : CH.Digraph} {V : Finset ℕ} {r lam : ℕ} (free : QFree D V 3)
    (reg : OutEq r D V) (two : 2 ≤ r) (size : V.card = 3 * r) (law : ShortfallFloor 3 (r-1) lam)
    (strong : r * (r-1) * (8*r-7) < lam * ((3*r-1) * (3*r-2))) : False := by
  have loop : ∀ v ∈ V, D v v ≠ true := fun v vm => loopfree free (by decide) vm
  have bound := floor_bound reg loop (floor_on_banks free size two law)
  rw [size] at bound
  rcases r with _ | _ | j
  · omega
  · omega
  · have e1 : j + 1 + 1 - 1 = j + 1 := by omega
    have e2 : 8 * (j + 1 + 1) - 7 = 8 * j + 9 := by omega
    have e3 : 3 * (j + 1 + 1) - 1 = 3 * j + 5 := by omega
    have e4 : 3 * (j + 1 + 1) - 2 = 3 * j + 4 := by omega
    have e5 : 3 * (j + 1 + 1) - 3 = 3 * j + 3 := by omega
    have e6 : 3 * (j + 1 + 1) = (3 * j + 4) + 2 := by omega
    rw [e1, e2, e3, e4] at strong
    rw [e5, e6] at bound
    have big := six_choose (3 * j + 4)
    have small := six_choose j
    have pair := two_choose (j + 1)
    have s1 : j + 1 + 1 = j + 2 := rfl
    rw [s1] at bound strong
    have t1 : j + 1 + 1 = j + 2 := rfl
    nlinarith [bound, strong, big, small, pair, Nat.zero_le lam, Nat.zero_le j,
      Nat.zero_le ((3 * j + 4 + 2).choose 3), Nat.zero_le ((j + 2).choose 3),
      Nat.zero_le ((j + 2).choose 2)]

/-! ### Banks of two labels

The same count for pairs. A surviving row is short at quota `r - 1` exactly
when both erased labels are its heads, so the shortfalls of all pair banks
add up to `|V| · C(r,2)`. On a carrier of at most `q (r-1) + 2` labels every
survivor graph is small enough for the lower-quota laws. -/

/-- One row: the pair banks avoiding it that lie inside its heads. -/
theorem pair_row {W O : Finset ℕ} (sub : O ⊆ W) :
    ∑ B ∈ W.powersetCard 2, ((O ∩ B).card - 1) = O.card.choose 2 := by
  classical
  have term : ∀ B ∈ W.powersetCard 2, ((O ∩ B).card - 1) = if B ⊆ O then 1 else 0 := by
    intro B bm
    have two := (mem_powersetCard.mp bm).2
    by_cases h : B ⊆ O
    · have full : (O ∩ B).card = 2 := by rw [inter_eq_right.mpr h, two]
      simp [h, full]
    · have lt : (O ∩ B).card < 2 := by
        rw [← two]
        exact card_lt_card (ssubset_of_subset_of_ne inter_subset_right
          (fun e => h (inter_eq_right.mp e)))
      have zero : (O ∩ B).card - 1 = 0 := by omega
      simp [h, zero]
  rw [sum_congr rfl term, ← card_filter]
  have eq : (W.powersetCard 2).filter (· ⊆ O) = O.powersetCard 2 := by
    ext B
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨_, c⟩, bo⟩; exact ⟨bo, c⟩
    · rintro ⟨bo, c⟩; exact ⟨⟨bo.trans sub, c⟩, bo⟩
  rw [eq, card_powersetCard]

/-- **The exact sum of shortfalls over all banks of two labels.** -/
theorem pair_bank_sum {D : CH.Digraph} {V : Finset ℕ} {r : ℕ} (reg : OutEq r D V)
    (loop : ∀ v ∈ V, D v v ≠ true) :
    ∑ B ∈ V.powersetCard 2, total (r-1) D (V \ B) = V.card * r.choose 2 := by
  classical
  have cost_eq : ∀ B ∈ V.powersetCard 2, ∀ u ∈ V \ B,
      cost (r-1) D (V \ B) u = (outN D V u ∩ B).card - 1 := by
    intro B _ u um
    have eq : outN D (V \ B) u = outN D V u \ B := by
      ext x; simp only [mem_outN, mem_sdiff]; tauto
    have part := card_sdiff_add_card_inter (outN D V u) B
    have deg := reg u (mem_sdiff.mp um).1
    unfold cost
    rw [eq]
    omega
  have swap : ∑ B ∈ V.powersetCard 2, total (r-1) D (V \ B) =
      ∑ u ∈ V, ∑ B ∈ (V.erase u).powersetCard 2, ((outN D V u ∩ B).card - 1) := by
    unfold total
    rw [sum_congr rfl (fun B bm => sum_congr rfl (cost_eq B bm))]
    apply sum_comm'
    intro B u
    simp only [mem_powersetCard, mem_sdiff]
    constructor
    · rintro ⟨⟨bv, c⟩, uv, ub⟩
      exact ⟨⟨fun x xb => mem_erase.mpr ⟨fun e => ub (e ▸ xb), bv xb⟩, c⟩, uv⟩
    · rintro ⟨⟨be, c⟩, uv⟩
      exact ⟨⟨fun x xb => (mem_erase.mp (be xb)).2, c⟩, uv,
        fun ub => (mem_erase.mp (be ub)).1 rfl⟩
  have row : ∀ u ∈ V, ∑ B ∈ (V.erase u).powersetCard 2, ((outN D V u ∩ B).card - 1) =
      r.choose 2 := by
    intro u uv
    have sub : outN D V u ⊆ V.erase u := by
      intro x xm
      obtain ⟨xv, ux⟩ := mem_outN.mp xm
      refine mem_erase.mpr ⟨fun e => ?_, xv⟩
      rw [e] at ux
      exact loop u uv ux
    rw [pair_row sub, reg u uv]
  rw [swap, sum_congr rfl row, sum_const, smul_eq_mul]

/-- A common floor on the shortfall left by every pair bank bounds the order. -/
theorem pair_floor_order {D : CH.Digraph} {V : Finset ℕ} {r lam : ℕ} (reg : OutEq r D V)
    (loop : ∀ v ∈ V, D v v ≠ true) (hr : 1 ≤ r) (live : 1 ≤ V.card)
    (floor : ∀ B ∈ V.powersetCard 2, lam ≤ total (r-1) D (V \ B)) :
    lam * (V.card - 1) ≤ r * (r - 1) := by
  have bound : lam * V.card.choose 2 ≤ V.card * r.choose 2 := by
    rw [← pair_bank_sum reg loop]
    calc lam * V.card.choose 2 = ∑ _B ∈ V.powersetCard 2, lam := by
          rw [sum_const, card_powersetCard, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := sum_le_sum floor
  obtain ⟨m, hm⟩ : ∃ m, V.card = m + 1 := ⟨V.card - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [hm] at bound ⊢
  have c1 := two_choose m
  have c2 := two_choose k
  have e1 : m + 1 - 1 = m := by omega
  have e2 : k + 1 - 1 = k := by omega
  rw [e1, e2]
  have scaled : (m + 1) * (lam * m) ≤ (m + 1) * ((k + 1) * k) := by nlinarith
  exact Nat.le_of_mul_le_mul_left scaled (by omega)

/-- At or below the unit-deficit band a shortfall floor bounds the order. -/
theorem band_floor_order {D : CH.Digraph} {V : Finset ℕ} {q r lam : ℕ} (free : QFree D V q)
    (hq : 1 ≤ q) (reg : OutEq r D V) (hr : 1 ≤ r) (three : 3 ≤ V.card)
    (order : V.card ≤ q * (r-1) + 2) (law : ShortfallFloor q (r-1) lam) :
    lam * (V.card - 1) ≤ r * (r - 1) := by
  refine pair_floor_order reg (fun v vm => loopfree free hq vm) hr (by omega) ?_
  intro B bm
  obtain ⟨bv, two⟩ := mem_powersetCard.mp bm
  have left : (V \ B).card = V.card - 2 := by rw [card_sdiff_of_subset bv, two]
  exact law D (V \ B) (card_pos.mp (by omega)) (by omega) (free.mono_set sdiff_subset)

/-- **With no host and no near-host one degree down**, a carrier of at most
`q (r-1) + 2` labels satisfies `2 (|V| - 1) ≤ r (r - 1)`. At the band itself
this fails as soon as `2 q ≥ r`. -/
theorem near_band_order {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (hq : 1 ≤ q) (reg : OutEq r D V) (hr : 1 ≤ r) (three : 3 ≤ V.card)
    (order : V.card ≤ q * (r-1) + 2) (none : BypassRepair.NoHost q (r-1))
    (near : LoneRow.NoNearHost q (r-1)) : 2 * (V.card - 1) ≤ r * (r - 1) := by
  refine pair_floor_order reg (fun v vm => loopfree free hq vm) hr (by omega) ?_
  intro B bm
  obtain ⟨bv, two⟩ := mem_powersetCard.mp bm
  have size : (V \ B).card = V.card - 2 := by rw [card_sdiff_of_subset bv, two]
  exact ShortfallBridge.total_ge_two none near (free.mono_set sdiff_subset)
    (card_pos.mp (by omega)) (by omega)

/-- **A bank that leaves exactly one unit of shortfall.** With no host one
degree down, a carrier of at most `q (r-1) + 2` labels with
`r (r-1) < 2 (|V| - 1)` has a pair of labels whose removal leaves total
shortfall one. At the band this holds whenever `2 q ≥ r`. -/
theorem lone_bank {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (hq : 1 ≤ q) (reg : OutEq r D V) (hr : 1 ≤ r) (three : 3 ≤ V.card)
    (order : V.card ≤ q * (r-1) + 2) (none : BypassRepair.NoHost q (r-1))
    (wide : r * (r - 1) < 2 * (V.card - 1)) :
    ∃ B ∈ V.powersetCard 2, total (r-1) D (V \ B) = 1 := by
  by_contra absent
  push Not at absent
  have bound := pair_floor_order (lam := 2) reg (fun v vm => loopfree free hq vm) hr (by omega) (by
    intro B bm
    obtain ⟨bv, two⟩ := mem_powersetCard.mp bm
    have size : (V \ B).card = V.card - 2 := by rw [card_sdiff_of_subset bv, two]
    have pos := ShortfallBridge.total_pos none (free.mono_set sdiff_subset)
      (card_pos.mp (by omega : 0 < (V \ B).card)) (by omega)
    have ne := absent B bm
    omega)
  omega

/-! ### Cutoff at least the degree

With no host one degree down, every two labels of a host on at most
`q (r-1) + 2` labels have a common parent: erasing a pair that has none
leaves a host of degree `r - 1` on at most `q (r-1)` labels. The rows supply
only `|V| · C(r,2)` pairs of heads, so `|V| - 1 ≤ r (r-1)`. When `r ≤ q` this
is below `q (r-1) + 1`, and the order is at least `q (r-1) + 3`. -/

/-- Every pair has a common parent, so the pairs of heads cover all pairs. -/
theorem host_band_order {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (hq : 1 ≤ q) (reg : OutEq r D V) (hr : 1 ≤ r) (three : 3 ≤ V.card)
    (order : V.card ≤ q * (r-1) + 2) (none : BypassRepair.NoHost q (r-1)) :
    V.card - 1 ≤ r * (r - 1) := by
  have bound := pair_floor_order (lam := 1) reg (fun v vm => loopfree free hq vm) hr (by omega) (by
    intro B bm
    obtain ⟨bv, two⟩ := mem_powersetCard.mp bm
    have size : (V \ B).card = V.card - 2 := by rw [card_sdiff_of_subset bv, two]
    exact ShortfallBridge.total_pos none (free.mono_set sdiff_subset)
      (card_pos.mp (by omega)) (by omega))
  omega

/-- **Cutoff at least the degree.** A `q`-free graph with minimum outdegree
`r`, `2 ≤ r ≤ q`, and no host one degree down has at least `q (r-1) + 3`
labels. -/
theorem wide_cutoff_order {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (live : V.Nonempty) (hr : 2 ≤ r) (wide : r ≤ q)
    (none : BypassRepair.NoHost q (r-1)) : q * (r-1) + 3 ≤ V.card := by
  classical
  by_contra small
  obtain ⟨F, sub, reg⟩ := exists_outEq deg
  have ff : QFree F V q := qfree_sub sub free
  obtain ⟨v, vm⟩ := live
  have inside : outN F V v ⊆ V.erase v := by
    intro x xm
    obtain ⟨xv, vx⟩ := mem_outN.mp xm
    exact mem_erase.mpr ⟨fun e => loopfree ff (by omega) vm (e ▸ vx), xv⟩
  have big : r + 1 ≤ V.card := by
    have := card_le_card inside
    rw [reg v vm, card_erase_of_mem vm] at this
    have := card_pos.mpr ⟨v, vm⟩
    omega
  have pairs := host_band_order ff (by omega) reg (by omega) (by omega) (by omega) none
  have mul : r * (r - 1) ≤ q * (r - 1) := Nat.mul_le_mul_right _ wide
  -- so one deletion already leaves at most `q (r-1)` labels
  refine none F (V.erase v) (card_pos.mp (by rw [card_erase_of_mem vm]; omega))
    (by rw [card_erase_of_mem vm]; omega) (ff.mono_set (erase_subset _ _)) ?_
  intro u um
  have uv := (mem_erase.mp um).2
  have cover : outN F V u ⊆ insert v (outN F (V.erase v) u) := by
    intro x xm
    obtain ⟨xv, ux⟩ := mem_outN.mp xm
    by_cases e : x = v
    · exact e ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, xv⟩, ux⟩)
  have := (card_le_card cover).trans (card_insert_le _ _)
  rw [reg u uv] at this
  omega

/-! ### What the natural floor one degree down closes

The natural floor is `ShortfallFloor q t t`: on `q t` labels the shortfall is
at least `t`, the value left by an extremal graph on `q t + 1` labels after
one deletion. Assumed at quota `r - 1`, it excludes a host of degree `r`
on at most `q (r-1) + 2` labels for every cutoff, on `q (r-1) + 3` labels
for cutoff at least four, and on every order up to `3 r` for cutoff three.
The floor itself is not proved here. -/

/-- A floor of at least one excludes hosts. -/
theorem noHost_of_floor {q t lam : ℕ} (pos : 1 ≤ lam) (law : ShortfallFloor q t lam) :
    BypassRepair.NoHost q t := by
  intro E U live small free deg
  have low := law E U live small free
  have zero : total t E U = 0 := by
    unfold total
    exact sum_eq_zero fun v vm => by
      have := deg v vm
      unfold cost
      omega
  omega

/-- A floor of at least two excludes a child with one unit of shortfall. -/
theorem lone_of_floor {D : CH.Digraph} {U : Finset ℕ} {q t lam : ℕ} (two : 2 ≤ lam)
    (law : ShortfallFloor q t lam) (free : QFree D U q) (live : U.Nonempty)
    (small : U.card ≤ q * t) (unit : total t D U = 1) : False := by
  have := law D U live small free
  omega

/-- One deletion: with no host one degree down the order is at least `q (r-1) + 2`. -/
theorem above_lower_order {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (hq : 1 ≤ q) (reg : OutEq r D V) (hr : 2 ≤ r) (live : V.Nonempty)
    (none : BypassRepair.NoHost q (r-1)) : q * (r-1) + 2 ≤ V.card := by
  classical
  by_contra small
  obtain ⟨v, vm⟩ := live
  have inside : outN D V v ⊆ V.erase v := by
    intro x xm
    obtain ⟨xv, vx⟩ := mem_outN.mp xm
    exact mem_erase.mpr ⟨fun e => loopfree free hq vm (e ▸ vx), xv⟩
  have big : r + 1 ≤ V.card := by
    have := card_le_card inside
    rw [reg v vm, card_erase_of_mem vm] at this
    have := card_pos.mpr ⟨v, vm⟩
    omega
  refine none D (V.erase v) (card_pos.mp (by rw [card_erase_of_mem vm]; omega))
    (by rw [card_erase_of_mem vm]; omega) (free.mono_set (erase_subset _ _)) ?_
  intro u um
  have uv := (mem_erase.mp um).2
  have cover : outN D V u ⊆ insert v (outN D (V.erase v) u) := by
    intro x xm
    obtain ⟨xv, ux⟩ := mem_outN.mp xm
    by_cases e : x = v
    · exact e ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, xv⟩, ux⟩)
  have := (card_le_card cover).trans (card_insert_le _ _)
  rw [reg u uv] at this
  omega

/-- **The pair band, every cutoff.** Under the natural floor one degree down
no host of degree `r` has between `r + 2` and `q (r-1) + 2` labels. -/
theorem floor_band {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (reg : OutEq r D V) (hr : 2 ≤ r) (lo : r + 2 ≤ V.card) (order : V.card ≤ q * (r-1) + 2)
    (law : ShortfallFloor q (r-1) (r-1)) : False := by
  have bound := band_floor_order free hq reg (by omega) (by omega) order law
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  have e : k + 2 - 1 = k + 1 := by omega
  rw [e] at bound
  have wide : (k + 1) * (k + 3) ≤ (k + 1) * (V.card - 1) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Triple banks, cutoff at least four.** Under the natural floor one degree
down no host of degree `r` has between `4 (r-1) + 3` and `q (r-1) + 3` labels. -/
theorem floor_third {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (reg : OutEq r D V) (hr : 2 ≤ r) (lo : 4 * (r-1) + 3 ≤ V.card)
    (order : V.card ≤ q * (r-1) + 3) (law : ShortfallFloor q (r-1) (r-1)) : False := by
  have loop : ∀ v ∈ V, D v v ≠ true := fun v vm => loopfree free hq vm
  have bound := floor_bound (lam := r - 1) reg loop (by
    intro B bm
    obtain ⟨bv, three⟩ := mem_powersetCard.mp bm
    have left : (V \ B).card = V.card - 3 := by rw [card_sdiff_of_subset bv, three]
    exact law D (V \ B) (card_pos.mp (by omega)) (by omega) (free.mono_set sdiff_subset))
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, V.card = m + 3 := ⟨V.card - 3, by omega⟩
  have e : k + 2 - 1 = k + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [hm, e, e3] at bound
  rw [hm, e] at lo
  have big := six_choose (m + 1)
  have small := six_choose k
  have pair := two_choose (k + 1)
  have s1 : m + 1 + 2 = m + 3 := rfl
  have s2 : k + 1 + 1 = k + 2 := rfl
  rw [s1] at big
  rw [s2] at pair
  -- clear the binomials: (k+1)(m+2)(m+1) + (k+2)(k+1)k ≤ 3 (k+2)(k+1) m
  have six : (k + 1) * (6 * (m + 3).choose 3) + (m + 3) * (6 * (k + 2).choose 3) ≤
      (m + 3) * (3 * (2 * (k + 2).choose 2) * m) := by
    have l : (k + 1) * (6 * (m + 3).choose 3) + (m + 3) * (6 * (k + 2).choose 3) =
        6 * ((k + 1) * (m + 3).choose 3 + (m + 3) * (k + 2).choose 3) := by ring
    have r : (m + 3) * (3 * (2 * (k + 2).choose 2) * m) =
        6 * ((m + 3) * ((k + 2).choose 2 * m)) := by ring
    rw [l, r]
    exact Nat.mul_le_mul_left 6 bound
  rw [big, small, pair] at six
  have poly : (m + 3) * ((k + 1) * ((m + 2) * (m + 1)) + (k + 2) * (k + 1) * k) ≤
      (m + 3) * (3 * ((k + 2) * (k + 1)) * m) := by
    calc (m + 3) * ((k + 1) * ((m + 2) * (m + 1)) + (k + 2) * (k + 1) * k)
        = (k + 1) * ((m + 3) * (m + 1 + 1) * (m + 1)) + (m + 3) * ((k + 2) * (k + 1) * k) := by ring
      _ ≤ _ := six
  have core := Nat.le_of_mul_le_mul_left poly (by omega)
  have room : 3 * (k + 2) * m + m + 2 ≤ (m + 2) * (m + 1) := by
    nlinarith [Nat.mul_le_mul_right m (by omega : 3 * k + 7 ≤ m + 3)]
  have scaled := Nat.mul_le_mul_left (k + 1) room
  nlinarith [core, scaled, Nat.zero_le ((k + 2) * (k + 1) * k), Nat.zero_le (k * m), Nat.zero_le m]

/-- The diagonal of the triangle case under the natural floor. -/
theorem floor_triangle {D : CH.Digraph} {V : Finset ℕ} {r : ℕ} (free : QFree D V 3)
    (reg : OutEq r D V) (two : 2 ≤ r) (size : V.card = 3 * r)
    (law : ShortfallFloor 3 (r-1) (r-1)) : False := by
  refine triangle_order free reg two size law ?_
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : 8 * (k + 2) - 7 = 8 * k + 9 := by omega
  have e3 : 3 * (k + 2) - 1 = 3 * k + 5 := by omega
  have e4 : 3 * (k + 2) - 2 = 3 * k + 4 := by omega
  rw [e1, e2, e3, e4]
  have split : (k + 2) * (k + 1) * (8 * k + 9) + (k + 1) * (k * k + 2 * k + 2) =
      (k + 1) * ((3 * k + 5) * (3 * k + 4)) := by ring
  have pos : 0 < (k + 1) * (k * k + 2 * k + 2) := by positivity
  linarith

/-- **The whole triangle case from the floor one degree down.** A graph with
no directed cycle of length at most three and minimum outdegree `r ≥ 2` has
at least `3 r + 1` labels, provided every such graph on at most `3 (r-1)`
labels has shortfall at least `r - 1` at quota `r - 1`. -/
theorem triangle_of_floor {D : CH.Digraph} {V : Finset ℕ} {r : ℕ} (free : QFree D V 3)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (live : V.Nonempty) (two : 2 ≤ r)
    (law : ShortfallFloor 3 (r-1) (r-1)) : 3 * r + 1 ≤ V.card := by
  by_contra small
  obtain ⟨F, sub, reg⟩ := exists_outEq deg
  have ff : QFree F V 3 := qfree_sub sub free
  have low := above_lower_order ff (by decide) reg two live (noHost_of_floor (by omega) law)
  by_cases band : V.card ≤ 3 * (r-1) + 2
  · exact floor_band ff (by decide) reg two (by omega) band law
  · exact floor_triangle ff reg two (by omega) law

/-! ### The floor one quota up, on the smaller carriers

The natural floor at quota `t - 1` gives the natural floor at quota `t` on
every carrier of at most `q (t-1) + 1` labels. On at most `q (t-1)` labels a
row that is short at quota `t - 1` is short by one more at quota `t`. On
`q (t-1) + 1` labels, erase a row that is short at quota `t`: every other
row loses at most one head and one unit of quota, so the shortfall drops by
at least one. What remains open is the floor on carriers with between
`q (t-1) + 2` and `q t` labels. -/

/-- Erasing one label and lowering the quota by one does not raise a row's shortfall. -/
theorem cost_erase_le {E : CH.Digraph} {U : Finset ℕ} {t b u : ℕ} :
    cost (t-1) E (U.erase b) u ≤ cost t E U u := by
  classical
  have cover : outN E U u ⊆ insert b (outN E (U.erase b) u) := by
    intro x xm
    obtain ⟨xu, ux⟩ := mem_outN.mp xm
    by_cases e : x = b
    · exact e ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e, xu⟩, ux⟩)
  have := (card_le_card cover).trans (card_insert_le _ _)
  unfold cost
  omega

/-- **The floor on carriers of at most `q (t-1) + 1` labels.** -/
theorem floor_low {q t : ℕ} (hq : 1 ≤ q) (ht : 2 ≤ t) (law : ShortfallFloor q (t-1) (t-1))
    (E : CH.Digraph) (U : Finset ℕ) (live : U.Nonempty) (small : U.card ≤ q * (t-1) + 1)
    (free : QFree E U q) : t ≤ total t E U := by
  classical
  by_cases low : U.card ≤ q * (t-1)
  · -- a row short at the lower quota is short by one more here
    have base := law E U live low free
    have strict : total (t-1) E U < total t E U := by
      unfold total
      apply sum_lt_sum
      · intro u _
        unfold cost
        omega
      · by_contra none
        push Not at none
        have zero : total (t-1) E U = 0 := by
          unfold total
          refine sum_eq_zero fun u um => ?_
          have := none u um
          unfold cost at this ⊢
          omega
        omega
    omega
  · have size : U.card = q * (t-1) + 1 := by omega
    have room : 1 ≤ q * (t-1) := Nat.mul_pos hq (by omega)
    by_contra few
    -- some row is short at quota `t`
    obtain ⟨b, bu, short⟩ : ∃ b ∈ U, 1 ≤ cost t E U b := by
      by_contra none
      push Not at none
      obtain ⟨v, vu⟩ := live
      have base := law E (U.erase v) (card_pos.mp (by rw [card_erase_of_mem vu]; omega))
        (by rw [card_erase_of_mem vu]; omega) (free.mono_set (erase_subset _ _))
      have zero : total (t-1) E (U.erase v) = 0 := by
        unfold total
        refine sum_eq_zero fun u um => ?_
        have le := cost_erase_le (E := E) (U := U) (t := t) (b := v) (u := u)
        have := none u (mem_erase.mp um).2
        omega
      omega
    have base := law E (U.erase b) (card_pos.mp (by rw [card_erase_of_mem bu]; omega))
      (by rw [card_erase_of_mem bu]; omega) (free.mono_set (erase_subset _ _))
    have drop : total (t-1) E (U.erase b) + cost t E U b ≤ total t E U := by
      unfold total
      rw [← add_sum_erase U (cost t E U) bu, Nat.add_comm]
      exact Nat.add_le_add_left (sum_le_sum fun u _ => cost_erase_le) _
    omega

#print axioms triples_through_pair
#print axioms pairs_in_triples
#print axioms triples_inside
#print axioms row_sum
#print axioms bank_sum
#print axioms floor_bound
#print axioms floor_on_banks
#print axioms thirty_ten
#print axioms triangle_order
#print axioms pair_bank_sum
#print axioms band_floor_order
#print axioms near_band_order
#print axioms lone_bank
#print axioms host_band_order
#print axioms wide_cutoff_order
#print axioms floor_band
#print axioms floor_third
#print axioms triangle_of_floor
#print axioms floor_low
end LeanCH.BR.BankAverage
