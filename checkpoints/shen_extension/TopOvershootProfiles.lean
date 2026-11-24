import checkpoints.shen_extension.PrivateCompletionOrder
import checkpoints.shen_extension.UnitStateBoundary
import checkpoints.shen_extension.HalfLawSupply
import Mathlib.Tactic

/-!
# Overshoot one at the triangle top order: the two profiles

Lean 4.35.0. Paper: `triangle_20261118/PrivateCompletionOrder_Handoff_20261118.md`, section "Remaining cases".
Setting: `O : Origin 3 (d+1)`, `fr : Frontier O st`, `c = total (d+1) st.H st.U < d+1`, `|V| + 1 = |U| + c`.
The top order `|V| = 3(d+1)` is not assumed: it follows from the overshoot (`top_of_overshoot_one`).

Pure counting (free type).
* `sum_one_layer`, `sum_two_layers`: a sum of values at most 1 (resp. 2) is the size of its level sets.
* `one_one_profile`: values at most 1 summing to 2 sit on exactly two points.
* `two_one_profile`: values at most 2, at most two positive, at most one at least 2, summing to 3, are `2,1,0,…`.

Levels and split.
* `triangle_levels`: at budget `3d+4` every row owes at most 2, at most two rows owe one, at most one owes two.
* `top_of_overshoot_one`: overshoot one forces `|V| = 3(d+1)`.
* `top_overshoot_one_split`: either one vertex is missing and `c = 2`, or two are missing and `c = 3`.

Profile (a): one missing vertex.
* `one_hole_layer`: (any cutoff, any reachable state) one hole and total two give rows owing at most 1, two positive.
* `profile_a_rows`: (any cutoff) exactly two distinct rows owe one, all others owe nothing.
* `one_hole_graph`: (any cutoff) the state is `q`-free, all rows have at least `d` heads, exactly two have `d`.
* `profile_a_graph`: at cutoff 3 also `|U| = 3d+2`.
* `QThreeTight q d` / `ThreeTight d`: every `q`-free digraph on `q*d+2` vertices with all rows at least `d` has
  three rows with exactly `d` heads.
* `one_hole_false_of_threeTight`, `profile_a_false_of_threeTight`: profile (a) contradicts the law.
* `threeTight_of_halfLaw`, `threeTight_of_tightLaw` (both for `1 ≤ d`), `threeTight_one/two/three`, `threeTight_small`.
* `one_hole_parent_count`: (any cutoff) a reachable state with one hole is `V.erase v`, and its total equals the
  number of parents of `v` with out-degree exactly `d+1` in the source.
* `profile_a_source`: in profile (a) the source has a vertex with exactly two parents of out-degree `d+1`.

Profile (b): two missing vertices.
* `profile_b_rows`: distinct `x, y` with `cost x = 2`, `cost y = 1`, all others 0.
* `arc_to_heavy_row`: (any cutoff) on at most `q*d+1` vertices with the lower law, if `y` has at least `d` heads
  and every row other than `x, y` at least `d+1`, then `y → x`.
* `profile_b_arc`: in profile (b), `st.H y x = true`.
* `unit_below`: deleting `x` leaves total one at target `d` (`y` has `d-1` heads, others at least `d`).
* `profile_b_unit_below`: on `st.U.erase x`: total `d` shortfall 1, `3d` vertices, 3-free.
* `QBoundaryNoPrivate q d` / `BoundaryNoPrivate d`: no `q`-free digraph on `q*d+1` vertices with all rows at
  least `d` has a vertex with exactly one parent.
* `unit_false_of_boundaryNoPrivate`: (any cutoff `q ≥ 1`, `d ≥ 2`) a total-one graph at target `d` on `q*d`
  vertices contradicts the law, via one private step.
* `not_boundaryNoPrivate_one`: `BoundaryNoPrivate 1` is false (directed 4-cycle), so `d ≥ 2` is needed.
* `profile_b_false_of_boundaryNoPrivate`: profile (b) contradicts the law for `d ≥ 2`.

Combined.
* `top_overshoot_one_false`: for `d ≥ 2`, `ThreeTight d` and `BoundaryNoPrivate d` exclude overshoot one.
* `overshoot_ge_two`: under the same laws every positive overshoot is at least 2.
* `third_disjunct_two`: the third disjunct of `Alternatives` holds with `2 ≤ g` in place of `0 < g`.

`ThreeTight d` and `BoundaryNoPrivate d` are SUPPLIED HYPOTHESES. Nothing here closes CH.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure.TopOvershoot

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 Finset LeanCH.BR.Closure.DeficitLevels
  LeanCH.BR.Closure.PackingFrontier LeanCH.BR.Closure.PrivateCompletion
  LeanCH.BR.Closure.UnitState LeanCH.BR.Closure.PrivateCompletionOrder
  LeanCH.BR.HalfLawSupply LeanCH.BR.TightRow

/-! ## Pure counting -/

/-- Values at most one: the sum is the number of positive values. -/
theorem sum_one_layer {α : Type*} {U : Finset α} {a : α → ℕ} (h : ∀ x ∈ U, a x ≤ 1) :
    ∑ x ∈ U, a x = (U.filter (fun x => 1 ≤ a x)).card := by
  rw [card_filter]
  apply sum_congr rfl
  intro x hx
  have := h x hx
  split_ifs <;> omega

/-- Values at most two: the sum is the sum of the two level sizes. -/
theorem sum_two_layers {α : Type*} {U : Finset α} {a : α → ℕ} (h : ∀ x ∈ U, a x ≤ 2) :
    ∑ x ∈ U, a x = (U.filter (fun x => 1 ≤ a x)).card + (U.filter (fun x => 2 ≤ a x)).card := by
  rw [card_filter, card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  have := h x hx
  split_ifs <;> omega

/-- Values at most one summing to two sit on exactly two points. -/
theorem one_one_profile {α : Type*} [DecidableEq α] {U : Finset α} {a : α → ℕ}
    (cap : ∀ x ∈ U, a x ≤ 1) (sum : ∑ x ∈ U, a x = 2) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ a x = 1 ∧ a y = 1 ∧ ∀ z ∈ U, z ≠ x → z ≠ y → a z = 0 := by
  have e := sum_one_layer cap
  have c : (U.filter (fun x => 1 ≤ a x)).card = 2 := by omega
  obtain ⟨x, y, ne, eq⟩ := card_eq_two.mp c
  have mx : x ∈ U.filter (fun x => 1 ≤ a x) := by rw [eq]; simp
  have my : y ∈ U.filter (fun x => 1 ≤ a x) := by rw [eq]; simp
  obtain ⟨xU, x1⟩ := mem_filter.mp mx
  obtain ⟨yU, y1⟩ := mem_filter.mp my
  refine ⟨x, xU, y, yU, ne, by have := cap x xU; omega, by have := cap y yU; omega, ?_⟩
  intro z zU zx zy
  by_contra h
  have m : z ∈ U.filter (fun x => 1 ≤ a x) := mem_filter.mpr ⟨zU, by omega⟩
  rw [eq] at m
  simp [zx, zy] at m

/-- Values at most two, at most two positive and at most one at least two, summing to three. -/
theorem two_one_profile {α : Type*} [DecidableEq α] {U : Finset α} {a : α → ℕ}
    (cap : ∀ x ∈ U, a x ≤ 2) (l1 : (U.filter (fun x => 1 ≤ a x)).card ≤ 2)
    (l2 : (U.filter (fun x => 2 ≤ a x)).card ≤ 1) (sum : ∑ x ∈ U, a x = 3) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ a x = 2 ∧ a y = 1 ∧ ∀ z ∈ U, z ≠ x → z ≠ y → a z = 0 := by
  have layers := sum_two_layers cap
  have c1 : (U.filter (fun x => 1 ≤ a x)).card = 2 := by omega
  have c2 : (U.filter (fun x => 2 ≤ a x)).card = 1 := by omega
  obtain ⟨x, hx⟩ := card_eq_one.mp c2
  have mx : x ∈ U.filter (fun x => 2 ≤ a x) := by rw [hx]; exact mem_singleton_self x
  obtain ⟨xU, x2⟩ := mem_filter.mp mx
  have mx1 : x ∈ U.filter (fun x => 1 ≤ a x) := mem_filter.mpr ⟨xU, by omega⟩
  have rest : ((U.filter (fun x => 1 ≤ a x)).erase x).card = 1 := by
    rw [card_erase_of_mem mx1]; omega
  obtain ⟨y, hy⟩ := card_eq_one.mp rest
  have my : y ∈ (U.filter (fun x => 1 ≤ a x)).erase x := by rw [hy]; exact mem_singleton_self y
  obtain ⟨yx, my1⟩ := mem_erase.mp my
  obtain ⟨yU, y1⟩ := mem_filter.mp my1
  have y2 : a y < 2 := by
    by_contra! h
    have m : y ∈ U.filter (fun x => 2 ≤ a x) := mem_filter.mpr ⟨yU, h⟩
    rw [hx] at m
    exact yx (mem_singleton.mp m)
  refine ⟨x, xU, y, yU, Ne.symm yx, by have := cap x xU; omega, by omega, ?_⟩
  intro z zU zx zy
  by_contra h
  have m : z ∈ (U.filter (fun x => 1 ≤ a x)).erase x :=
    mem_erase.mpr ⟨zx, mem_filter.mpr ⟨zU, by omega⟩⟩
  rw [hy] at m
  exact zy (mem_singleton.mp m)

/-! ## Levels and the split -/

/-- At budget `3d+4`: every row owes at most two, at most two rows owe one, at most one owes two. -/
theorem triangle_levels {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (budget : st.U.card + total (d+1) st.H st.U ≤ 3*d+4) :
    (∀ x ∈ st.U, cost (d+1) st.H st.U x ≤ 2) ∧
    (st.U.filter (fun x => 1 ≤ cost (d+1) st.H st.U x)).card ≤ 2 ∧
    (st.U.filter (fun x => 2 ≤ cost (d+1) st.H st.U x)).card ≤ 1 := by
  let a := cost (d+1) st.H st.U
  let L (j : ℕ) := st.U.filter (fun x => j ≤ a x)
  have width (j : ℕ) (pos : 0 < j) (live : (L j).Nonempty) :
      3*j+3*(L j).card+1 ≤ 3*3+(L j).card :=
    reverse_level_bound (b := 3) fr (by decide) small pos (by omega) (filter_subset _ _) live
      (fun _ hx => (mem_filter.mp hx).2)
  have level1 : (L 1).card ≤ 2 := by
    by_contra! h
    have := width 1 (by decide) (card_pos.mp (by omega))
    omega
  have level2 : (L 2).card ≤ 1 := by
    by_contra! h
    have := width 2 (by decide) (card_pos.mp (by omega))
    omega
  have ceiling (x) (hx : x ∈ st.U) : a x ≤ 2 := by
    by_contra! h
    have hit : x ∈ L 3 := mem_filter.mpr ⟨hx, h⟩
    have nonempty : (L 3).Nonempty := ⟨x, hit⟩
    have := width 3 (by decide) nonempty
    have := card_pos.mpr nonempty
    omega
  exact ⟨ceiling, level1, level2⟩

/-- Overshoot one forces the top order. -/
theorem top_of_overshoot_one {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U) :
    O.V.card = 3*(d+1) := by
  have order := O.order
  have := triangle_frontier_overshoot fr small (g := 1) (e := 3*(d+1) - O.V.card)
    (by decide) (by omega) excess
  omega

/-- Part 1: one missing vertex with total two, or two missing vertices with total three. -/
theorem top_overshoot_one_split {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U) :
    (st.U.card + 1 = O.V.card ∧ total (d+1) st.H st.U = 2) ∨
    (st.U.card + 2 = O.V.card ∧ total (d+1) st.H st.U = 3) := by
  have order := O.order
  have b := triangle_second_budget fr small (by omega)
  have := fr.proper
  omega

/-! ## Profile (a): one missing vertex -/

/-- One hole and total two: every row owes at most one and exactly two rows owe one. -/
theorem one_hole_layer {q s : ℕ} (O : Origin q s) {st : State}
    (reach : Reach (RStep q s) O.init st) (one : st.U.card + 1 = O.V.card)
    (two : total s st.H st.U = 2) :
    (∀ x ∈ st.U, cost s st.H st.U x ≤ 1) ∧
      (st.U.filter (fun x => 1 ≤ cost s st.H st.U x)).card = 2 := by
  have le1 : ∀ x ∈ st.U, cost s st.H st.U x ≤ 1 := fun x hx => by
    have := cost_le_holes O reach hx; omega
  have e : total s st.H st.U = (st.U.filter (fun x => 1 ≤ cost s st.H st.U x)).card :=
    sum_one_layer le1
  exact ⟨le1, by omega⟩

/-- (2a) Two distinct rows owe one head each, all other rows are full. -/
theorem profile_a_rows {q s : ℕ} (O : Origin q s) {st : State}
    (reach : Reach (RStep q s) O.init st) (one : st.U.card + 1 = O.V.card)
    (two : total s st.H st.U = 2) :
    ∃ p₁ ∈ st.U, ∃ p₂ ∈ st.U, p₁ ≠ p₂ ∧ cost s st.H st.U p₁ = 1 ∧ cost s st.H st.U p₂ = 1 ∧
      ∀ x ∈ st.U, x ≠ p₁ → x ≠ p₂ → cost s st.H st.U x = 0 :=
  one_one_profile (one_hole_layer O reach one two).1 two

/-- (2b) The one-hole state: `q`-free, all rows at least `d`, exactly two rows with `d` heads. -/
theorem one_hole_graph {q d : ℕ} (O : Origin q (d+1)) {st : State}
    (reach : Reach (RStep q (d+1)) O.init st) (one : st.U.card + 1 = O.V.card)
    (two : total (d+1) st.H st.U = 2) :
    QFree st.H st.U q ∧ (∀ x ∈ st.U, d ≤ (outN st.H st.U x).card) ∧
      (st.U.filter (fun x => (outN st.H st.U x).card = d)).card = 2 := by
  obtain ⟨le1, c2⟩ := one_hole_layer O reach one two
  have rows : ∀ x ∈ st.U, d ≤ (outN st.H st.U x).card := fun x hx => by
    have := le1 x hx; unfold cost at this; omega
  refine ⟨(rreach_valid O reach).2.2, rows, ?_⟩
  rw [← c2]
  congr 1
  apply filter_congr
  intro x hx
  have := rows x hx
  unfold cost
  constructor <;> intro h <;> omega

/-- (2b) Profile (a) at cutoff 3, with the order `3d+2`. -/
theorem profile_a_graph {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U)
    (one : st.U.card + 1 = O.V.card) :
    QFree st.H st.U 3 ∧ st.U.card = 3*d+2 ∧ (∀ x ∈ st.U, d ≤ (outN st.H st.U x).card) ∧
      (st.U.filter (fun x => (outN st.H st.U x).card = d)).card = 2 := by
  have top := top_of_overshoot_one fr small excess
  obtain ⟨free, rows, tight⟩ := one_hole_graph O fr.reached one (by omega)
  exact ⟨free, by omega, rows, tight⟩

/-- Three tight rows on `q*d+2` vertices. -/
def QThreeTight (q d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U q → U.card = q*d+2 →
    (∀ x ∈ U, d ≤ (outN E U x).card) → 3 ≤ (U.filter (fun x => (outN E U x).card = d)).card

/-- Three tight rows on `3d+2` vertices, cutoff 3. -/
abbrev ThreeTight (d : ℕ) : Prop := QThreeTight 3 d

/-- (2c) A one-hole state of total two on `q*d+2` vertices contradicts `QThreeTight q d`. -/
theorem one_hole_false_of_threeTight {q d : ℕ} (law : QThreeTight q d) (O : Origin q (d+1)) {st : State}
    (reach : Reach (RStep q (d+1)) O.init st) (one : st.U.card + 1 = O.V.card)
    (two : total (d+1) st.H st.U = 2) (size : st.U.card = q*d+2) : False := by
  obtain ⟨free, rows, tight⟩ := one_hole_graph O reach one two
  have := law _ _ free size rows
  omega

/-- (2c) Profile (a) contradicts `ThreeTight d`. -/
theorem profile_a_false_of_threeTight {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U)
    (one : st.U.card + 1 = O.V.card) (law : ThreeTight d) : False := by
  obtain ⟨free, size, rows, tight⟩ := profile_a_graph fr small excess one
  have := law _ _ free size rows
  omega

/-- (2c) The half law gives three tight rows (`3d+2 ≤ 2t` with `d ≥ 1` gives `t ≥ 3`). -/
theorem threeTight_of_halfLaw {d : ℕ} (hd : 1 ≤ d) (H : HalfLaw d) : ThreeTight d := by
  intro E U free size deg
  have := H E U free size deg
  omega

/-- (2c) The tight-row law gives `d+2 ≥ 3` tight rows. -/
theorem threeTight_of_tightLaw {d : ℕ} (hd : 1 ≤ d) (T : TightLaw 3 d) : ThreeTight d := by
  intro E U free size deg
  have := T E U free (by omega) deg
  omega

theorem threeTight_one : ThreeTight 1 := threeTight_of_halfLaw le_rfl halfLaw_one

theorem threeTight_two : ThreeTight 2 := threeTight_of_halfLaw (by omega) halfLaw_two

theorem threeTight_three : ThreeTight 3 := threeTight_of_halfLaw (by omega) halfLaw_three

theorem threeTight_small {d : ℕ} (h1 : 1 ≤ d) (h3 : d ≤ 3) : ThreeTight d := by
  interval_cases d
  · exact threeTight_one
  · exact threeTight_two
  · exact threeTight_three

/-- (2d) A reachable one-hole state is `V.erase v`, and its shortfall counts the parents of `v`
with out-degree exactly `d+1` in the (arc-maximal) source. -/
theorem one_hole_parent_count {q d : ℕ} (O : Origin q (d+1)) {st : State}
    (maximal : MaximalReturns q O.G O.V) (reach : Reach (RStep q (d+1)) O.init st)
    (one : st.U.card + 1 = O.V.card) :
    ∃ v ∈ O.V, st.U = O.V.erase v ∧
      total (d+1) st.H st.U =
        (O.V.filter (fun p => O.G p v = true ∧ (outN O.G O.V p).card = d+1)).card := by
  classical
  have valid := rreach_valid O reach
  have sub := valid.1
  have keep := rstep_originalKept O reach
  have hq := origin_cutoff_pos O
  obtain ⟨v, hv⟩ := card_eq_one.mp (show (O.V \ st.U).card = 1 by
    rw [card_sdiff_of_subset sub]; omega)
  have mv : v ∈ O.V \ st.U := by rw [hv]; exact mem_singleton_self v
  obtain ⟨hvV, hvU⟩ := mem_sdiff.mp mv
  have eqU : st.U = O.V.erase v := by
    apply eq_of_subset_of_card_le
    · intro x hx
      exact mem_erase.mpr ⟨fun e => hvU (e ▸ hx), sub hx⟩
    · rw [card_erase_of_mem hvV]; omega
  have sd : O.V \ {v} = st.U := by
    rw [eqU]; ext x; simp only [mem_sdiff, mem_singleton, mem_erase]; tauto
  have safe : QFree st.H (O.V \ {v}) q := by rw [sd]; exact valid.2.2
  have keep' : ∀ a ∈ O.V \ {v}, ∀ b ∈ O.V \ {v}, O.G a b = true → st.H a b = true := by
    rw [sd]; exact keep
  have same := one_hole_exact O.free maximal hvV O.deg safe keep'
  rw [sd] at same
  refine ⟨v, hvV, eqU, ?_⟩
  rw [same, eqU]
  let w (u : ℕ) : ℕ := if O.G u v = true ∧ (outN O.G O.V u).card = d+1 then 1 else 0
  have row (u) (hu : u ∈ O.V.erase v) : cost (d+1) O.G (O.V.erase v) u = w u := by
    have er : outN O.G (O.V.erase v) u = (outN O.G O.V u).erase v := outN_erase O.G O.V v u
    have orig := O.deg _ (mem_of_mem_erase hu)
    unfold cost
    rw [er]
    by_cases e : O.G u v = true
    · rw [card_erase_of_mem (mem_outN.mpr ⟨hvV, e⟩)]
      simp only [w, e, true_and]
      split_ifs <;> omega
    · have none : v ∉ outN O.G O.V u := fun h => e (mem_outN.mp h).2
      rw [erase_eq_of_notMem none]
      have zero : w u = 0 := by simp [w, e]
      rw [zero]
      omega
  have eqs := sum_congr rfl row
  have sum0 := sum_erase_add O.V w hvV
  have zero : w v = 0 := by simp [w, loopfree O.free hq hvV]
  rw [zero, Nat.add_zero] at sum0
  rw [card_filter]
  exact eqs.trans sum0

/-- (2d) In profile (a) the state is the source minus one vertex `v`, and `v` has exactly two
parents of out-degree exactly `d+1` in the source. -/
theorem profile_a_source {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U)
    (one : st.U.card + 1 = O.V.card) :
    ∃ v ∈ O.V, st.U = O.V.erase v ∧
      (O.V.filter (fun p => O.G p v = true ∧ (outN O.G O.V p).card = d+1)).card = 2 := by
  obtain ⟨v, hv, eqU, count⟩ := one_hole_parent_count O fr.maximal fr.reached one
  exact ⟨v, hv, eqU, by omega⟩

/-! ## Profile (b): two missing vertices -/

/-- (3a) One row owes two, one owes one, all others are full. -/
theorem profile_b_rows {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U)
    (twoHoles : st.U.card + 2 = O.V.card) :
    ∃ x ∈ st.U, ∃ y ∈ st.U, x ≠ y ∧ cost (d+1) st.H st.U x = 2 ∧ cost (d+1) st.H st.U y = 1 ∧
      ∀ z ∈ st.U, z ≠ x → z ≠ y → cost (d+1) st.H st.U z = 0 := by
  have order := O.order
  obtain ⟨cap, l1, l2⟩ := triangle_levels fr small (by omega)
  exact two_one_profile cap l1 l2 (show total (d+1) st.H st.U = 3 by omega)

/-- (3b, any cutoff) On at most `q*d+1` vertices under the lower law, if `y` keeps at least `d` heads
and every row other than `x, y` has at least `d+1`, then `y` points to `x`. -/
theorem arc_to_heavy_row {D : CH.Digraph} {U : Finset ℕ} {q d x y : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (size : U.card ≤ q*d+1)
    (hx : x ∈ U) (hy : y ∈ U) (ne : y ≠ x) (ycard : d ≤ (outN D U y).card)
    (full : ∀ z ∈ U, z ≠ x → z ≠ y → d+1 ≤ (outN D U z).card) : D y x = true := by
  by_contra no
  have deg : ∀ z ∈ U.erase x, d ≤ (outN D (U.erase x) z).card := by
    intro z hz
    obtain ⟨zx, zU⟩ := mem_erase.mp hz
    rw [outN_erase]
    by_cases zy : z = y
    · rw [zy, erase_eq_of_notMem (fun m => no (mem_outN.mp m).2)]
      exact ycard
    · have := full z zU zx zy
      have := pred_card_le_card_erase (s := outN D U z) (a := x)
      omega
  have big := lower D (U.erase x) (free.mono_set (erase_subset x U)) deg ⟨y, mem_erase.mpr ⟨ne, hy⟩⟩
  rw [card_erase_of_mem hx] at big
  omega

/-- (3b) In profile (b) the one-unit row points to the two-unit row. -/
theorem profile_b_arc {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (twoHoles : st.U.card + 2 = O.V.card) {x y : ℕ} (hx : x ∈ st.U) (hy : y ∈ st.U) (ne : x ≠ y)
    (cy : cost (d+1) st.H st.U y = 1)
    (rest : ∀ z ∈ st.U, z ≠ x → z ≠ y → cost (d+1) st.H st.U z = 0) : st.H y x = true := by
  have order := O.order
  apply arc_to_heavy_row (rreach_valid O fr.reached).2.2 fr.lower (by omega) hx hy (Ne.symm ne)
  · unfold cost at cy; omega
  · intro z hz zx zy; have := rest z hz zx zy; unfold cost at this; omega

/-- (3c, any cutoff) Deleting `x` leaves shortfall one at target `d`: `y` has `d-1` heads, others at least `d`. -/
theorem unit_below {D : CH.Digraph} {U : Finset ℕ} {d x y : ℕ} (hd : 1 ≤ d)
    (hx : x ∈ U) (hy : y ∈ U) (ne : y ≠ x) (yx : D y x = true) (ycard : (outN D U y).card = d)
    (full : ∀ z ∈ U, z ≠ x → z ≠ y → d+1 ≤ (outN D U z).card) :
    total d D (U.erase x) = 1 ∧ (outN D (U.erase x) y).card + 1 = d ∧
      ∀ z ∈ U.erase x, z ≠ y → d ≤ (outN D (U.erase x) z).card := by
  have yrow : (outN D (U.erase x) y).card + 1 = d := by
    rw [outN_erase, card_erase_of_mem (mem_outN.mpr ⟨hx, yx⟩)]; omega
  have others : ∀ z ∈ U.erase x, z ≠ y → d ≤ (outN D (U.erase x) z).card := by
    intro z hz zy
    obtain ⟨zx, zU⟩ := mem_erase.mp hz
    rw [outN_erase]
    have := full z zU zx zy
    have := pred_card_le_card_erase (s := outN D U z) (a := x)
    omega
  refine ⟨?_, yrow, others⟩
  unfold total
  rw [sum_eq_single y]
  · unfold cost; omega
  · intro z hz zy; have := others z hz zy; unfold cost; omega
  · intro no; exact absurd (mem_erase.mpr ⟨ne, hy⟩) no

/-- (3c) In profile (b), deleting `x` leaves a 3-free unit graph one degree down on `3d` vertices. -/
theorem profile_b_unit_below {d : ℕ} {O : Origin 3 (d+1)} {st : State}
    (fr : Frontier O st) (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U)
    (twoHoles : st.U.card + 2 = O.V.card) {x y : ℕ} (hx : x ∈ st.U) (hy : y ∈ st.U) (ne : x ≠ y)
    (cy : cost (d+1) st.H st.U y = 1)
    (rest : ∀ z ∈ st.U, z ≠ x → z ≠ y → cost (d+1) st.H st.U z = 0) :
    total d st.H (st.U.erase x) = 1 ∧ (st.U.erase x).card = 3*d ∧ QFree st.H (st.U.erase x) 3 := by
  have top := top_of_overshoot_one fr small excess
  have arc := profile_b_arc fr twoHoles hx hy ne cy rest
  have hd := origin_degree_pos O
  have ycard : (outN st.H st.U y).card = d := by unfold cost at cy; omega
  obtain ⟨unit, _, _⟩ := unit_below hd hx hy (Ne.symm ne) arc ycard
    (fun z hz zx zy => by have := rest z hz zx zy; unfold cost at this; omega)
  exact ⟨unit, by rw [card_erase_of_mem hx]; omega,
    (rreach_valid O fr.reached).2.2.mono_set (erase_subset x st.U)⟩

/-- No vertex with exactly one parent, on `q*d+1` vertices with all rows at least `d`. -/
def QBoundaryNoPrivate (q d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (W : Finset ℕ), QFree E W q → W.card = q*d+1 →
    (∀ x ∈ W, d ≤ (outN E W x).card) → ∀ v ∈ W, ¬ ∃ p ∈ W, ∀ x ∈ W, E x v = true ↔ x = p

/-- The same at cutoff 3. -/
abbrev BoundaryNoPrivate (d : ℕ) : Prop := QBoundaryNoPrivate 3 d

/-- (3d, any cutoff) A `q`-free graph on `q*d` vertices with shortfall one at target `d ≥ 2`
contradicts `QBoundaryNoPrivate q d`: one private step builds the forbidden graph. -/
theorem unit_false_of_boundaryNoPrivate {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (law : QBoundaryNoPrivate q d) (hq : 1 ≤ q) (hd : 2 ≤ d) (free : QFree D U q)
    (size : U.card = q*d) (unit : total d D U = 1) : False := by
  obtain ⟨u, hu, short⟩ : ∃ u ∈ U, 0 < cost d D U u := by
    by_contra! none
    have zero : total d D U = 0 := sum_eq_zero (fun x hx => by have := none x hx; omega)
    omega
  obtain ⟨E, v, fresh, safe, _, parents, paid⟩ := private_step free hq (by omega) hu short
  have card := card_insert_of_notMem fresh
  apply law E (insert v U) safe (by omega) ?_ v (mem_insert_self v U) ⟨u, mem_insert_of_mem hu, ?_⟩
  · intro x hx
    have le := single_le_sum (f := cost d E (insert v U)) (fun _ _ => Nat.zero_le _) hx
    change d - (outN E (insert v U) x).card ≤ total d E (insert v U) at le
    omega
  · intro x hx
    rcases mem_insert.mp hx with rfl | old
    · have ne : x ≠ u := fun eq => fresh (eq ▸ hu)
      simp [ne, loopfree safe hq (mem_insert_self x U)]
    · exact parents x old

/-- (3d) `BoundaryNoPrivate 1` is false: the directed 4-cycle on `{0,1,2,3}`. -/
theorem not_boundaryNoPrivate_one : ¬ BoundaryNoPrivate 1 := by
  let D : CH.Digraph := fun x y => decide (y = (x+1) % 4)
  have pos : ∀ {a b m : ℕ}, Walk D (range 4) a b m → (a < 4 ∨ 0 < m) → b = (a+m) % 4 := by
    intro a b m w
    induction w with
    | refl a => intro h; omega
    | @step a b c k hb hab _ ih =>
      intro _
      have e : b = (a+1) % 4 := by simpa [D] using hab
      have hb4 : b < 4 := mem_range.mp hb
      have := ih (Or.inl hb4)
      omega
  have free : QFree D (range 4) 3 := by
    intro a l h1 h3 w
    have := pos w (Or.inr (by omega))
    omega
  have deg : ∀ x ∈ range 4, 1 ≤ (outN D (range 4) x).card := by
    intro x _
    exact card_pos.mpr ⟨(x+1) % 4, mem_outN.mpr ⟨mem_range.mpr (by omega), by simp [D]⟩⟩
  have uniq : ∀ x ∈ range 4, D x 0 = true ↔ x = 3 := by
    intro x hx
    have := mem_range.mp hx
    simp only [D, decide_eq_true_eq]
    constructor <;> intro h <;> omega
  intro law
  exact law D (range 4) free (by simp) deg 0 (by simp) ⟨3, by simp, uniq⟩

/-- (3d) Profile (b) contradicts `BoundaryNoPrivate d` for `d ≥ 2`. -/
theorem profile_b_false_of_boundaryNoPrivate {d : ℕ} (hd : 2 ≤ d) (law : BoundaryNoPrivate d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U)
    (twoHoles : st.U.card + 2 = O.V.card) : False := by
  obtain ⟨x, hx, y, hy, ne, _, cy, rest⟩ := profile_b_rows fr small excess twoHoles
  obtain ⟨unit, size, free⟩ := profile_b_unit_below fr small excess twoHoles hx hy ne cy rest
  exact unit_false_of_boundaryNoPrivate law (by decide) hd free size unit

/-! ## Combined -/

/-- Part 4: under `ThreeTight d` and `BoundaryNoPrivate d`, `d ≥ 2`, overshoot one is impossible. -/
theorem top_overshoot_one_false {d : ℕ} (hd : 2 ≤ d) (T : ThreeTight d) (B : BoundaryNoPrivate d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U) : False := by
  rcases top_overshoot_one_split fr small excess with ⟨one, _⟩ | ⟨two, _⟩
  · exact profile_a_false_of_threeTight fr small excess one T
  · exact profile_b_false_of_boundaryNoPrivate hd B fr small excess two

/-- Part 4: under the same laws every positive overshoot is at least two. -/
theorem overshoot_ge_two {d : ℕ} (hd : 2 ≤ d) (T : ThreeTight d) (B : BoundaryNoPrivate d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (small : total (d+1) st.H st.U < d+1) {g : ℕ} (positive : 0 < g)
    (gap : O.V.card + g = st.U.card + total (d+1) st.H st.U) : 2 ≤ g := by
  by_contra! low
  have g1 : g = 1 := by omega
  subst g1
  exact top_overshoot_one_false hd T B fr small gap

/-- Part 4: the third disjunct of `Alternatives` holds with `2 ≤ g`. -/
theorem third_disjunct_two {d : ℕ} (hd : 2 ≤ d) (T : ThreeTight d) (B : BoundaryNoPrivate d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (third : total (d+1) st.H st.U<d+1 ∧ ∃ g e, 0<g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g)) :
    total (d+1) st.H st.U<d+1 ∧ ∃ g e, 2≤g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g) := by
  obtain ⟨small, g, e, positive, size, gap, box⟩ := third
  exact ⟨small, g, e, overshoot_ge_two hd T B fr small positive gap, size, gap, box⟩

#print axioms one_one_profile
#print axioms two_one_profile
#print axioms triangle_levels
#print axioms top_of_overshoot_one
#print axioms top_overshoot_one_split
#print axioms profile_a_rows
#print axioms one_hole_graph
#print axioms profile_a_graph
#print axioms one_hole_false_of_threeTight
#print axioms profile_a_false_of_threeTight
#print axioms threeTight_of_halfLaw
#print axioms threeTight_of_tightLaw
#print axioms threeTight_small
#print axioms one_hole_parent_count
#print axioms profile_a_source
#print axioms profile_b_rows
#print axioms arc_to_heavy_row
#print axioms profile_b_arc
#print axioms unit_below
#print axioms profile_b_unit_below
#print axioms unit_false_of_boundaryNoPrivate
#print axioms not_boundaryNoPrivate_one
#print axioms profile_b_false_of_boundaryNoPrivate
#print axioms top_overshoot_one_false
#print axioms overshoot_ge_two
#print axioms third_disjunct_two

end LeanCH.BR.Closure.TopOvershoot
