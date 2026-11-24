import checkpoints.shen_extension.RecursivePrivateCompletion
import checkpoints.shen_extension.TightProfileGeneral
import checkpoints.shen_extension.HalfLawSupply
import Mathlib.Tactic

/-!
# Unit graphs one degree down, and the exact-cost alternative at cutoff 3

Lean 4.35.0. A unit graph at level `d`, cutoff `q`: `QFree D U q` with `total (d+1) D U = 1`, i.e. one row `u`
with exactly `d` heads and every other row with at least `d+1`. The lower law is `OrderLaw q d (q*d+1)`.

Part A (general cutoff `q`).
* `outN_erase`: the heads of `x` in `U.erase u` are the heads of `x` in `U` minus `u`.
* `unit_order_lower`: a unit graph with the lower law has at least `q*d+2` vertices (`1 ≤ q`, `1 ≤ d`).
* `unit_low_row`: if `U \ Z` is nonempty with at most `q*d` vertices, either `u ∉ Z` has a head in `Z`, or some
  other row outside `Z` has at least two heads in `Z` (no side condition).
* `unit_pair`: on at most `q*d+2` vertices, any two distinct vertices are hit by `u` or have a common parent.
* `unit_parents_dominate`: on at most `q*d+2` vertices, every vertex other than `u` shares a parent with `u`.
* `unit_order_of_total`, `unit_low_row_of_total`, `unit_pair_of_total`, `unit_parents_dominate_of_total`: the same
  from `total (d+1) D U = 1`.

Part B (closure states).
* `origin_cutoff_pos`: every origin has `1 ≤ q`.
* `origin_degree_pos`: every origin at degree `d+1` has `1 ≤ d` (degree 1 never fails, any cutoff).
* `unit_state_card`: a valid proper unit state has `q*d+2 ≤ |U|` and its origin has `q*d+3 ≤ |V|`.
* `unit_state_three`: at cutoff 3, `|U| = 3d+2` and `|V| = 3(d+1)`.
* `middle_three`: the data of the exact-cost alternative at cutoff 3 is a unit graph on `3d+2` vertices with an
  origin of order `3(d+1)`.

Part C (laws that kill a unit graph).
* `QTwoTight q d` / `TwoTight d`: every `q`-free digraph on `q*d+2` vertices with all rows at least `d` has two
  rows with exactly `d` heads.
* `QHeavyTightHead q d` / `HeavyTightHead d`: on `q*d+1` vertices with all rows at least `d`, every heavy row
  has a tight head.
* `unit_false_of_twoTight_row`, `unit_false_of_twoTight`: a unit graph on `q*d+2` vertices contradicts `QTwoTight q d`.
* `twoTight_of_halfLaw`, `twoTight_of_tightLaw`, `twoTight_one`, `twoTight_two`, `twoTight_three`, `twoTight_small`.
* `unit_false_of_heavyTightHead_row`, `unit_false_of_heavyTightHead`: for `3 ≤ q`, `1 ≤ d`, a unit graph on
  `q*d+2` vertices contradicts `QHeavyTightHead q d` (closed walk `u → h → a → u`).
* `thin_row`: one row can be cut down to any subset of its heads, keeping the cutoff.
* `twoTight_of_heavyTightHead`: for `3 ≤ q`, `1 ≤ d`, `QHeavyTightHead q d` implies `QTwoTight q d`.
* `heavyTightHead_of_boundaryRegular`, `unit_false_of_boundaryRegular`, `unit_false_of_no_top_profile`.

Part D (the alternatives at cutoff 3; `1 ≤ d` is derived from the origin).
* `middle_false_of_twoTight`, `middle_false_of_heavyTightHead`, `middle_false_of_boundaryRegular`,
  `middle_false_of_halfLaw`: the exact-cost disjunct of `Alternatives` is impossible under each law.
* `alternatives_three`: under `TwoTight d`, the first or third disjunct of `Alternatives` holds.
* `alternatives_three_of_halfLaw`: the same under `HalfLaw d`.
* `alternatives_three_small`: the same with no law for `d ≤ 3`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure.UnitState

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 Finset LeanCH.BR.Closure.DeficitLevels
  LeanCH.BR.Closure.PackingFrontier LeanCH.BR.Closure.PrivateCompletion
  LeanCH.BR.TightProfile LeanCH.BR.HalfLawSupply LeanCH.BR.TightRow

/-! ## Part A -/

/-- Heads in `U.erase u`. -/
theorem outN_erase (D : CH.Digraph) (U : Finset ℕ) (u x : ℕ) :
    outN D (U.erase u) x = (outN D U x).erase u := by
  ext z; simp only [mem_outN, mem_erase]; tauto

/-- (A1) A unit graph with the lower law has at least `q*d+2` vertices. -/
theorem unit_order_lower {D : CH.Digraph} {U : Finset ℕ} {q d u : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hu : u ∈ U) (short : (outN D U u).card = d)
    (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) :
    q*d+2 ≤ U.card := by
  obtain ⟨h, hh⟩ := card_pos.mp (show 0 < (outN D U u).card by omega)
  have hne : h ≠ u := by
    rintro rfl
    exact loopfree free hq hu (mem_outN.mp hh).2
  have live : (U.erase u).Nonempty := ⟨h, mem_erase.mpr ⟨hne, outN_subset hh⟩⟩
  have deg : ∀ x ∈ U.erase u, d ≤ (outN D (U.erase u) x).card := by
    intro x hx
    obtain ⟨xu, xU⟩ := mem_erase.mp hx
    rw [outN_erase]
    have := full x xU xu
    have := pred_card_le_card_erase (s := outN D U x) (a := u)
    omega
  have big := lower D (U.erase u) (free.mono_set (erase_subset u U)) deg live
  rw [card_erase_of_mem hu] at big
  have := card_pos.mpr ⟨u, hu⟩
  omega

/-- (A2) A low row outside `Z`: either the short row hits `Z`, or another row has two heads in `Z`. -/
theorem unit_low_row {D : CH.Digraph} {U Z : Finset ℕ} {q d u : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1))
    (short : (outN D U u).card = d) (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card)
    (live : (U \ Z).Nonempty) (small : (U \ Z).card ≤ q*d) :
    (u ∉ Z ∧ ∃ z ∈ Z, D u z = true) ∨ ∃ x ∈ U \ Z, x ≠ u ∧ 2 ≤ (outN D Z x).card := by
  obtain ⟨x, hx, low⟩ : ∃ x ∈ U \ Z, (outN D (U \ Z) x).card < d := by
    by_contra! h
    have := lower D (U \ Z) (free.mono_set sdiff_subset) h live
    omega
  have split : (outN D U x).card ≤ (outN D (U \ Z) x).card + (outN D Z x).card := by
    calc (outN D U x).card ≤ (outN D (U \ Z) x ∪ outN D Z x).card := by
          apply card_le_card
          intro z hz
          obtain ⟨zU, e⟩ := mem_outN.mp hz
          rw [mem_union]
          by_cases zZ : z ∈ Z
          · exact Or.inr (mem_outN.mpr ⟨zZ, e⟩)
          · exact Or.inl (mem_outN.mpr ⟨mem_sdiff.mpr ⟨zU, zZ⟩, e⟩)
      _ ≤ _ := card_union_le _ _
  obtain ⟨xU, xZ⟩ := mem_sdiff.mp hx
  by_cases xu : x = u
  · subst xu
    left
    refine ⟨xZ, ?_⟩
    obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (outN D Z x).card by omega)
    exact ⟨z, (mem_outN.mp hz).1, (mem_outN.mp hz).2⟩
  · right
    have := full x xU xu
    exact ⟨x, hx, xu, by omega⟩

/-- Two heads in a pair means both. -/
private theorem both_of_two {D : CH.Digraph} {z w x : ℕ} (ne : z ≠ w)
    (two : 2 ≤ (outN D {z, w} x).card) : D x z = true ∧ D x w = true := by
  have eq : outN D {z, w} x = {z, w} :=
    eq_of_subset_of_card_le outN_subset (by rw [card_pair ne]; exact two)
  have hz : z ∈ outN D {z, w} x := by rw [eq]; simp
  have hw : w ∈ outN D {z, w} x := by rw [eq]; simp
  exact ⟨(mem_outN.mp hz).2, (mem_outN.mp hw).2⟩

/-- (A3) Any two distinct vertices are hit by `u` or have a common parent. -/
theorem unit_pair {D : CH.Digraph} {U : Finset ℕ} {q d u : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hu : u ∈ U) (short : (outN D U u).card = d)
    (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) (size : U.card ≤ q*d+2)
    {z w : ℕ} (hz : z ∈ U) (hw : w ∈ U) (ne : z ≠ w) :
    D u z = true ∨ D u w = true ∨ ∃ x ∈ U, D x z = true ∧ D x w = true := by
  have big := unit_order_lower free lower hq hd hu short full
  have sub : ({z, w} : Finset ℕ) ⊆ U := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hz
    · rw [mem_singleton.mp hy]; exact hw
  have two : ({z, w} : Finset ℕ).card = 2 := card_pair ne
  have cs : (U \ {z, w}).card + ({z, w} : Finset ℕ).card = U.card := card_sdiff_add_card_eq_card sub
  have pos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
  generalize hm : q * d = m at big size pos
  have live : (U \ {z, w}).Nonempty := by rw [← card_pos]; omega
  have small : (U \ {z, w}).card ≤ q*d := by rw [hm]; omega
  rcases unit_low_row free lower short full live small with
    ⟨_, y, hy, e⟩ | ⟨x, hx, _, two'⟩
  · rcases mem_insert.mp hy with rfl | hy
    · exact Or.inl e
    · rw [mem_singleton.mp hy] at e; exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr ⟨x, (mem_sdiff.mp hx).1, both_of_two ne two'⟩)

/-- (A3) The parents of the short row dominate every other vertex. -/
theorem unit_parents_dominate {D : CH.Digraph} {U : Finset ℕ} {q d u : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hu : u ∈ U) (short : (outN D U u).card = d)
    (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) (size : U.card ≤ q*d+2)
    {z : ℕ} (hz : z ∈ U) (ne : z ≠ u) :
    ∃ x ∈ U, D x u = true ∧ D x z = true := by
  have big := unit_order_lower free lower hq hd hu short full
  have sub : ({u, z} : Finset ℕ) ⊆ U := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hu
    · rw [mem_singleton.mp hy]; exact hz
  have two : ({u, z} : Finset ℕ).card = 2 := card_pair (Ne.symm ne)
  have cs : (U \ {u, z}).card + ({u, z} : Finset ℕ).card = U.card := card_sdiff_add_card_eq_card sub
  have pos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
  generalize hm : q * d = m at big size pos
  have live : (U \ {u, z}).Nonempty := by rw [← card_pos]; omega
  have small : (U \ {u, z}).card ≤ q*d := by rw [hm]; omega
  rcases unit_low_row free lower short full live small with
    ⟨nu, _⟩ | ⟨x, hx, _, two'⟩
  · exact absurd (mem_insert_self u {z}) nu
  · exact ⟨x, (mem_sdiff.mp hx).1, both_of_two (Ne.symm ne) two'⟩

/-- (A1) from one unit. -/
theorem unit_order_of_total {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (unit : total (d+1) D U = 1) : q*d+2 ≤ U.card := by
  obtain ⟨u, hu, short, full⟩ := unit_profile unit
  exact unit_order_lower free lower hq hd hu (by omega) full

/-- (A2) from one unit. -/
theorem unit_low_row_of_total {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (unit : total (d+1) D U = 1) :
    ∃ u ∈ U, (outN D U u).card = d ∧ (∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) ∧
      ∀ Z : Finset ℕ, (U \ Z).Nonempty → (U \ Z).card ≤ q*d →
        (u ∉ Z ∧ ∃ z ∈ Z, D u z = true) ∨ ∃ x ∈ U \ Z, x ≠ u ∧ 2 ≤ (outN D Z x).card := by
  obtain ⟨u, hu, short, full⟩ := unit_profile unit
  exact ⟨u, hu, by omega, full, fun Z live small => unit_low_row free lower (by omega) full live small⟩

/-- (A3) pair form from one unit. -/
theorem unit_pair_of_total {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (unit : total (d+1) D U = 1) (size : U.card ≤ q*d+2) :
    ∃ u ∈ U, (outN D U u).card = d ∧ (∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) ∧
      ∀ z ∈ U, ∀ w ∈ U, z ≠ w →
        D u z = true ∨ D u w = true ∨ ∃ x ∈ U, D x z = true ∧ D x w = true := by
  obtain ⟨u, hu, short, full⟩ := unit_profile unit
  exact ⟨u, hu, by omega, full, fun z hz w hw ne =>
    unit_pair free lower hq hd hu (by omega) full size hz hw ne⟩

/-- (A3) domination form from one unit. -/
theorem unit_parents_dominate_of_total {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (free : QFree D U q) (lower : OrderLaw q d (q*d+1)) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (unit : total (d+1) D U = 1) (size : U.card ≤ q*d+2) :
    ∃ u ∈ U, (outN D U u).card = d ∧ (∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) ∧
      ∀ z ∈ U, z ≠ u → ∃ x ∈ U, D x u = true ∧ D x z = true := by
  obtain ⟨u, hu, short, full⟩ := unit_profile unit
  exact ⟨u, hu, by omega, full, fun z hz ne =>
    unit_parents_dominate free lower hq hd hu (by omega) full size hz ne⟩

/-! ## Part B -/

/-- Every origin has a positive cutoff. -/
theorem origin_cutoff_pos {q s : ℕ} (O : Origin q s) : 1 ≤ q := by
  have h1 := O.order
  have h2 := card_pos.mpr O.ne
  rcases Nat.eq_zero_or_pos q with h | h
  · have : q * s = 0 := by rw [h, Nat.zero_mul]
    omega
  · exact h

/-- (D4) Degree one never fails: an origin at degree `d+1` has `1 ≤ d`, at every cutoff. -/
theorem origin_degree_pos {q d : ℕ} (O : Origin q (d+1)) : 1 ≤ d := by
  by_contra h
  have e : q * (d+1) = q := by rw [show d = 0 by omega]; ring
  have small : O.V.card ≤ q := by have := O.order; omega
  obtain ⟨t, ht, sink⟩ := exists_sink O.free O.ne small
  have deg := O.deg t ht
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (outN O.G O.V t).card by omega)
  exact sink z (mem_outN.mp hz).1 (mem_outN.mp hz).2

/-- (B1) A valid proper unit state has `q*d+2 ≤ |U|`, and its origin has `q*d+3 ≤ |V|`. -/
theorem unit_state_card {q d : ℕ} (O : Origin q (d+1)) {st : State} (valid : Valid O st)
    (proper : st.U.card < O.V.card) (unit : total (d+1) st.H st.U = 1)
    (lower : OrderLaw q d (q*d+1)) :
    q*d+2 ≤ st.U.card ∧ q*d+3 ≤ O.V.card := by
  have := unit_order_of_total valid.2.2 lower (origin_cutoff_pos O) (origin_degree_pos O) unit
  omega

/-- (B1) At cutoff 3 the orders are forced: `|U| = 3d+2`, `|V| = 3(d+1)`. -/
theorem unit_state_three {d : ℕ} (O : Origin 3 (d+1)) {st : State} (valid : Valid O st)
    (proper : st.U.card < O.V.card) (unit : total (d+1) st.H st.U = 1)
    (lower : OrderLaw 3 d (3*d+1)) :
    st.U.card = 3*d+2 ∧ O.V.card = 3*(d+1) := by
  have := unit_state_card O valid proper unit lower
  have := O.order
  omega

/-- (B2) The exact-cost alternative at cutoff 3 is a unit graph on `3d+2` vertices. -/
theorem middle_three {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (P : Origin 3 (d+1)) (v : ℕ) (t : State) (same : P.V.card = O.V.card) (hv : v ∈ P.V)
    (ht : t.U = P.V.erase v) (reach : Reach (RStep 3 (d+1)) P.init t)
    (unit : total (d+1) t.H t.U = 1) :
    O.V.card = 3*(d+1) ∧ t.U.card = 3*d+2 ∧ QFree t.H t.U 3 ∧ total (d+1) t.H t.U = 1 := by
  have valid := rreach_valid P reach
  have proper : t.U.card < P.V.card := by rw [ht]; exact card_lt_card (erase_ssubset hv)
  obtain ⟨c1, c2⟩ := unit_state_three P valid proper unit fr.lower
  exact ⟨by omega, c1, valid.2.2, unit⟩

/-! ## Part C -/

/-- Two tight rows on `q*d+2` vertices. -/
def QTwoTight (q d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U q → U.card = q*d+2 →
    (∀ x ∈ U, d ≤ (outN E U x).card) → 2 ≤ (U.filter (fun x => (outN E U x).card = d)).card

/-- Two tight rows on `3d+2` vertices, cutoff 3. -/
abbrev TwoTight (d : ℕ) : Prop := QTwoTight 3 d

/-- Every heavy row has a tight head, on `q*d+1` vertices. -/
def QHeavyTightHead (q d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (W : Finset ℕ), QFree E W q → W.card = q*d+1 →
    (∀ x ∈ W, d ≤ (outN E W x).card) →
    ∀ x ∈ W, d+1 ≤ (outN E W x).card → ∃ a ∈ outN E W x, (outN E W a).card = d

/-- Every heavy row has a tight head, on `3d+1` vertices, cutoff 3. -/
abbrev HeavyTightHead (d : ℕ) : Prop := QHeavyTightHead 3 d

/-- (C1) row form: only `u` is tight, so `QTwoTight` fails. -/
theorem unit_false_of_twoTight_row {D : CH.Digraph} {U : Finset ℕ} {q d u : ℕ}
    (law : QTwoTight q d) (free : QFree D U q) (size : U.card = q*d+2)
    (short : (outN D U u).card = d) (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) : False := by
  have two := law D U free size (fun x hx => by
    by_cases e : x = u
    · rw [e]; omega
    · have := full x hx e; omega)
  have sub : U.filter (fun x => (outN D U x).card = d) ⊆ {u} := by
    intro x hx
    obtain ⟨xU, e⟩ := mem_filter.mp hx
    rw [mem_singleton]
    by_contra ne
    have := full x xU ne
    omega
  have := card_le_card sub
  rw [card_singleton] at this
  omega

/-- (C1) A unit graph on `q*d+2` vertices contradicts `QTwoTight q d`. -/
theorem unit_false_of_twoTight {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (law : QTwoTight q d) (free : QFree D U q) (size : U.card = q*d+2)
    (unit : total (d+1) D U = 1) : False := by
  obtain ⟨u, _, short, full⟩ := unit_profile unit
  exact unit_false_of_twoTight_row law free size (by omega) full

/-- (C2) The half law gives two tight rows. -/
theorem twoTight_of_halfLaw {d : ℕ} (hd : 1 ≤ d) (H : HalfLaw d) : TwoTight d := by
  intro E U free size deg
  have := H E U free size deg
  omega

/-- (C2) The tight-row law gives two tight rows. -/
theorem twoTight_of_tightLaw {d : ℕ} (T : TightLaw 3 d) : TwoTight d := by
  intro E U free size deg
  have := T E U free (by omega) deg
  omega

theorem twoTight_one : TwoTight 1 := twoTight_of_halfLaw le_rfl halfLaw_one

theorem twoTight_two : TwoTight 2 := twoTight_of_halfLaw (by omega) halfLaw_two

theorem twoTight_three : TwoTight 3 := twoTight_of_halfLaw (by omega) halfLaw_three

theorem twoTight_small {d : ℕ} (h1 : 1 ≤ d) (h3 : d ≤ 3) : TwoTight d := by
  interval_cases d
  · exact twoTight_one
  · exact twoTight_two
  · exact twoTight_three

/-- (C3) row form: for `3 ≤ q`, `1 ≤ d` a unit graph on `q*d+2` vertices contradicts `QHeavyTightHead q d`. -/
theorem unit_false_of_heavyTightHead_row {D : CH.Digraph} {U : Finset ℕ} {q d u : ℕ}
    (hq : 3 ≤ q) (hd : 1 ≤ d) (law : QHeavyTightHead q d) (free : QFree D U q)
    (size : U.card = q*d+2) (hu : u ∈ U) (short : (outN D U u).card = d)
    (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) : False := by
  have wsize : (U.erase u).card = q*d+1 := by rw [card_erase_of_mem hu]; omega
  have deg : ∀ x ∈ U.erase u, d ≤ (outN D (U.erase u) x).card := by
    intro x hx
    obtain ⟨xu, xU⟩ := mem_erase.mp hx
    rw [outN_erase]
    have := full x xU xu
    have := pred_card_le_card_erase (s := outN D U x) (a := u)
    omega
  obtain ⟨h, hh⟩ := card_pos.mp (show 0 < (outN D U u).card by omega)
  obtain ⟨hU, uh⟩ := mem_outN.mp hh
  have hne : h ≠ u := by
    rintro rfl
    exact loopfree free (by omega) hu uh
  have hW : h ∈ U.erase u := mem_erase.mpr ⟨hne, hU⟩
  have back : D h u ≠ true := fun e => digonfree free (by omega) hu hU uh e
  have hrow : outN D (U.erase u) h = outN D U h := by
    rw [outN_erase, erase_eq_of_notMem (fun m => back (mem_outN.mp m).2)]
  have heavy : d+1 ≤ (outN D (U.erase u) h).card := by rw [hrow]; exact full h hU hne
  obtain ⟨a, ha, tight⟩ := law D (U.erase u) (free.mono_set (erase_subset u U)) wsize deg h hW heavy
  obtain ⟨aW, ha'⟩ := mem_outN.mp ha
  obtain ⟨au, aU⟩ := mem_erase.mp aW
  have au' : D a u = true := by
    by_contra no
    have er : outN D (U.erase u) a = outN D U a := by
      rw [outN_erase, erase_eq_of_notMem (fun m => no (mem_outN.mp m).2)]
    rw [er] at tight
    have := full a aU au
    omega
  exact free u 3 (by omega) hq (.step hU uh (.step aU ha' (.step hu au' (.refl u))))

/-- (C3) A unit graph on `q*d+2` vertices contradicts `QHeavyTightHead q d` (`3 ≤ q`, `1 ≤ d`). -/
theorem unit_false_of_heavyTightHead {D : CH.Digraph} {U : Finset ℕ} {q d : ℕ}
    (hq : 3 ≤ q) (hd : 1 ≤ d) (law : QHeavyTightHead q d) (free : QFree D U q)
    (size : U.card = q*d+2) (unit : total (d+1) D U = 1) : False := by
  obtain ⟨u, hu, short, full⟩ := unit_profile unit
  exact unit_false_of_heavyTightHead_row hq hd law free size hu (by omega) full

/-- Thinning one row to a chosen subset of its heads keeps the cutoff. -/
theorem thin_row {E : CH.Digraph} {U S : Finset ℕ} {q x0 : ℕ} (free : QFree E U q)
    (hS : S ⊆ outN E U x0) :
    ∃ E' : CH.Digraph, QFree E' U q ∧ outN E' U x0 = S ∧ ∀ x, x ≠ x0 → outN E' U x = outN E U x := by
  classical
  refine ⟨fun a b => if a = x0 then decide (b ∈ S) else E a b, qfree_sub ?_ free, ?_, ?_⟩
  · intro a b h
    by_cases e : a = x0
    · simp only [e, ↓reduceIte, decide_eq_true_eq] at h
      rw [e]
      exact (mem_outN.mp (hS h)).2
    · simpa only [e, ↓reduceIte] using h
  · ext b
    simp only [mem_outN, ↓reduceIte, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨outN_subset (hS h), h⟩⟩
  · intro x ne
    ext b
    simp only [mem_outN, ne, ↓reduceIte]

/-- (C4) For `3 ≤ q`, `1 ≤ d`: every heavy row having a tight head forces two tight rows. -/
theorem twoTight_of_heavyTightHead {q d : ℕ} (hq : 3 ≤ q) (hd : 1 ≤ d) (law : QHeavyTightHead q d) :
    QTwoTight q d := by
  classical
  intro E U free size deg
  by_contra few
  push Not at few
  have notTight (x) (hx : x ∈ U) (e : (outN E U x).card = d) :
      x ∈ U.filter (fun x => (outN E U x).card = d) := mem_filter.mpr ⟨hx, e⟩
  rcases (show (U.filter (fun x => (outN E U x).card = d)).card = 0 ∨
      (U.filter (fun x => (outN E U x).card = d)).card = 1 by omega) with zero | one
  · obtain ⟨x0, hx0⟩ := card_pos.mp (show 0 < U.card by omega)
    obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq (deg x0 hx0)
    obtain ⟨E', free', row0, rows⟩ := thin_row free hS
    apply unit_false_of_heavyTightHead_row hq hd law free' size hx0 (by rw [row0, hSc])
    intro x hx ne
    rw [rows x ne]
    have := deg x hx
    have : (outN E U x).card ≠ d := fun e => by
      have m := notTight x hx e
      rw [card_eq_zero.mp zero] at m
      exact absurd m (notMem_empty x)
    omega
  · obtain ⟨u, hu⟩ := card_eq_one.mp one
    have uin : u ∈ U.filter (fun x => (outN E U x).card = d) := by rw [hu]; exact mem_singleton_self u
    obtain ⟨uU, ushort⟩ := mem_filter.mp uin
    apply unit_false_of_heavyTightHead_row hq hd law free size uU ushort
    intro x hx ne
    have := deg x hx
    have : (outN E U x).card ≠ d := fun e => by
      have m := notTight x hx e
      rw [hu, mem_singleton] at m
      exact ne m
    omega

/-- (C4) Out-regularity at the boundary order makes `HeavyTightHead` vacuous. -/
theorem heavyTightHead_of_boundaryRegular {d : ℕ} (reg : BoundaryRegular d) : HeavyTightHead d := by
  intro E W free size deg x hx heavy
  have := reg E W free size deg x hx
  omega

/-- (C4) A unit graph on `3d+2` vertices contradicts boundary out-regularity. -/
theorem unit_false_of_boundaryRegular {D : CH.Digraph} {U : Finset ℕ} {d : ℕ}
    (hd : 1 ≤ d) (reg : BoundaryRegular d) (free : QFree D U 3)
    (size : U.card = 3*d+2) (unit : total (d+1) D U = 1) : False :=
  unit_false_of_heavyTightHead le_rfl hd (heavyTightHead_of_boundaryRegular reg) free size unit

/-- (C4) A unit graph on `3d+2` vertices contradicts the absence of the top profile. -/
theorem unit_false_of_no_top_profile {D : CH.Digraph} {U : Finset ℕ} {d : ℕ}
    (hd : 1 ≤ d) (none : ¬ QProfile 3 (3*d) d) (free : QFree D U 3)
    (size : U.card = 3*d+2) (unit : total (d+1) D U = 1) : False :=
  unit_false_of_boundaryRegular hd (regular_of_not_profile_top none) free size unit

/-! ## Part D -/

/-- (D1) Under `TwoTight d` the exact-cost disjunct of `Alternatives` is impossible. -/
theorem middle_false_of_twoTight {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (law : TwoTight d) :
    ¬ ∃ (P : Origin 3 (d+1)) (v : ℕ) (t : State), P.V.card=O.V.card ∧
      MaximalReturns 3 P.G P.V ∧ v∈P.V ∧ t.U=P.V.erase v ∧
      Reach (RStep 3 (d+1)) P.init t ∧ total (d+1) t.H t.U=1 := by
  rintro ⟨P, v, t, same, _, hv, ht, reach, unit⟩
  obtain ⟨_, size, free, _⟩ := middle_three fr P v t same hv ht reach unit
  exact unit_false_of_twoTight law free size unit

/-- (D1) The same under `HeavyTightHead d`. -/
theorem middle_false_of_heavyTightHead {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (law : HeavyTightHead d) :
    ¬ ∃ (P : Origin 3 (d+1)) (v : ℕ) (t : State), P.V.card=O.V.card ∧
      MaximalReturns 3 P.G P.V ∧ v∈P.V ∧ t.U=P.V.erase v ∧
      Reach (RStep 3 (d+1)) P.init t ∧ total (d+1) t.H t.U=1 :=
  middle_false_of_twoTight fr (twoTight_of_heavyTightHead le_rfl (origin_degree_pos O) law)

/-- (D1) The same under `BoundaryRegular d`. -/
theorem middle_false_of_boundaryRegular {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (reg : BoundaryRegular d) :
    ¬ ∃ (P : Origin 3 (d+1)) (v : ℕ) (t : State), P.V.card=O.V.card ∧
      MaximalReturns 3 P.G P.V ∧ v∈P.V ∧ t.U=P.V.erase v ∧
      Reach (RStep 3 (d+1)) P.init t ∧ total (d+1) t.H t.U=1 :=
  middle_false_of_heavyTightHead fr (heavyTightHead_of_boundaryRegular reg)

/-- (D1) The same under `HalfLaw d`. -/
theorem middle_false_of_halfLaw {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (H : HalfLaw d) :
    ¬ ∃ (P : Origin 3 (d+1)) (v : ℕ) (t : State), P.V.card=O.V.card ∧
      MaximalReturns 3 P.G P.V ∧ v∈P.V ∧ t.U=P.V.erase v ∧
      Reach (RStep 3 (d+1)) P.init t ∧ total (d+1) t.H t.U=1 :=
  middle_false_of_twoTight fr (twoTight_of_halfLaw (origin_degree_pos O) H)

/-- (D2) Under `TwoTight d` the alternatives at cutoff 3 reduce to the first or the third. -/
theorem alternatives_three {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (alt : Alternatives O st) (law : TwoTight d) :
    (total (d+1) st.H st.U=d+1 ∧
      ∀ v∈O.V, (outN O.G O.V v).card=d+1 ∧ (BR45.inN O.G O.V v).card=d+1) ∨
    (total (d+1) st.H st.U<d+1 ∧ ∃ g e, 0<g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g)) := by
  rcases alt with first | middle | third
  · exact Or.inl first
  · exact absurd middle (middle_false_of_twoTight fr law)
  · exact Or.inr third

/-- (D2) The same under `HalfLaw d`. -/
theorem alternatives_three_of_halfLaw {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (alt : Alternatives O st) (H : HalfLaw d) :
    (total (d+1) st.H st.U=d+1 ∧
      ∀ v∈O.V, (outN O.G O.V v).card=d+1 ∧ (BR45.inN O.G O.V v).card=d+1) ∨
    (total (d+1) st.H st.U<d+1 ∧ ∃ g e, 0<g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g)) :=
  alternatives_three fr alt (twoTight_of_halfLaw (origin_degree_pos O) H)

/-- (D3) For `d ≤ 3` no law is needed. -/
theorem alternatives_three_small {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (alt : Alternatives O st) (hd3 : d ≤ 3) :
    (total (d+1) st.H st.U=d+1 ∧
      ∀ v∈O.V, (outN O.G O.V v).card=d+1 ∧ (BR45.inN O.G O.V v).card=d+1) ∨
    (total (d+1) st.H st.U<d+1 ∧ ∃ g e, 0<g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g)) :=
  alternatives_three fr alt (twoTight_small (origin_degree_pos O) hd3)

end LeanCH.BR.Closure.UnitState

open LeanCH.BR.Closure.UnitState in
#print axioms unit_order_lower
open LeanCH.BR.Closure.UnitState in
#print axioms unit_low_row
open LeanCH.BR.Closure.UnitState in
#print axioms unit_pair
open LeanCH.BR.Closure.UnitState in
#print axioms unit_parents_dominate
open LeanCH.BR.Closure.UnitState in
#print axioms unit_order_of_total
open LeanCH.BR.Closure.UnitState in
#print axioms unit_low_row_of_total
open LeanCH.BR.Closure.UnitState in
#print axioms unit_pair_of_total
open LeanCH.BR.Closure.UnitState in
#print axioms unit_parents_dominate_of_total
open LeanCH.BR.Closure.UnitState in
#print axioms origin_degree_pos
open LeanCH.BR.Closure.UnitState in
#print axioms unit_state_card
open LeanCH.BR.Closure.UnitState in
#print axioms unit_state_three
open LeanCH.BR.Closure.UnitState in
#print axioms middle_three
open LeanCH.BR.Closure.UnitState in
#print axioms unit_false_of_twoTight
open LeanCH.BR.Closure.UnitState in
#print axioms twoTight_of_halfLaw
open LeanCH.BR.Closure.UnitState in
#print axioms twoTight_of_tightLaw
open LeanCH.BR.Closure.UnitState in
#print axioms twoTight_small
open LeanCH.BR.Closure.UnitState in
#print axioms unit_false_of_heavyTightHead
open LeanCH.BR.Closure.UnitState in
#print axioms thin_row
open LeanCH.BR.Closure.UnitState in
#print axioms twoTight_of_heavyTightHead
open LeanCH.BR.Closure.UnitState in
#print axioms heavyTightHead_of_boundaryRegular
open LeanCH.BR.Closure.UnitState in
#print axioms unit_false_of_boundaryRegular
open LeanCH.BR.Closure.UnitState in
#print axioms unit_false_of_no_top_profile
open LeanCH.BR.Closure.UnitState in
#print axioms middle_false_of_twoTight
open LeanCH.BR.Closure.UnitState in
#print axioms middle_false_of_heavyTightHead
open LeanCH.BR.Closure.UnitState in
#print axioms middle_false_of_boundaryRegular
open LeanCH.BR.Closure.UnitState in
#print axioms middle_false_of_halfLaw
open LeanCH.BR.Closure.UnitState in
#print axioms alternatives_three
open LeanCH.BR.Closure.UnitState in
#print axioms alternatives_three_of_halfLaw
open LeanCH.BR.Closure.UnitState in
#print axioms alternatives_three_small
