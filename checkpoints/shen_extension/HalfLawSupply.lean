import checkpoints.shen_extension.HalfRowsThree

/-!
# The half law as the single supplier at cutoff 3

Lean 4.35.0. Paper: `checkpoints/shen_extension/triangle_20261118/HalfLaw_20261118.md`.

`HalfLaw d`: every `3`-free digraph on `3d+2` vertices with all outdegrees at least `d` has at least half its
rows of outdegree exactly `d`. It is a statement about digraphs that exist, so it can be tested.

* `halfLaw_one`, `halfLaw_two`, `halfLaw_three`: proved.
* `tightLaw_of_halfLaw`: `HalfLaw d` gives `TightRow.TightLaw 3 d` for `d ≥ 1`.
* `capstone_of_halfLaw`: `HalfLaw (s-1)` gives the literal capstone statement at `(3, s)` for `s ≥ 2`.
* `halfLaw_of_injection`: the half law for one digraph follows from any injection of its heavy rows into its
  tight rows (the matching form; the relation along which the injection is built is free).
* `no_source_of_halfLaw`: under `HalfLaw (s-1)`, `s ≥ 2`, there is no nonempty `3`-free digraph on at most `3s`
  vertices with all outdegrees at least `s` (the form used on a least-order source).

`HalfLaw d` for `d ≥ 4` is a SUPPLIED HYPOTHESIS here (d = 4 has a paper proof). Nothing here closes CH.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.HalfLawSupply

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.TightRow LeanCH.BR.HalfRows LeanCH.BR.HalfRowsThree

/-- The half law at degree `d` (cutoff 3). -/
def HalfLaw (d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U 3 → U.card = 3 * d + 2 →
    (∀ x ∈ U, d ≤ (outN E U x).card) →
    U.card ≤ 2 * (U.filter (fun x => (outN E U x).card = d)).card

theorem halfLaw_one : HalfLaw 1 := fun _ _ free card deg => half_small le_rfl (by omega) free card deg

theorem halfLaw_two : HalfLaw 2 := fun _ _ free card deg => half_small (by omega) le_rfl free card deg

theorem halfLaw_three : HalfLaw 3 := fun _ _ free card deg => half_three free card deg

/-- The half law gives the tight-row law. -/
theorem tightLaw_of_halfLaw {d : ℕ} (hd : 1 ≤ d) (H : HalfLaw d) : TightLaw 3 d := by
  intro E U free card deg
  have := H E U free (by omega) deg
  omega

/-- The literal capstone statement at `(3, s)` from the half law one degree down. -/
theorem capstone_of_halfLaw {n s : ℕ} {D : CH.Digraph} (hn : 0 < n) (hs : 2 ≤ s) (order : n ≤ 3 * s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s) (H : HalfLaw (s - 1)) :
    CH.HasDirectedCycleAtMost D n 3 :=
  capstone_of_tightLaw hn (by omega) order loop degree (tightLaw_of_halfLaw (by omega) H)

/-- Matching form: an injection of the heavy rows into the tight rows gives the half law for that digraph. -/
theorem halfLaw_of_injection {D : CH.Digraph} {V : Finset ℕ} {d : ℕ} (f : ℕ → ℕ)
    (maps : ∀ x ∈ V, (outN D V x).card ≠ d → f x ∈ V.filter (fun y => (outN D V y).card = d))
    (inj : ∀ x ∈ V, ∀ y ∈ V, (outN D V x).card ≠ d → (outN D V y).card ≠ d → f x = f y → x = y) :
    V.card ≤ 2 * (V.filter (fun x => (outN D V x).card = d)).card := by
  classical
  have split := Finset.card_filter_add_card_filter_not (s := V) (fun x => (outN D V x).card = d)
  have le : (V.filter (fun x => ¬ (outN D V x).card = d)).card ≤
      (V.filter (fun x => (outN D V x).card = d)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      obtain ⟨hxV, hne⟩ := Finset.mem_filter.mp hx
      exact maps x hxV hne
    · intro x hx y hy e
      obtain ⟨hxV, hnx⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyV, hny⟩ := Finset.mem_filter.mp hy
      exact inj x hxV y hyV hnx hny e
  omega

/-- Under the half law at `s-1` there is no hypothetical source at degree `s`. -/
theorem no_source_of_halfLaw {s : ℕ} (hs : 2 ≤ s) (H : HalfLaw (s - 1)) {D : CH.Digraph} {V : Finset ℕ}
    (free : QFree D V 3) (ne : V.Nonempty) (order : V.card ≤ 3 * s)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) : False := by
  have T : TightLaw 3 (s - 1) := tightLaw_of_halfLaw (by omega) H
  obtain ⟨D', V', f', c', d'⟩ := pad_to (q := 3) (s := s) (3 * s - V.card) D V free ne deg
  have ss : s - 1 + 1 = s := by omega
  have card : V'.card = 3 * (s - 1 + 1) := by rw [c', ss]; omega
  exact tightLaw_implies_CH T f' card (by rw [c']; have := Finset.card_pos.mpr ne; omega)
    (fun v hv => by have := d' v hv; omega)

end LeanCH.BR.HalfLawSupply

open LeanCH.BR.HalfLawSupply in
#print axioms halfLaw_three
open LeanCH.BR.HalfLawSupply in
#print axioms capstone_of_halfLaw
open LeanCH.BR.HalfLawSupply in
#print axioms halfLaw_of_injection
open LeanCH.BR.HalfLawSupply in
#print axioms no_source_of_halfLaw
