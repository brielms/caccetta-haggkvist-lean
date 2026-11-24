import checkpoints.shen_extension.DeleteRepairUnlock
import Mathlib.Tactic

/-!
# Transition closure: apply every rule, recursively, and say where it ends

Lean 4.35.0. Own file; `Capstone.lean` is not touched. Skeleton, version 1 (18 Nov 2026).

The capstone applies each compiled rule once to the counterexample and keeps the result as a fact. This file sets
up the other reading: one kind of state, an explicit list of rules, reachability under any number of rule
applications in any order, and a definition of where a road ends.

## Part A (no graph theory)

* `Reach step a b`: `b` is obtained from `a` by applying rules any number of times.
* `Terminal step a`: no rule applies to `a`.
* `invariant_of_reach`: a property kept by every rule holds at every reachable state.
* `reach_terminal_of_measure`: if something drops on every rule, every state reaches a terminal state.
* `terminal_or_cycle`: on a finite state space, every state reaches a terminal state or a closed cycle.

## Part B (the first three rules, all on one state type)

A state is the set of surviving labels together with the current arcs on them. The origin is a least-order
source. Rules in version 1: delete vertices, cut arcs, add one safe arc at a short row.

* `reach_valid`: every reachable state is a valid state (labels inside the origin, nonempty, no short cycle).
* `reach_not_paid`: no reachable state on a proper set of labels has all rows full. This is the earlier one-step
  "stuck" theorem, now for every sequence of rules.
* `add_closure`: from any state the adding rule can be run to exhaustion, and it ends.
* `every_branch_reaches_stop`: from every reachable state on a proper set of labels, running the adding rule to
  exhaustion reaches a `Stop`: a valid state with a short row in which every short row is saturated (each of its
  non-heads walks back to it within `q-1` steps).
* `stop_not_terminal`: a `Stop` with at least two labels is NOT terminal for the full rule list: deletion still
  applies. So a `Stop` is where the adding rule ends, not where the system ends.
* `closure_capstone`: if no `Stop` can exist (`StopsImpossible`, a SUPPLIED HYPOTHESIS), there is no least-order
  source with at least two vertices.

Logical status of `StopsImpossible`: it quantifies over hypothetical sources (`Origin` includes `order`), so it
is not refuted by any graph that exists. By `stop_exists` every source with two vertices yields a stop, so for this
rule list `StopsImpossible q s` is EQUIVALENT to "no such source exists": proving it is exactly as hard as the
conjecture at `(q, s)`. Saturation alone gives no structural reason for a contradiction. Adding a rule to the list
adds a condition to `Stop`; whether a source still supplies a state meeting all the conditions has to be proved
each time (see `TransitionClosureRestore.lean`). Nothing here closes CH.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.DeleteRepair

/-! ## Part A. Rule systems in general -/

section General

variable {σ : Type*}

/-- Reachability: apply rules any number of times, in any order. -/
abbrev Reach (step : σ → σ → Prop) : σ → σ → Prop := Relation.ReflTransGen step

/-- A state is terminal when no rule applies to it. -/
def Terminal (step : σ → σ → Prop) (a : σ) : Prop := ∀ b, ¬ step a b

/-- A property kept by every rule holds at every reachable state. -/
theorem invariant_of_reach {step : σ → σ → Prop} {inv : σ → Prop}
    (pres : ∀ a b, inv a → step a b → inv b) {a b : σ} (ha : inv a) (r : Reach step a b) : inv b := by
  induction r with
  | refl => exact ha
  | tail _ hbc ih => exact pres _ _ ih hbc

/-- If something drops on every rule, every state reaches a terminal state. -/
theorem reach_terminal_of_measure {step : σ → σ → Prop} (μ : σ → ℕ)
    (drop : ∀ a b, step a b → μ b < μ a) (a : σ) : ∃ t, Reach step a t ∧ Terminal step t := by
  induction' h : μ a using Nat.strong_induction_on with n ih generalizing a
  by_cases term : Terminal step a
  · exact ⟨a, Relation.ReflTransGen.refl, term⟩
  · simp only [Terminal, not_forall, not_not] at term
    obtain ⟨b, hb⟩ := term
    obtain ⟨t, rt, tt⟩ := ih (μ b) (h ▸ drop a b hb) b rfl
    exact ⟨t, Relation.ReflTransGen.head hb rt, tt⟩

/-- On a finite state space, every state reaches a terminal state or a closed cycle. -/
theorem terminal_or_cycle [Finite σ] (step : σ → σ → Prop) (a : σ) :
    (∃ t, Reach step a t ∧ Terminal step t) ∨ ∃ c, Reach step a c ∧ Relation.TransGen step c c := by
  by_contra h
  rw [not_or] at h
  obtain ⟨noTerm, noCyc⟩ := h
  let R := {b // Reach step a b}
  let r : R → R → Prop := fun x y => Relation.TransGen step y.1 x.1
  have : IsTrans R r := ⟨fun _ _ _ hxy hyz => Relation.TransGen.trans hyz hxy⟩
  have : Std.Irrefl r := ⟨fun x hx => noCyc ⟨x.1, x.2, hx⟩⟩
  have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨m, _, hmin⟩ := wf.has_min Set.univ ⟨⟨a, Relation.ReflTransGen.refl⟩, trivial⟩
  apply noTerm
  refine ⟨m.1, m.2, ?_⟩
  intro b hb
  exact hmin ⟨b, m.2.tail hb⟩ trivial (Relation.TransGen.single hb)

end General

/-! ## Part B. States and the first three rules -/

/-- The origin: a HYPOTHETICAL source at cutoff `q` and degree `s`: a least-order `q`-free digraph with every
outdegree at least `s`, on at most `q*s` vertices. CH says no such object exists. -/
structure Origin (q s : ℕ) where
  G : CH.Digraph
  V : Finset ℕ
  ne : V.Nonempty
  order : V.card ≤ q * s
  free : QFree G V q
  least : Least q s V
  deg : ∀ x ∈ V, s ≤ (outN G V x).card

/-- A state: the surviving labels and the current arcs on them. -/
structure State where
  U : Finset ℕ
  H : CH.Digraph

variable {q s : ℕ}

/-- The starting state is the origin itself. -/
def Origin.init (O : Origin q s) : State := ⟨O.V, O.G⟩

/-- A valid state: labels inside the origin, nonempty, no closed walk of length `1..q`. -/
def Valid (O : Origin q s) (st : State) : Prop :=
  st.U ⊆ O.V ∧ st.U.Nonempty ∧ QFree st.H st.U q

/-- A short row: fewer than `s` heads among the surviving labels. -/
def Short (s : ℕ) (st : State) (u : ℕ) : Prop := u ∈ st.U ∧ (outN st.H st.U u).card < s

/-- A paid state: no short row. -/
def Paid (s : ℕ) (st : State) : Prop := ∀ u ∈ st.U, s ≤ (outN st.H st.U u).card

/-- Rule 1: delete vertices (keep at least one). -/
def DeleteStep (a b : State) : Prop := b.H = a.H ∧ b.U ⊂ a.U ∧ b.U.Nonempty

/-- Rule 2: cut arcs. -/
def CutStep (a b : State) : Prop :=
  b.U = a.U ∧ (∀ x y, b.H x y = true → a.H x y = true) ∧
    ∃ x ∈ a.U, ∃ y ∈ a.U, a.H x y = true ∧ b.H x y ≠ true

/-- Rule 3: add one arc `u → z` at a short row `u`, when `z` does not walk back to `u` within `q-1` steps. -/
def AddStep (q s : ℕ) (a b : State) : Prop :=
  ∃ u z, Short s a u ∧ z ∈ a.U ∧ a.H u z ≠ true ∧ (∀ m, m + 1 ≤ q → ¬ Walk a.H a.U z u m) ∧
    b.U = a.U ∧ b.H = repair a.H {u} (fun _ => {z})

/-- The rule list, version 1. -/
inductive Step (q s : ℕ) : State → State → Prop
  | delete {a b : State} : DeleteStep a b → Step q s a b
  | cut {a b : State} : CutStep a b → Step q s a b
  | add {a b : State} : AddStep q s a b → Step q s a b

/-- Every rule takes a valid state to a valid state. -/
theorem step_valid (O : Origin q s) {a b : State} (v : Valid O a) (h : Step q s a b) : Valid O b := by
  obtain ⟨sub, _, free⟩ := v
  cases h with
  | delete d =>
    obtain ⟨hH, hU, hne⟩ := d
    refine ⟨hU.subset.trans sub, hne, ?_⟩
    rw [hH]
    exact free.mono_set hU.subset
  | cut c =>
    obtain ⟨hU, hsub, _⟩ := c
    rw [← hU] at sub free
    exact ⟨sub, by rwa [hU], qfree_sub hsub free⟩
  | add ad =>
    obtain ⟨u, z, _, _, _, far, hU, hH⟩ := ad
    refine ⟨by rw [hU]; exact sub, by rwa [hU], ?_⟩
    rw [hU, hH]
    apply repair_qfree free
    intro u' hu' z' hz' u'' hu'' m hm
    rw [Finset.mem_singleton] at hu' hz' hu''
    subst hu' hz' hu''
    exact far m hm

theorem init_valid (O : Origin q s) : Valid O O.init := ⟨Finset.Subset.refl _, O.ne, O.free⟩

/-- **Every reachable state is valid**, whatever rules were applied and in whatever order. -/
theorem reach_valid (O : Origin q s) {st : State} (r : Reach (Step q s) O.init st) : Valid O st :=
  invariant_of_reach (inv := Valid O) (fun _ _ v h => step_valid O v h) (init_valid O) r

/-- A valid state on a proper set of labels is never paid. -/
theorem valid_not_paid (O : Origin q s) {st : State} (v : Valid O st) (proper : st.U.card < O.V.card) :
    ¬ Paid s st := by
  intro p
  have := O.least st.H st.U v.2.2 p v.2.1
  omega

/-- **No sequence of rules reaches a paid state on a proper set of labels.** -/
theorem reach_not_paid (O : Origin q s) {st : State} (r : Reach (Step q s) O.init st)
    (proper : st.U.card < O.V.card) : ¬ Paid s st :=
  valid_not_paid O (reach_valid O r) proper

/-! ### Running the adding rule to exhaustion -/

/-- Number of ordered pairs of surviving labels with no arc. It drops on every adding step. -/
def nonArcs (st : State) : ℕ := ((st.U ×ˢ st.U).filter (fun p => st.H p.1 p.2 ≠ true)).card

theorem add_drops {a b : State} (h : AddStep q s a b) : nonArcs b < nonArcs a := by
  obtain ⟨u, z, hu, hz, hne, _, hU, hH⟩ := h
  unfold nonArcs
  rw [hU, hH]
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp1, fun old => hp2 (repair_old old)⟩
  · intro hsub
    have mem : (u, z) ∈ (a.U ×ˢ a.U).filter (fun p => a.H p.1 p.2 ≠ true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu.1, hz⟩, hne⟩
    have := (Finset.mem_filter.mp (hsub mem)).2
    exact this (repair_new (Finset.mem_singleton_self u) (Finset.mem_singleton_self z))

/-- **The adding rule always ends.** -/
theorem add_closure (q s : ℕ) (a : State) :
    ∃ t, Reach (AddStep q s) a t ∧ Terminal (AddStep q s) t :=
  reach_terminal_of_measure nonArcs (fun _ _ h => add_drops h) a

theorem add_reach_carrier {a t : State} (r : Reach (AddStep q s) a t) : t.U = a.U :=
  invariant_of_reach (inv := fun x => x.U = a.U)
    (fun _ _ hx h => by obtain ⟨_, _, _, _, _, _, hU, _⟩ := h; exact hU.trans hx) rfl r

theorem add_reach_step {a t : State} (r : Reach (AddStep q s) a t) : Reach (Step q s) a t := by
  induction r with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail (Step.add h)

/-- A saturated state: every non-head of every short row walks back to that row within `q-1` steps. -/
def Saturated (q s : ℕ) (st : State) : Prop :=
  ∀ u, Short s st u → ∀ z ∈ st.U, st.H u z ≠ true → ∃ m, m + 1 ≤ q ∧ Walk st.H st.U z u m

/-- Where the adding rule ends is exactly a saturated state. -/
theorem addTerminal_iff_saturated (st : State) : Terminal (AddStep q s) st ↔ Saturated q s st := by
  constructor
  · intro term u hu z hz hne
    by_contra h
    push Not at h
    exact term ⟨st.U, repair st.H {u} (fun _ => {z})⟩ ⟨u, z, hu, hz, hne, h, rfl, rfl⟩
  · intro sat b ⟨u, z, hu, hz, hne, far, _, _⟩
    obtain ⟨m, hm, w⟩ := sat u hu z hz hne
    exact far m hm w

/-- A stop of the adding rule: valid, on a proper set of labels, with a short row, and saturated. -/
structure Stop (O : Origin q s) (st : State) : Prop where
  valid : Valid O st
  proper : st.U.card < O.V.card
  short : ∃ u, Short s st u
  saturated : Saturated q s st

/-- **From every reachable state on a proper set of labels, a stop is reachable on the same labels.** -/
theorem every_branch_reaches_stop (O : Origin q s) {st : State} (r : Reach (Step q s) O.init st)
    (proper : st.U.card < O.V.card) :
    ∃ t, Reach (Step q s) O.init t ∧ t.U = st.U ∧ Stop O t := by
  obtain ⟨t, rt, term⟩ := add_closure q s st
  have hU := add_reach_carrier rt
  have reach : Reach (Step q s) O.init t := r.trans (add_reach_step rt)
  have v := reach_valid O reach
  have prop' : t.U.card < O.V.card := by rw [hU]; exact proper
  have np := valid_not_paid O v prop'
  have short : ∃ u, Short s t u := by
    by_contra h
    push Not at h
    apply np
    intro u hu
    by_contra lt
    exact h u ⟨hu, by omega⟩
  exact ⟨t, reach, hU, ⟨v, prop', short, (addTerminal_iff_saturated t).mp term⟩⟩

/-- A stop exists as soon as the origin has two vertices: delete one vertex, then add to exhaustion. -/
theorem stop_exists (O : Origin q s) (two : 2 ≤ O.V.card) : ∃ t, Reach (Step q s) O.init t ∧ Stop O t := by
  obtain ⟨x, hx⟩ := O.ne
  have hne : (O.V.erase x).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx]; omega
  have del : Step q s O.init ⟨O.V.erase x, O.G⟩ :=
    Step.delete ⟨rfl, Finset.erase_ssubset hx, hne⟩
  have proper : (O.V.erase x).card < O.V.card := by rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨t, rt, _, stop⟩ := every_branch_reaches_stop O (Relation.ReflTransGen.single del) proper
  exact ⟨t, rt, stop⟩

/-- **A stop is not the end of the system.** With two or more labels the deleting rule still applies. -/
theorem stop_not_terminal (O : Origin q s) {st : State} (_stop : Stop O st) (two : 2 ≤ st.U.card) :
    ¬ Terminal (Step q s) st := by
  intro term
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < st.U.card)
  have hne : (st.U.erase x).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx]; omega
  exact term ⟨st.U.erase x, st.H⟩ (Step.delete ⟨rfl, Finset.erase_ssubset hx, hne⟩)

/-- SUPPLIED HYPOTHESIS for this rule list: no stop exists. Adding rules to the list makes `Stop` smaller. -/
def StopsImpossible (q s : ℕ) : Prop := ∀ (O : Origin q s) (st : State), Stop O st → False

/-- **Closure form of the capstone for the rule list of version 1.** -/
theorem closure_capstone (h : StopsImpossible q s) (O : Origin q s) (two : 2 ≤ O.V.card) : False := by
  obtain ⟨t, _, stop⟩ := stop_exists O two
  exact h O t stop

end LeanCH.BR.Closure

open LeanCH.BR.Closure in
#print axioms terminal_or_cycle
open LeanCH.BR.Closure in
#print axioms reach_not_paid
open LeanCH.BR.Closure in
#print axioms every_branch_reaches_stop
open LeanCH.BR.Closure in
#print axioms stop_not_terminal
open LeanCH.BR.Closure in
#print axioms closure_capstone
