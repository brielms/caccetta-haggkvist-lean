import LeanCH.BR.CH.Conjecture
import Mathlib.Data.Finset.Card

/-!
# Walks inside a vertex set (route to `BR(q,2)`), Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq2_attempt_subagent.md`, §1 (Fact 1.1) and §7 (Lean route).

* `Walk D W a b m`: a directed walk of exactly `m` arcs from `a` to `b` in `D`; every vertex after the start lies in
  `W`. A closed walk of positive length therefore lies entirely in `W`.
* `QFree D W q`: no closed walk of length `1..q` inside `W` (loops included, as closed walks of length one).
* `Walk.lastVisit`: a walk either never enters `u`, or splits at its last entry into `u`.
* `cycle_of_closedWalk` (Fact 1.1, the new general lemma): in a loopless digraph on `range n`, a closed walk of
  length `ℓ ≥ 1` gives a simple directed cycle of length at most `ℓ` (`CH.HasDirectedCycleAtMost G n ℓ`).
* `qfree_of_noShort`: hence `¬ CH.HasDirectedCycleAtMost G n q` gives `QFree G (range n) q`.
-/

namespace LeanCH.BR.BRq2

/-- A directed walk of exactly `m` arcs from `a` to `b` in `D`, all of whose vertices after the start lie in `W`. -/
inductive Walk (D : CH.Digraph) (W : Finset ℕ) : ℕ → ℕ → ℕ → Prop
  | refl (a : ℕ) : Walk D W a a 0
  | step {a b c k : ℕ} : b ∈ W → D a b = true → Walk D W b c k → Walk D W a c (k + 1)

/-- No closed walk of length `1..q` inside `W`. -/
def QFree (D : CH.Digraph) (W : Finset ℕ) (q : ℕ) : Prop :=
  ∀ a ℓ, 1 ≤ ℓ → ℓ ≤ q → ¬ Walk D W a a ℓ

namespace Walk

variable {D E : CH.Digraph} {W W' : Finset ℕ}

theorem mono (h : W ⊆ W') {a b m : ℕ} (w : Walk D W a b m) : Walk D W' a b m := by
  induction w with
  | refl a => exact .refl a
  | step hb hab _ ih => exact .step (h hb) hab ih

theorem congr (h : ∀ a b, b ∈ W → D a b = E a b) {a b m : ℕ} (w : Walk D W a b m) : Walk E W a b m := by
  induction w with
  | refl a => exact .refl a
  | step hb hab _ ih => exact .step hb (by rw [← h _ _ hb]; exact hab) ih

theorem append {a b c m m' : ℕ} (w1 : Walk D W a b m) (w2 : Walk D W b c m') : Walk D W a c (m + m') := by
  induction w1 with
  | refl a => simpa using w2
  | step hb hab _ ih =>
    rw [show ∀ k, k + 1 + m' = k + m' + 1 from fun k => by omega]
    exact .step hb hab (ih w2)

theorem snoc {a b c m : ℕ} (w : Walk D W a b m) (hc : c ∈ W) (hbc : D b c = true) : Walk D W a c (m + 1) :=
  w.append (.step hc hbc (.refl c))

theorem unsnoc {a b m : ℕ} (w : Walk D W a b (m + 1)) : ∃ y, Walk D W a y m ∧ b ∈ W ∧ D y b = true := by
  induction m generalizing a with
  | zero =>
    cases w with
    | step hb hab w' => cases w'; exact ⟨a, .refl a, hb, hab⟩
  | succ m ih =>
    cases w with
    | step hb hab w' =>
      obtain ⟨y, wy, hyb, hy⟩ := ih w'
      exact ⟨y, .step hb hab wy, hyb, hy⟩

theorem end_mem_or {a b m : ℕ} (w : Walk D W a b m) : b = a ∨ b ∈ W := by
  induction w with
  | refl => exact Or.inl rfl
  | step hb _ _ ih =>
    right
    rcases ih with rfl | h
    · exact hb
    · exact h

/-- A walk either never enters `u`, or splits at its last entry into `u` (the tail then never enters `u`). -/
theorem lastVisit (u : ℕ) {a b m : ℕ} (w : Walk D W a b m) :
    Walk D (W.erase u) a b m ∨
      ∃ m1 m2, 0 < m1 ∧ m1 + m2 = m ∧ Walk D W a u m1 ∧ Walk D (W.erase u) u b m2 := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a b c k hb hab _ ih =>
    rcases ih with h | ⟨m1, m2, h0, hsum, w1, w2⟩
    · by_cases hbu : b = u
      · subst hbu
        exact Or.inr ⟨1, k, by omega, by omega, .step hb hab (.refl _), h⟩
      · exact Or.inl (.step (Finset.mem_erase.mpr ⟨hbu, hb⟩) hab h)
    · exact Or.inr ⟨m1 + 1, m2, by omega, by omega, .step hb hab w1, w2⟩

/-- A walk from `u` has a suffix from `u`, no longer, that never re-enters `u`. -/
theorem fromStart {u b m : ℕ} (w : Walk D W u b m) : ∃ m', m' ≤ m ∧ Walk D (W.erase u) u b m' := by
  rcases w.lastVisit u with h | ⟨m1, m2, _, hsum, _, w2⟩
  · exact ⟨m, le_rfl, h⟩
  · exact ⟨m2, by omega, w2⟩

/-- A walk as a vertex sequence. -/
theorem toFun {a b m : ℕ} (w : Walk D W a b m) :
    ∃ f : ℕ → ℕ, f 0 = a ∧ f m = b ∧ ∀ i, i < m → f (i + 1) ∈ W ∧ D (f i) (f (i + 1)) = true := by
  induction w with
  | refl a => exact ⟨fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @step a b c k hb hab _ ih =>
    obtain ⟨f, f0, fk, hf⟩ := ih
    refine ⟨fun i => if i = 0 then a else f (i - 1), by simp, by simp [fk], ?_⟩
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [f0, hb, hab]
    · have h := hf (i - 1) (by omega)
      have e : i - 1 + 1 = i := by omega
      rw [e] at h
      simp only [show i + 1 ≠ 0 by omega, show i ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
      exact h

end Walk

theorem QFree.mono_set {D : CH.Digraph} {W W' : Finset ℕ} {q : ℕ} (h : W ⊆ W') (hf : QFree D W' q) :
    QFree D W q :=
  fun a ℓ h1 hq w => hf a ℓ h1 hq (w.mono h)

theorem QFree.mono_bound {D : CH.Digraph} {W : Finset ℕ} {q q' : ℕ} (h : q' ≤ q) (hf : QFree D W q) :
    QFree D W q' :=
  fun a ℓ h1 hq w => hf a ℓ h1 (hq.trans h) w

theorem edgesFrom_map_range (G : CH.Digraph) :
    ∀ (len : ℕ) (h : ℕ → ℕ), (∀ i, i < len → G (h i) (h (i + 1)) = true) →
      CH.EdgesFrom G (h 0) ((List.range len).map (fun i => h (i + 1)))
  | 0, _, _ => trivial
  | len + 1, h, hh => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine ⟨hh 0 (by omega), ?_⟩
    exact edgesFrom_map_range G len (fun i => h (i + 1)) (fun i hi => hh (i + 1) (by omega))

/-- Fact 1.1 for vertex sequences: a closed sequence-walk of length `ℓ ≥ 1` in a loopless digraph on `range n`
contains a simple directed cycle of length at most `ℓ`. -/
theorem cycle_of_closedFun {G : CH.Digraph} {n : ℕ} (loopless : CH.Loopless G n) :
    ∀ ℓ (f : ℕ → ℕ), 1 ≤ ℓ → f ℓ = f 0 →
      (∀ i, i < ℓ → f (i + 1) < n ∧ G (f i) (f (i + 1)) = true) →
      CH.HasDirectedCycleAtMost G n ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
  intro f hℓ hcl hf
  by_cases hrep : ∃ i j, i < j ∧ j < ℓ ∧ f i = f j
  · -- a repeated vertex: pass to the shorter closed walk between the two visits
    obtain ⟨i, j, hij, hjl, hfij⟩ := hrep
    obtain ⟨L, hL, hlen⟩ := ih (j - i) (by omega) (fun t => f (i + t)) (by omega)
      (by show f (i + (j - i)) = f (i + 0); rw [Nat.add_sub_cancel' hij.le, Nat.add_zero, hfij])
      (fun t ht => hf (i + t) (by omega))
    exact ⟨L, hL, by omega⟩
  · have hinj : ∀ i j, i < j → j < ℓ → f i ≠ f j := fun i j h1 h2 h3 => hrep ⟨i, j, h1, h2, h3⟩
    have h2 : 2 ≤ ℓ := by
      by_contra h
      have hl1 : ℓ = 1 := by omega
      subst hl1
      obtain ⟨hn, hG⟩ := hf 0 (by omega)
      have e : f (0 + 1) = f 0 := hcl
      rw [e] at hn hG
      rw [loopless _ hn] at hG
      exact Bool.false_ne_true hG
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by omega⟩
    have hcl' : f (m + 1 + 1) = f 0 := hcl
    refine ⟨(List.range (m + 2)).map f, ?_, by simp⟩
    have hshape : (List.range (m + 2)).map f = f 0 :: (List.range (m + 1)).map (fun i => f (i + 1)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl
    rw [hshape]
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · rw [← hshape]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro x hx y hy hxy
      simp only [List.mem_range] at hx hy
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact hinj x y h hy hxy
      · exact hinj y x h hx hxy.symm
    · intro v hv
      rw [← hshape] at hv
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
      simp only [List.mem_range] at hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [← hcl']; exact (hf (m + 1) (by omega)).1
      · have := (hf (i - 1) (by omega)).1
        rwa [Nat.sub_add_cancel hpos] at this
    · exact edgesFrom_map_range G (m + 1) f (fun i hi => (hf i (by omega)).2)
    · rw [List.range_succ, List.map_append, List.map_singleton, List.getLastD_concat]
      have := (hf (m + 1) (by omega)).2
      rw [hcl'] at this
      exact this

/-- Fact 1.1: a closed walk of length `ℓ ≥ 1` on `range n` gives a simple cycle of length at most `ℓ`. -/
theorem cycle_of_closedWalk {G : CH.Digraph} {n : ℕ} (loopless : CH.Loopless G n) {a ℓ : ℕ}
    (w : Walk G (Finset.range n) a a ℓ) (hℓ : 1 ≤ ℓ) : CH.HasDirectedCycleAtMost G n ℓ := by
  obtain ⟨f, f0, fl, hf⟩ := w.toFun
  exact cycle_of_closedFun loopless ℓ f hℓ (by rw [fl, f0])
    (fun i hi => ⟨Finset.mem_range.mp (hf i hi).1, (hf i hi).2⟩)

theorem qfree_of_noShort {G : CH.Digraph} {n q : ℕ} (loopless : CH.Loopless G n)
    (noShort : ¬ CH.HasDirectedCycleAtMost G n q) : QFree G (Finset.range n) q := by
  intro a ℓ h1 hq w
  obtain ⟨L, hL, hlen⟩ := cycle_of_closedWalk loopless w h1
  exact noShort ⟨L, hL, hlen.trans hq⟩

end LeanCH.BR.BRq2
