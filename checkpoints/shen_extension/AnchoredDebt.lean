import checkpoints.shen_extension.NativeDistance

/-!
# One debt law in every free parameter found so far

`anchored_debt` leaves free, at once:

* the carrier `W ⊆ V` (any survivor set, no bank size condition),
* the weights `μ` of total at most `q t` (zero deletes a label, two copies it),
* the cut `C` (any cut; its losses are charged where they fall, no spare budget is assumed),
* the anchor `p` (any label of `V`, erased or not) and the radius `g` with `2 (g + 1) < q + 4`.

Rows that point to `p` may take any label of `W` within `g` native steps after `p` that they miss
and that does not return to them within `q - 1` retained arcs. The law: some row of positive weight
stays below quota in weight.

Instances (see the examples at the end and `AnchoredDebtChecks`): the shared-parent debt and its
radius-`g` form (unit weights on `V \ B`), the copy allocation rule (no anchored row used), the
swapped bank (carrier with `x` exchanged for an erased label, anchor `x`), copy-and-bypass
(weight two on one label, anchor `x`).
-/

namespace LeanCH.BR.AnchoredDebt
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay BypassTwoStepRow JointShortcut
  JointShortcutReplay LoneRow WeightedJoint NativeDistance

variable {D : CH.Digraph} {V : Finset ℕ} {q t : ℕ}

/-- **Anchored weighted debt.** -/
theorem anchored_debt {p g : ℕ} (free : QFree D V q) (none : NoHost q t) {W : Finset ℕ}
    (wv : W ⊆ V) (pv : p ∈ V) (μ : ℕ → ℕ) (pos : ∃ v ∈ W, 0 < μ v)
    (mass : ∑ v ∈ W, μ v ≤ q*t) (room : 2 * (g + 1) < q + 4) (C : ℕ → Finset ℕ) :
    ∃ u ∈ W, 0 < μ u ∧
      ∑ w ∈ outN D W u \ C u, μ w +
        (if D u p = true then ∑ w ∈ clearBall D (cut D C) V W q g p u, μ w else 0) < t := by
  classical
  by_contra bad
  push Not at bad
  let F : Finset Arc := (W ×ˢ W).filter
    (fun j => D j.1 p = true ∧ j.2 ∈ clearBall D (cut D C) V W q g p j.1)
  have memF : ∀ j, j ∈ F ↔ j.1 ∈ W ∧ j.2 ∈ W ∧ D j.1 p = true ∧
      j.2 ∈ clearBall D (cut D C) V W q g p j.1 := by
    intro j
    simp only [F, mem_filter, mem_product, and_assoc]
  have inW : ∀ j ∈ F, j.2 ∈ W := fun j jF => ((memF j).mp jF).2.1
  have props : ∀ j ∈ F, after D V p g j.2 ∧ D j.1 j.2 ≠ true ∧
      ∀ d, d + 1 ≤ q → ¬ Walk (cut D C) W j.2 j.1 d :=
    fun j jF => (mem_filter.mp ((memF j).mp jF).2.2.2).2
  have safe : QFree (install (cut D C) F) W q := by
    refine (near_iff free wv cut_sub inW room ?_).mpr (fun j jF => (props j jF).2.2)
    intro j jF j' jF'
    obtain ⟨i, ipos, ile, route⟩ := (props j jF).1
    exact ⟨i + 1, by omega, by omega, .step pv ((memF j').mp jF').2.2.1 route⟩
  refine weighted_exit none μ safe pos mass (fun u uW upos => ?_)
  have need := bad u uW upos
  have keep : outN D W u \ C u ⊆ outN (install (cut D C) F) W u := by
    intro w hw
    obtain ⟨oldw, off⟩ := mem_sdiff.mp hw
    obtain ⟨ww, arc⟩ := mem_outN.mp oldw
    exact mem_outN.mpr ⟨ww, install_old (by simp [cut, arc, off])⟩
  by_cases up : D u p = true
  · simp only [up, ↓reduceIte] at need
    have new : clearBall D (cut D C) V W q g p u ⊆ outN (install (cut D C) F) W u := by
      intro z hz
      exact mem_outN.mpr ⟨(mem_filter.mp hz).1,
        install_new ((memF (u, z)).mpr ⟨uW, (mem_filter.mp hz).1, up, hz⟩)⟩
    have dis : Disjoint (outN D W u \ C u) (clearBall D (cut D C) V W q g p u) := by
      rw [disjoint_left]
      intro z hz hc
      exact (mem_filter.mp hc).2.2.1 (mem_outN.mp (mem_sdiff.mp hz).1).2
    rw [← sum_union dis] at need
    exact need.trans (sum_le_sum_of_subset (union_subset keep new))
  · simp only [up, Bool.false_eq_true, ↓reduceIte, add_zero] at need
    exact need.trans (sum_le_sum_of_subset keep)

/-- The law as one packet on a graph: every carrier, weighting, cut, anchor and radius. -/
structure Anchored (D : CH.Digraph) (V : Finset ℕ) (q t : ℕ) : Prop where
  debt : ∀ W ⊆ V, ∀ p ∈ V, ∀ μ : ℕ → ℕ, (∃ v ∈ W, 0 < μ v) → ∑ v ∈ W, μ v ≤ q*t →
    ∀ g, 2 * (g + 1) < q + 4 → ∀ C : ℕ → Finset ℕ,
    ∃ u ∈ W, 0 < μ u ∧
      ∑ w ∈ outN D W u \ C u, μ w +
        (if D u p = true then ∑ w ∈ clearBall D (cut D C) V W q g p u, μ w else 0) < t

@[aesop safe forward (immediate := [free,none]) (rule_sets := [CHGraphFamilies])]
theorem anchored (free : QFree D V q) (none : NoHost q t) : Anchored D V q t :=
  ⟨fun _ wv _ pv μ pos mass _ room C => anchored_debt free none wv pv μ pos mass room C⟩

/-! ### Instances -/

/-- Unit weights on the survivors of a bank, cut inside spare, short rows sharing `p`:
the radius-`g` shared-parent debt. -/
theorem unit_instance {B : Finset ℕ} {p g : ℕ} {C : ℕ → Finset ℕ} (law : Anchored D V q t)
    (bank : Eligible V B q t) (pv : p ∈ V) (room : 2 * (g + 1) < q + 4)
    (budget : ∀ c ∈ V \ B, (C c).card ≤ spare D (V \ B) t c) :
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      (D u p = true → (clearBall D (cut D C) V (V \ B) q g p u).card +
        (outN D (V \ B) u).card < t) := by
  have card := card_sdiff_add_card_eq_card bank.sub
  have size := bank.size
  obtain ⟨u, uu, _, low⟩ := law.debt (V \ B) sdiff_subset p pv (fun _ => 1)
    (by obtain ⟨v, hv⟩ := bank.live; exact ⟨v, hv, by decide⟩)
    (by simp only [sum_const, smul_eq_mul, mul_one]; omega) g room C
  simp only [sum_const, smul_eq_mul, mul_one] at low
  have b : (C u).card ≤ (outN D (V \ B) u).card - t := budget u uu
  have k := le_card_sdiff (C u) (outN D (V \ B) u)
  have short : (outN D (V \ B) u).card < t := by
    by_contra full
    omega
  refine ⟨u, uu, short, fun up => ?_⟩
  simp only [up, ↓reduceIte] at low
  have none' : C u = ∅ := card_eq_zero.mp (by omega)
  rw [none', sdiff_empty] at low
  omega

/-- No anchored row used, weight zero on the slots `S` and one extra unit on each label that a slot
is assigned to: the copy allocation rule, with an arbitrary cut. -/
theorem copy_instance {W : Finset ℕ} {p : ℕ} (law : Anchored D V q t) (wv : W ⊆ V) (pv : p ∈ V)
    (μ : ℕ → ℕ) (pos : ∃ v ∈ W, 0 < μ v) (mass : ∑ v ∈ W, μ v ≤ q*t)
    (off : ∀ u ∈ W, D u p ≠ true) (C : ℕ → Finset ℕ) :
    ∃ u ∈ W, 0 < μ u ∧ ∑ w ∈ outN D W u \ C u, μ w < t := by
  obtain ⟨u, uW, upos, low⟩ := law.debt W wv p pv μ pos mass 0 (by omega) C
  refine ⟨u, uW, upos, ?_⟩
  simp only [off u uW, Bool.false_eq_true, ↓reduceIte, add_zero] at low
  exact low

#print axioms anchored_debt
#print axioms anchored
#print axioms unit_instance
#print axioms copy_instance
end LeanCH.BR.AnchoredDebt
