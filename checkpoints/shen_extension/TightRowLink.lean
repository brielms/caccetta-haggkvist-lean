import checkpoints.shen_extension.DeleteRepairUnlock
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The tight-row statement implies CH one degree up (compiled conditional rule)

Lean 4.35.0. Paper: `checkpoints/shen_extension/triangle_20261118/Triangle_ThreeLeads_20261118.md`.

`TightLaw q s` is a SUPPLIED HYPOTHESIS, not a theorem: on `q*(s+1) - 1` vertices, a `q`-free digraph with
minimum outdegree at least `s` has at least `s+2` vertices of outdegree exactly `s`. It is the case `e = q-1`
of the defect law, which is conjectural (exact computations only).

`tightLaw_implies_CH` is the compiled link: under `TightLaw q s` there is no `q`-free digraph on `q*(s+1)`
vertices with minimum outdegree at least `s+1`. Proof: trim to outdegree exactly `s+1`, delete a vertex of
indegree at most `s+1`; only its parents become tight.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.TightRow

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.DeleteRepair

/-- Supplied hypothesis (conjectural): the tight-row statement at `(q, s)`. -/
def TightLaw (q s : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U q → U.card + 1 = q * (s + 1) →
    (∀ x ∈ U, s ≤ (outN E U x).card) →
    s + 2 ≤ (U.filter (fun x => (outN E U x).card = s)).card

/-- Sum of indegrees equals sum of outdegrees on a vertex set. -/
theorem sum_indeg_eq_sum_outdeg (G : CH.Digraph) (V : Finset ℕ) :
    ∑ x ∈ V, (V.filter (fun y => G y x = true)).card = ∑ y ∈ V, (outN G V y).card := by
  simp only [outN, Finset.card_filter]
  exact Finset.sum_comm

/-- **Compiled link.** The tight-row statement at `(q, s)` excludes a `q`-free digraph on `q*(s+1)` vertices
with minimum outdegree at least `s+1`. -/
theorem tightLaw_implies_CH {q s : ℕ} (T : TightLaw q s) {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hV : V.card = q * (s + 1)) (hpos : 0 < V.card)
    (deg : ∀ v ∈ V, s + 1 ≤ (outN D V v).card) : False := by
  obtain ⟨G, sub, eq⟩ := exists_outEq deg
  have gfree : QFree G V q := fun a ℓ h1 hq w => hf a ℓ h1 hq (walk_sub sub w)
  -- a vertex of indegree at most s+1
  have total : ∑ x ∈ V, (V.filter (fun y => G y x = true)).card = (s + 1) * V.card := by
    rw [sum_indeg_eq_sum_outdeg, Finset.sum_congr rfl (fun y hy => eq y hy)]
    simp [mul_comm]
  obtain ⟨x, hx, small⟩ : ∃ x ∈ V, (V.filter (fun y => G y x = true)).card ≤ s + 1 := by
    by_contra bad
    push Not at bad
    have big : (s + 2) * V.card ≤ ∑ x ∈ V, (V.filter (fun y => G y x = true)).card := by
      have := Finset.card_nsmul_le_sum V (fun x => (V.filter (fun y => G y x = true)).card) (s + 2)
        (fun x hx => bad x hx)
      simpa [mul_comm] using this
    rw [total] at big
    have := Nat.le_of_mul_le_mul_right big hpos
    omega
  -- delete it
  have cardU : (V \ {x}).card + 1 = V.card := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hx)
    simpa using this
  have degV : ∀ y ∈ V, s + 1 ≤ (outN G V y).card := fun y hy => (eq y hy).ge
  have degU : ∀ y ∈ V \ {x}, s ≤ (outN G (V \ {x}) y).card := by
    intro y hy
    have yV := (Finset.mem_sdiff.mp hy).1
    have sub' : outN G V y ⊆ insert x (outN G (V \ {x}) y) := by
      intro z hz
      obtain ⟨zV, arc⟩ := mem_outN.mp hz
      by_cases zx : z = x
      · exact Finset.mem_insert.mpr (Or.inl zx)
      · exact Finset.mem_insert_of_mem (mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨zV, by simpa using zx⟩, arc⟩)
    have le := (Finset.card_le_card sub').trans (Finset.card_insert_le _ _)
    have := degV y yV
    omega
  have tight := T G (V \ {x}) (gfree.mono_set Finset.sdiff_subset) (by omega) degU
  -- every tight row of the smaller graph is a parent of x
  have into : (V \ {x}).filter (fun y => (outN G (V \ {x}) y).card = s) ⊆
      V.filter (fun y => G y x = true) := by
    intro y hy
    obtain ⟨yU, ys⟩ := Finset.mem_filter.mp hy
    have yV := (Finset.mem_sdiff.mp yU).1
    obtain ⟨arc, _, _⟩ := short_is_tight_parent (s := s + 1) (v := x) degV yV (by omega)
    exact Finset.mem_filter.mpr ⟨yV, arc⟩
  have := Finset.card_le_card into
  omega

end LeanCH.BR.TightRow

open LeanCH.BR.TightRow in
#print axioms tightLaw_implies_CH
