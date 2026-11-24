import checkpoints.shen_extension.SeparatedReturnBank
import checkpoints.shen_extension.TransitionClosureStatic
import checkpoints.shen_extension.JointShortcut

/-!
# Two edit tests in their exact form

* `hub_iff`: a new label `z` with in-set `I` and out-set `H` is safe **exactly** when the old
  graph is safe and no old walk of at most `q-2` arcs leads from `H` to `I`. The sufficiency is
  `SeparatedReturnBank.hub_safe`. Padding (`I = ∅`), clones, restored rows and a reinserted row
  are instances.
* `addArcs_eq_install`, `admissible_iff_trail`: the arc sets of `TransitionClosureStatic` are the
  arc labels of `JointShortcut`. A family is admissible exactly when it is new, within the row
  capacities, and has no closed trail of cost at most `q`. So the least shortfall on a fixed label
  set (`static_minimum`) ranges over trail-free families (`static_trail_minimum`).
-/

namespace LeanCH.BR.InsertionTests
open Finset BRq2 BRq3 JointShortcut
open LeanCH.BR.Closure LeanCH.BR.Closure.SeparatedReturnBank

/-- **One new label, exact test.** -/
theorem hub_iff {D : CH.Digraph} {W I H : Finset ℕ} {q z : ℕ} (fresh : z ∉ W) (hw : H ⊆ W) :
    QFree (hub D z I H) (insert z W) q ↔
      QFree D W q ∧ ∀ h ∈ H, ∀ i ∈ I, ∀ k, k+2 ≤ q → ¬ Walk D W h i k := by
  have lift : ∀ {a b n}, Walk D W a b n → a ∈ W → Walk (hub D z I H) (insert z W) a b n := by
    intro a b n w
    induction w with
    | refl => exact fun _ => .refl _
    | @step a c b n cw ac rest ih =>
      intro aw
      have az : a ≠ z := by
        rintro rfl
        exact fresh aw
      have cz : c ≠ z := by
        rintro rfl
        exact fresh cw
      exact .step (mem_insert_of_mem cw) (by simp [hub, az, cz, ac]) (ih cw)
  constructor
  · intro safe
    refine ⟨fun a n pos le w => ?_, fun h hh i hi k cap w => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
      obtain ⟨_, _, aw, _⟩ := w.unsnoc
      exact safe a (m+1) pos le (lift w aw)
    · have hW := hw hh
      have iW : i ∈ W := by
        rcases w.end_mem_or with e | iw
        · rw [e]
          exact hW
        · exact iw
      have iz : i ≠ z := by
        rintro rfl
        exact fresh iW
      have first : hub D z I H z h = true := by simp [hub, hh]
      have last : hub D z I H i z = true := by simp [hub, iz, hi]
      exact safe z (k+1+1) (by omega) (by omega)
        (.step (mem_insert_of_mem hW) first ((lift w hW).snoc (mem_insert_self z W) last))
  · rintro ⟨free, far⟩
    exact hub_safe free fresh hw far

/-- The arc sets of the static closure are the arc labels of the joint shortcut test. -/
theorem addArcs_eq_install (G : CH.Digraph) (F : Finset (ℕ × ℕ)) : addArcs G F = install G F := rfl

/-- **Admissible families are the trail-free ones.** -/
theorem admissible_iff_trail {q s : ℕ} (O : Origin q s) {U : Finset ℕ} (hU : U ⊆ O.V)
    {F : Finset (ℕ × ℕ)} :
    Admissible O U F ↔ F ⊆ U ×ˢ U ∧ (∀ p ∈ F, O.G p.1 p.2 ≠ true) ∧
      (∀ u ∈ U, (row F u).card ≤ cap O U u) ∧
      ∀ i ∈ F, ∀ c, 0 < c → c ≤ q → ¬ Trail O.G U F i i c := by
  have base : QFree O.G U q := O.free.mono_set hU
  constructor
  · intro a
    have inU : ∀ j ∈ F, j.2 ∈ U := fun j hj => (mem_product.mp (a.sub hj)).2
    exact ⟨a.sub, a.new, a.rowCap, ((install_iff inU).mp a.free).2⟩
  · rintro ⟨sub, new, rowCap, clear⟩
    have inU : ∀ j ∈ F, j.2 ∈ U := fun j hj => (mem_product.mp (sub hj)).2
    exact ⟨sub, new, rowCap, (install_iff inU).mpr ⟨base, clear⟩⟩

/-- **Least shortfall over trail-free families.** On a fixed nonempty label set, every reachable
state has shortfall at least `capTotal - |F|` for a new, capacity-respecting family `F` without a
closed trail of cost at most `q`, and every such family is attained. -/
theorem static_trail_minimum {q s : ℕ} (O : Origin q s) {U : Finset ℕ} (hU : U ⊆ O.V)
    (hne : U.Nonempty) :
    (∀ t, Reach (RStep q s) O.init t → t.U = U →
        ∃ F : Finset (ℕ × ℕ), F ⊆ U ×ˢ U ∧ (∀ p ∈ F, O.G p.1 p.2 ≠ true) ∧
          (∀ u ∈ U, (row F u).card ≤ cap O U u) ∧
          (∀ i ∈ F, ∀ c, 0 < c → c ≤ q → ¬ Trail O.G U F i i c) ∧
          capTotal O U - F.card ≤ shortfall s t) ∧
    (∀ F : Finset (ℕ × ℕ), F ⊆ U ×ˢ U → (∀ p ∈ F, O.G p.1 p.2 ≠ true) →
        (∀ u ∈ U, (row F u).card ≤ cap O U u) →
        (∀ i ∈ F, ∀ c, 0 < c → c ≤ q → ¬ Trail O.G U F i i c) →
        ∃ t, Reach (RStep q s) O.init t ∧ t.U = U ∧ shortfall s t = capTotal O U - F.card) := by
  obtain ⟨lower, attained⟩ := static_minimum O hU hne
  refine ⟨fun t r ht => ?_, fun F sub new rowCap clear => ?_⟩
  · obtain ⟨F, adm, le⟩ := lower t r ht
    obtain ⟨sub, new, rowCap, clear⟩ := (admissible_iff_trail O hU).mp adm
    exact ⟨F, sub, new, rowCap, clear, le⟩
  · exact attained F ((admissible_iff_trail O hU).mpr ⟨sub, new, rowCap, clear⟩)

#print axioms hub_iff
#print axioms addArcs_eq_install
#print axioms admissible_iff_trail
#print axioms static_trail_minimum
end LeanCH.BR.InsertionTests
