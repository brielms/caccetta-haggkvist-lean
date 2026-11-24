import LeanCH.BR.BRFiniteWalk

/-!
# Shared exits and short returns

Extension trace clause 460257 in the local (7,56) run motivates the last
theorem. The first two theorems hold for arbitrary finite vertex sets and cutoff.
-/

namespace LeanCH.BR.SATBoundaryPilot

open Finset BRq2 BRq3

/-- From each starting row one can reach a row pointing to every target in T.
The path stays inside X and takes fewer than |X| steps. -/
theorem shared_exit_sink {D : CH.Digraph} {V X T : Finset ℕ} {q x : ℕ}
    (free : QFree D V q) (rows : X ⊆ V) (size : X.card ≤ q) (start : x ∈ X)
    (budget : ∀ a ∈ X, T.card ≤ (outN D (X ∪ T) a).card) :
    ∃ z ∈ X, ∃ k < X.card, Walk D X x z k ∧ ∀ t ∈ T, D z t = true := by
  obtain ⟨z, hz, sink, k, hk, path⟩ :=
    reach_sink_of_card (free.mono_set rows) size start
  have targets : outN D (X ∪ T) z ⊆ T := by
    intro b hb
    obtain ⟨inMenu, arc⟩ := mem_outN.mp hb
    exact (mem_union.mp inMenu).resolve_left (fun inX => sink b inX arc)
  have full := eq_of_subset_of_card_le targets (budget z hz)
  exact ⟨z, hz, k, hk, path, fun t ht => (mem_outN.mp (full.symm ▸ ht)).2⟩

/-- A return from a target to the starting row within r steps would close a
positive walk of length at most |X| + r. -/
theorem shared_exit_excludes_return {D : CH.Digraph} {V X T : Finset ℕ} {q x t r : ℕ}
    (free : QFree D V q) (rows : X ⊆ V) (targets : T ⊆ V)
    (start : x ∈ X) (target : t ∈ T) (room : r + X.card ≤ q)
    (budget : ∀ a ∈ X, T.card ≤ (outN D (X ∪ T) a).card) :
    x ∉ ball D V t r := by
  obtain ⟨z, _, k, hk, path, full⟩ := shared_exit_sink free rows (by omega) start budget
  intro hit
  obtain ⟨_, j, hj, back⟩ := mem_ball.mp hit
  exact free x (k + 1 + j) (by omega) (by omega)
    (((path.mono rows).snoc (targets target) (full t target)).append back)

/-- Graph interpretation of the three negative literals of clause 460257.
The first six counter positions in each of rows 5 and 6 are the labels 0 to 6
with the row itself removed. The fixed arcs from 0 rule out a return to 0.
The resulting graph implication already holds at cutoff four. -/
theorem clause_460257 {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (free : QFree D V q) (hq : 4 ≤ q) (labels : range 7 ⊆ V)
    (pinned : ∀ a ∈ ({5, 6} : Finset ℕ), D 0 a = true)
    (counts : ∀ a ∈ ({5, 6} : Finset ℕ), 4 ≤ (outN D ((range 7).erase a) a).card) :
    5 ∉ ball D V 1 2 := by
  let X : Finset ℕ := {5, 6}
  let T : Finset ℕ := {1, 2, 3, 4}
  have xs : X ⊆ V := (show X ⊆ range 7 by decide).trans labels
  have ts : T ⊆ V := (show T ⊆ range 7 by decide).trans labels
  have budget (a) (ha : a ∈ X) : T.card ≤ (outN D (X ∪ T) a).card := by
    have noZero : D a 0 ≠ true := by
      intro back
      exact free 0 2 (by decide) (by omega)
        (.step (xs ha) (pinned a ha) (.step (labels (by decide : 0 ∈ range 7)) back (.refl 0)))
    have sub : outN D ((range 7).erase a) a ⊆ outN D (X ∪ T) a := by
      intro b hb
      obtain ⟨inPrefix, edge⟩ := mem_outN.mp hb
      have nz : b ≠ 0 := fun eq => noZero (eq ▸ edge)
      have inMenu : b ∈ X ∪ T := by
        rw [show X ∪ T = (range 7).erase 0 by decide]
        exact mem_erase.mpr ⟨nz, mem_of_mem_erase inPrefix⟩
      exact mem_outN.mpr ⟨inMenu, edge⟩
    rw [show T.card = 4 by decide]
    exact (counts a ha).trans (card_le_card sub)
  apply shared_exit_excludes_return free xs ts (by decide : 5 ∈ X) (by decide : 1 ∈ T) _ budget
  have : X.card = 2 := by decide
  omega

#print axioms shared_exit_sink
#print axioms shared_exit_excludes_return
#print axioms clause_460257

end LeanCH.BR.SATBoundaryPilot
