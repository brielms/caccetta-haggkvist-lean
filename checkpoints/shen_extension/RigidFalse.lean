import checkpoints.shen_extension.RigidHost

/-!
# No rigid host

A rigid host (`RigidHost.Rigid`: order `q s`, `q = 2 i + 1`, out-degree `≥ s`, every `i`-ball
exactly `s i + 1`, every `(i+1)`-ball exactly `s (i+1)`) does not exist, for either parity of `i`.

Reverse every arc. The reverse balls of radius `i` have exactly `s i + 1` labels at every vertex
(`rev_inner`), so Seymour's second-neighbourhood theorem on the reverse reach relation gives a
vertex whose reverse ball of radius `2 i = q - 1` has at least `2 s i + 1` labels. But the heads
of a vertex are at reverse distance at least `q` from it, so every reverse ball of radius `q - 1`
misses at least `s` labels and has at most `2 s i` (`rev_tail`).

`fifth_top_false` is the instance at the top order of the fifth strip, for every `a ≥ 2` with the
ledger floors and the top-order check, with no parity condition.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.RigidFalse
open Finset BRq2 BRq3 FifthStripAll FifthStripAllParity RigidHost

/-- **No rigid host.** -/
theorem rigid_false {D : CH.Digraph} {V : Finset ℕ} {q s i : ℕ} (R : Rigid D V q s i)
    (hi : 1 ≤ i) (ne : V.Nonempty) : False := by
  have h := reach_seymour (D := tr D) (V := V) (q := q) (k := i) (f := s*i+1) (A := s*(2*i))
    (qfree_tr R.free) (by rw [R.odd]; omega) ne
    (fun v hv => by
      rw [← reverseBall_eq_ball_tr hv]
      exact (rev_inner R v hv).ge)
    (fun v hv => by
      rw [← reverseBall_eq_ball_tr hv]
      have t := rev_tail R (k := 1) hi hv
      rwa [show q - 1 = 2*i by rw [R.odd]; omega] at t)
  have e : s*(2*i) = 2*(s*i) := by ring
  omega

/-- **Top order of the fifth strip, either parity.** No `q`-free digraph with all out-degrees at
least `s = a + 7` on `q s` vertices, `q = 2 a + 7`, when the ledger floors and the top-order check
hold. -/
theorem fifth_top_false {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (size : V.card = (2*a+7)*(a+7)) : False := by
  have ne : V.Nonempty := by
    rw [← card_pos, size]; positivity
  exact rigid_false (rigid_of_top ha L tc free degree size) (by omega) ne

#print axioms rigid_false
#print axioms fifth_top_false
end LeanCH.BR.RigidFalse
