import checkpoints.shen_extension.FifthStripAllParity

/-!
# A tight pair of ball floors closes the order

The two-ball count closes an order `n` when the floors `a` at radius `k` and `b` at radius
`q - k` satisfy `a + b ≥ n + 2`. Here `a + b ≥ n + 1` is enough, provided `2a + c ≥ n + 3` for a
floor `c` at radius `q - 2k`.

When `a + b = n + 1` every reverse ball of radius `k` has exactly `a` labels
(`two_balls_boundary_cards`). Seymour's second-neighbourhood theorem on the reverse reach relation
then gives a vertex whose reverse ball of radius `2k` has at least `2a - 1` labels, while the
out-ball of radius `q - 2k` at that vertex caps it at `n + 1 - c`.

`tight_pair_host` is the form with the ideal floors `s k + 1` and `s (q - 2k) + 1` in a host of
order at most `q s`: the floor at radius `q - k` may then be one below what the two-ball count
needs.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TightPair
open Finset BRq2 BRq3 FifthStripAll FifthStripAllParity

/-- **Tight pair.** Floors `a`, `b`, `c` at radii `k`, `q - k`, `q - 2k` with `a + b ≥ n + 1`
and `2a + c ≥ n + 3` are impossible in a `q`-free digraph on `n` labels. -/
theorem tight_pair_false {D : CH.Digraph} {V : Finset ℕ} {q k a b c : ℕ}
    (free : QFree D V q) (hk : 2*k ≤ q) (ne : V.Nonempty)
    (inner : ∀ v ∈ V, a ≤ (ball D V v k).card)
    (outer : ∀ v ∈ V, b ≤ (ball D V v (q-k)).card)
    (small : ∀ v ∈ V, c ≤ (ball D V v (q-2*k)).card)
    (pair : V.card + 1 ≤ a + b) (gain : V.card + 3 ≤ 2*a + c) : False := by
  obtain ⟨v0, hv0⟩ := ne
  have a_le : a ≤ V.card := (inner v0 hv0).trans (card_le_card ball_subset)
  have c_le : c ≤ V.card := (small v0 hv0).trans (card_le_card ball_subset)
  have ex := two_balls_boundary_cards (i := q-k) (j := k) (a := V.card + 1 - a) (b := a) free
    (by omega) (fun v hv => by have := outer v hv; omega) inner (by omega)
  have h := reach_seymour (D := tr D) (V := V) (q := q) (k := k) (f := a) (A := V.card + 1 - c)
    (qfree_tr free) hk ⟨v0, hv0⟩
    (fun v hv => by
      rw [← reverseBall_eq_ball_tr hv]
      exact (ex v hv).2.2.ge)
    (fun v hv => by
      rw [← reverseBall_eq_ball_tr hv]
      have t := reverseBall_add_ball_le (v := v) (i := q-2*k) (j := 2*k) free (by omega)
      have := small v hv
      omega)
  omega

/-- **Host form.** In a `q`-free digraph on at most `q s` labels with the ideal floors
`s k + 1` at radius `k` and `s (q - 2k) + 1` at radius `q - 2k`, a floor `b` at radius `q - k`
with `n ≤ s k + b` is impossible. (The two-ball count needs `n + 1 ≤ s k + b`.) -/
theorem tight_pair_host {D : CH.Digraph} {V : Finset ℕ} {q s k b : ℕ}
    (free : QFree D V q) (hk : 2*k ≤ q) (ne : V.Nonempty) (size : V.card ≤ q*s)
    (inner : ∀ v ∈ V, s*k + 1 ≤ (ball D V v k).card)
    (outer : ∀ v ∈ V, b ≤ (ball D V v (q-k)).card)
    (small : ∀ v ∈ V, s*(q-2*k) + 1 ≤ (ball D V v (q-2*k)).card)
    (pair : V.card ≤ s*k + b) : False := by
  refine tight_pair_false free hk ne inner outer small (by omega) ?_
  obtain ⟨m, rfl⟩ : ∃ m, q = 2*k + m := ⟨q - 2*k, by omega⟩
  have e : (2*k + m)*s = 2*(s*k) + s*m := by ring
  rw [Nat.add_sub_cancel_left]
  omega

#print axioms tight_pair_false
#print axioms tight_pair_host
end LeanCH.BR.TightPair
