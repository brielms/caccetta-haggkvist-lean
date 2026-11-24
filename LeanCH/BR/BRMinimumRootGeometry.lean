import LeanCH.BR.BRSplitTransferGeometry

/-! Local short-return geometry for cut tails pointing back to a receiver. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem walk_survives_returning_tail_cuts {q : ℕ} {D : CH.Digraph}
    {V K : Finset ℕ} {y a b l : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hKV : K ⊆ V) (hy : y ∈ V)
    (hC : ∀ x z, (x, z) ∈ C → D x y = true) (p : Walk D K a b l) :
    ∀ k, Walk D V y a k → k + l ≤ q → Walk (cutGraph D C) K a b l := by
  induction p with
  | refl a => intro k _ _; exact .refl a
  | @step a z b m hz haz rest ih =>
    intro k initial hlen
    have hnot : (a, z) ∉ C := by
      intro hcut
      exact hf y (k + 1) (by omega) (by omega) (initial.snoc hy (hC a z hcut))
    exact .step hz (decide_eq_true ⟨haz, hnot⟩)
      (ih (k + 1) (initial.snoc (hKV hz) haz) (by omega))

theorem ball_unchanged_by_returning_tail_cuts {q r : ℕ} {D : CH.Digraph}
    {V K : Finset ℕ} {y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hKV : K ⊆ V) (hy : y ∈ V) (hr : r ≤ q)
    (hC : ∀ x z, (x, z) ∈ C → D x y = true) :
    ball (cutGraph D C) K y r = ball D K y r := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxK, k, hk, p⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨hxK, k, hk, walk_sub (cutGraph_sub D C) p⟩
  · intro hx
    obtain ⟨hxK, k, hk, p⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨hxK, k, hk,
      walk_survives_returning_tail_cuts hf hKV hy hC p 0 (.refl _) (by omega)⟩

/-- The same exclusion after any old prefix; direct heads of y inherit
unchanged returns of length at most q-1. -/
theorem ball_unchanged_with_prefix {q d r : ℕ} {D : CH.Digraph}
    {V K : Finset ℕ} {y t : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hKV : K ⊆ V) (hy : y ∈ V)
    (initial : Walk D V y t d) (hlen : d + r ≤ q)
    (hC : ∀ x z, (x, z) ∈ C → D x y = true) :
    ball (cutGraph D C) K t r = ball D K t r := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxK, k, hk, p⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨hxK, k, hk, walk_sub (cutGraph_sub D C) p⟩
  · intro hx
    obtain ⟨hxK, k, hk, p⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨hxK, k, hk,
      walk_survives_returning_tail_cuts hf hKV hy hC p d initial (by omega)⟩

theorem returning_tail_distance_lower {q d j : ℕ} {D : CH.Digraph}
    {V : Finset ℕ} {y t r : ℕ} (hf : QFree D V q) (hy : y ∈ V)
    (initial : Walk D V y t d) (ending : Walk D V t r j) (hry : D r y = true) :
    q ≤ d + j := by
  by_contra hn
  exact hf y (d + j + 1) (by omega) (by omega) ((initial.append ending).snoc hy hry)

theorem splitSafe_receiver_iff_original {q : ℕ} {D : CH.Digraph}
    {V : Finset ℕ} {v y x : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hy : y ∈ outN D V v)
    (hC : ∀ r s, (r, s) ∈ C → D r y = true) :
    y ∈ splitSafe q D V v C x ↔ x ∉ ball D (V.erase v) y (q - 1) := by
  simp only [splitSafe, mem_filter]
  rw [ball_unchanged_by_returning_tail_cuts hf (erase_subset v V) (outN_subset hy)
    (by omega : q - 1 ≤ q) hC]
  exact and_iff_right hy

/-- An interior tail on a dangerous return is not a receiver and cannot head
the starting receiver. Length assumptions, rather than a fixed cutoff, suffice. -/
theorem interior_return_tail_exclusions {q i j : ℕ} {D : CH.Digraph}
    {V : Finset ℕ} {v t r s x : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (ht : t ∈ outN D V v) (hx : x ∈ inN D V v)
    (initial : Walk D V t r i) (hrs : D r s = true) (hs : s ∈ V)
    (ending : Walk D V s x j) (hi : 1 ≤ i) (hlen : i + 1 + j ≤ q - 1) :
    r ∉ outN D V v ∧ ¬ D r t = true := by
  constructor
  · intro hrT
    have hsep := root_head_parent_separation hf hv hrT hx (.step hs hrs ending)
    omega
  · intro hrt
    exact hf t (i + 1) (by omega) (by omega) (initial.snoc (outN_subset ht) hrt)

end LeanCH.BR.WeightedSD
