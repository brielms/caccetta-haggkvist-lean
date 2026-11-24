import checkpoints.shen_extension.DotTwoPassShellTransport_20261117

/-!
# Exact root degree and the layer facts of a ball

* `exact_root`: trimming the root row of a `q`-free graph of minimum out-degree `r`
  to exactly `r` heads keeps every hypothesis and only shrinks the root's balls.
  So a ball floor may be proved at a root of out-degree exactly `r`.
* The layers `layer D V i u = ball i \ ball (i - 1)`, `i ≥ 1`, of a ball around `u`:
  layer one is the out-neighbourhood, a row of layer `i` (with `i + 1 ≤ q`) heads only
  layers `1 … i + 1`, a row of layer `i + 1` has a parent in layer `i`, distinct layers
  are disjoint, `|ball k| = 1 + Σ_{j < k} |layer (j + 1)|`, and an empty layer is
  followed by an empty layer.
-/

namespace LeanCH.BR.ShapeClimbRoot
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer shell)

/-! ### Target 1: an exact root -/

/-- The root row of `D` replaced by the selection `S`. -/
def trim (D : CH.Digraph) (u : ℕ) (S : Finset ℕ) : CH.Digraph :=
  fun v w => if v = u then decide (w ∈ S) else D v w

theorem outN_trim_root {D : CH.Digraph} {V S : Finset ℕ} {u : ℕ} (hS : S ⊆ V) :
    outN (trim D u S) V u = S := by
  ext w
  simp only [mem_outN, trim, ite_true, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩

theorem outN_trim_other {D : CH.Digraph} {V S : Finset ℕ} {u v : ℕ} (e : v ≠ u) :
    outN (trim D u S) V v = outN D V v := by
  ext w
  simp only [mem_outN, trim, e, ite_false]

/-- **Exact root.** A root of out-degree at least `r` can be trimmed to out-degree exactly
`r`: the trimmed graph is arcwise below `D`, agrees with `D` off the root row, keeps
minimum out-degree `r` and `q`-freeness, and its balls at the root are inside those of `D`. -/
theorem exact_root {D : CH.Digraph} {V : Finset ℕ} {q r u : ℕ}
    (big : r ≤ (outN D V u).card) (free : QFree D V q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    ∃ D' : CH.Digraph, (∀ v w, D' v w = true → D v w = true) ∧
      (∀ v w, v ≠ u → D' v w = D v w) ∧ (outN D' V u).card = r ∧
      (∀ v ∈ V, r ≤ (outN D' V v).card) ∧ QFree D' V q ∧
      ∀ k, ball D' V u k ⊆ ball D V u k := by
  obtain ⟨S, hS, cS⟩ := exists_subset_card_eq big
  have SV : S ⊆ V := hS.trans outN_subset
  have below : ∀ v w, trim D u S v w = true → D v w = true := by
    intro v w h
    by_cases e : v = u
    · subst e
      simp only [trim, ite_true, decide_eq_true_eq] at h
      exact (mem_outN.mp (hS h)).2
    · simpa only [trim, e, ite_false] using h
  refine ⟨trim D u S, below, fun v w e => by simp only [trim, e, ite_false], ?_, ?_,
    qfree_sub below free, fun k => ball_sub below⟩
  · rw [outN_trim_root SV, cS]
  · intro v hv
    by_cases e : v = u
    · subst e; rw [outN_trim_root SV, cS]
    · rw [outN_trim_other e]; exact deg v hv

/-! ### Target 2: layer facts -/

section layers
variable {D : CH.Digraph} {V : Finset ℕ} {q u : ℕ}

theorem mem_layer {i v : ℕ} : v ∈ layer D V i u ↔ v ∈ ball D V u i ∧ v ∉ ball D V u (i - 1) := by
  simp only [layer, mem_sdiff]

theorem ball_zero_eq (hu : u ∈ V) : ball D V u 0 = {u} := by
  ext v
  simp only [mem_singleton]
  constructor
  · intro hv
    obtain ⟨_, j, hj, w⟩ := mem_ball.mp hv
    obtain rfl : j = 0 := by omega
    cases w; rfl
  · rintro rfl; exact self_mem_ball hu

theorem layer_one (free : QFree D V q) (hq : 1 ≤ q) (hu : u ∈ V) :
    layer D V 1 u = outN D V u := by
  ext v
  rw [mem_layer, show 1 - 1 = 0 from rfl, ball_zero_eq hu, mem_ball_one hu, mem_singleton]
  constructor
  · rintro ⟨h | h, n⟩
    · exact absurd h n
    · exact h
  · intro h
    refine ⟨Or.inr h, fun e => ?_⟩
    subst e
    exact loopfree free hq hu (mem_outN.mp h).2

/-- Every label of a ball other than the root lies in some layer `1 … k`. -/
theorem layer_of_ball (hu : u ∈ V) {k y : ℕ} (hy : y ∈ ball D V u k) (ne : y ≠ u) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ y ∈ layer D V j u := by
  induction k with
  | zero => rw [ball_zero_eq hu, mem_singleton] at hy; exact absurd hy ne
  | succ k ih =>
    by_cases old : y ∈ ball D V u k
    · obtain ⟨j, h1, h2, hj⟩ := ih old
      exact ⟨j, h1, by omega, hj⟩
    · exact ⟨k + 1, by omega, le_rfl, mem_layer.mpr ⟨hy, by simpa using old⟩⟩

/-- **Heads.** A row of layer `i`, `1 ≤ i`, `i + 1 ≤ q`, heads only layers `1 … i + 1`:
a head at the root closes a walk of at most `i + 1` arcs. -/
theorem head_mem (free : QFree D V q) (hu : u ∈ V) {i x y : ℕ} (_hi : 1 ≤ i) (time : i + 1 ≤ q)
    (hx : x ∈ layer D V i u) (hy : y ∈ outN D V x) :
    ∃ j, 1 ≤ j ∧ j ≤ i + 1 ∧ y ∈ layer D V j u := by
  have xb := (mem_layer.mp hx).1
  have yb := ball_step xb (mem_outN.mp hy).1 (mem_outN.mp hy).2
  have ne : y ≠ u := by
    rintro rfl
    exact no_back_arc free hu xb time (mem_outN.mp hy).2
  exact layer_of_ball hu yb ne

/-- **Parents.** A row of layer `i + 1`, `1 ≤ i`, has a parent in layer `i`. -/
theorem parent_mem (hu : u ∈ V) {i y : ℕ} (_hi : 1 ≤ i) (hy : y ∈ layer D V (i + 1) u) :
    ∃ p ∈ layer D V i u, D p y = true := by
  obtain ⟨yb, yn⟩ := mem_layer.mp hy
  rw [Nat.add_sub_cancel] at yn
  obtain ⟨p, pb, arc⟩ := ball_succ_pred hu yb yn
  refine ⟨p, mem_layer.mpr ⟨pb, fun old => ?_⟩, arc⟩
  have := ball_step (k := i - 1) old (mem_ball.mp yb).1 arc
  rw [show i - 1 + 1 = i by omega] at this
  exact yn this

theorem layer_disjoint {i j : ℕ} (h : i < j) : Disjoint (layer D V i u) (layer D V j u) := by
  rw [disjoint_left]
  intro v vi vj
  exact (mem_layer.mp vj).2 (ball_mono_radius (by omega) (mem_layer.mp vi).1)

theorem layer_disjoint' {i j : ℕ} (h : i ≠ j) : Disjoint (layer D V i u) (layer D V j u) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact layer_disjoint h
  · exact (layer_disjoint h).symm

theorem card_ball_succ (k : ℕ) :
    (ball D V u (k + 1)).card = (layer D V (k + 1) u).card + (ball D V u k).card := by
  have := card_sdiff_add_card_eq_card (ball_mono_radius (D := D) (W := V) (u := u) (Nat.le_succ k))
  simpa only [layer, Nat.add_sub_cancel] using this.symm

theorem card_ball_sum (hu : u ∈ V) (k : ℕ) :
    (ball D V u k).card = 1 + ∑ j ∈ range k, (layer D V (j + 1) u).card := by
  induction k with
  | zero => rw [ball_zero_eq hu]; simp
  | succ k ih => rw [card_ball_succ, ih, sum_range_succ]; omega

/-- An empty layer is followed by an empty layer. -/
theorem layer_empty_next (hu : u ∈ V) {i : ℕ} (e : layer D V (i + 1) u = ∅) :
    layer D V (i + 2) u = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro y hy
  obtain ⟨yb, yn⟩ := mem_layer.mp hy
  rw [show i + 2 - 1 = i + 1 by omega] at yn
  obtain ⟨p, pb, arc⟩ := ball_succ_pred hu yb yn
  have pi : p ∈ ball D V u i := by
    by_contra n
    have : p ∈ layer D V (i + 1) u := mem_layer.mpr ⟨pb, by simpa using n⟩
    rw [e] at this
    exact absurd this (notMem_empty p)
  exact yn (ball_step pi (mem_ball.mp yb).1 arc)

theorem layer_one_card (free : QFree D V q) (hq : 1 ≤ q) (hu : u ∈ V) {r : ℕ}
    (exact : (outN D V u).card = r) : (layer D V 1 u).card = r := by
  rw [layer_one free hq hu, exact]

end layers

#print axioms exact_root
#print axioms head_mem
#print axioms parent_mem
#print axioms card_ball_sum
#print axioms layer_empty_next
end LeanCH.BR.ShapeClimbRoot
