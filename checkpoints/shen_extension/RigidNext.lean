import checkpoints.shen_extension.RigidHost

/-!
# The rigid host one radius further out

A rigid host (`RigidHost.Rigid`: order `q s`, `q = 2 i + 1`, every `i`-ball exactly `s i + 1`,
every `(i+1)`-ball exactly `s (i+1)`) has the same ball size at every vertex at radii `i` and
`i + 1`. This file shows that it cannot have the same ball size at every vertex at radius `i + 2`
when `i` is even, and says what the layer at distance `i + 2` is.

* `sum_next_le`: the `(i+2)`-balls have at most `s (i+2)` labels on average.
* `exists_big_next`: for `i + 2 = 2 k` some vertex has an `(i+2)`-ball of at least `s (i+2) + 1`
  labels (Seymour's second neighbourhood theorem on the reach relation).
* `next_not_constant`: so the size of the `(i+2)`-ball is not the same at every vertex.
  `exists_small_next`: some vertex has at most `s (i+2) - 1`.
* `mem_layer_next`: `w` is at distance `i + 2` from `v` exactly when `w` is within `i + 2` of `v`
  and `v` is at distance exactly `i` from `w`.
* `card_layer_next`: `|layer (i+2) v| + |stuck v| + |reverseBall v (i-1)| = s i + 1`, where the
  stuck labels reach `v` in exactly `i` steps but are not within `i + 2` of `v`.
* `seymour_vertex_deficit`: some vertex has `|reverseBall v (i-1)| + |stuck v| ≤ s (i-1)`.
* `fifth_top_next_not_constant`: the instance at the even-degree top order of the fifth strip.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.RigidNext
open Finset BRq2 BRq3 FifthStripAll RigidHost
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer card_ball_succ)

variable {D : CH.Digraph} {V : Finset ℕ} {q s i : ℕ}

/-- The `(i+2)`-balls of a rigid host have at most `s (i+2)` labels on average. -/
theorem sum_next_le (R : Rigid D V q s i) (hi : 1 ≤ i) :
    ∑ v ∈ V, (ball D V v (i+2)).card ≤ V.card * (s*(i+2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have two : ∀ v ∈ V, (reverseBall D V v j).card + (ball D V v (j+1+2)).card ≤ V.card + 1 :=
    fun v _ => reverseBall_add_ball_le (v := v) (i := j+1+2) (j := j) R.free
      (by rw [R.odd]; omega)
  have s1 := Finset.sum_le_sum two
  rw [Finset.sum_add_distrib, sum_reverseBall_eq_sum_ball] at s1
  have fl := Finset.sum_le_sum (fun v hv => R.floor j (by omega) v hv)
  simp only [Finset.sum_const, smul_eq_mul] at s1 fl
  have e : V.card + 1 = (s*j+1) + s*(j+1+2) := by rw [R.size, R.odd]; ring
  rw [e, mul_add] at s1
  omega

/-- Seymour on the reach relation: some `(i+2)`-ball has at least `s (i+2) + 1` labels. -/
theorem exists_big_next (R : Rigid D V q s i) {k : ℕ} (hk : i + 2 = 2*k) (hi : 2 ≤ i)
    (ne : V.Nonempty) : ∃ y ∈ V, s*(i+2) + 1 ≤ (ball D V y (i+2)).card := by
  by_contra h
  have h2 := reach_seymour (k := k) (f := s*k+1) (A := s*(i+2)) R.free (by rw [R.odd]; omega) ne
    (fun v hv => R.floor k (by omega) v hv)
    (fun v hv => by
      rw [← hk]
      by_contra big
      exact h ⟨v, hv, by omega⟩)
  have : s*(i+2) = 2*(s*k) := by rw [hk]; ring
  omega

/-- Some `(i+2)`-ball has at most `s (i+2) - 1` labels. -/
theorem exists_small_next (R : Rigid D V q s i) {k : ℕ} (hk : i + 2 = 2*k) (hi : 2 ≤ i)
    (ne : V.Nonempty) : ∃ z ∈ V, (ball D V z (i+2)).card + 1 ≤ s*(i+2) := by
  by_contra h
  obtain ⟨y, hy, big⟩ := exists_big_next R hk hi ne
  have lt : ∑ _v ∈ V, s*(i+2) < ∑ v ∈ V, (ball D V v (i+2)).card :=
    Finset.sum_lt_sum
      (fun v hv => by
        by_contra small
        exact h ⟨v, hv, by omega⟩)
      ⟨y, hy, by omega⟩
  have sm := sum_next_le R (by omega)
  simp only [Finset.sum_const, smul_eq_mul] at lt
  omega

/-- **No stationarity at radius `i + 2`.** In a rigid host with `i` even the `(i+2)`-ball does
not have the same size at every vertex. -/
theorem next_not_constant (R : Rigid D V q s i) {k : ℕ} (hk : i + 2 = 2*k) (hi : 2 ≤ i)
    (ne : V.Nonempty) : ¬ ∃ c, ∀ v ∈ V, (ball D V v (i+2)).card = c := by
  rintro ⟨c, hc⟩
  obtain ⟨y, hy, big⟩ := exists_big_next R hk hi ne
  obtain ⟨z, hz, small⟩ := exists_small_next R hk hi ne
  have := hc y hy
  have := hc z hz
  omega

/-- The layer at distance `i + 2`: within `i + 2` going out, at distance exactly `i` coming
back. -/
theorem mem_layer_next (R : Rigid D V q s i) (hi : 1 ≤ i) {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V) :
    w ∈ layer D V (i+2) v ↔
      w ∈ ball D V v (i+2) ∧ v ∈ ball D V w i ∧ v ∉ ball D V w (i-1) := by
  have e : i + 2 - 1 = i + 1 := by omega
  rw [mem_layer, e]
  constructor
  · rintro ⟨hb, hn⟩
    have ne : v ≠ w := by
      rintro rfl
      exact hn (self_mem_ball hv)
    refine ⟨hb, ?_, ?_⟩
    · by_contra far
      exact hn ((dich' R hv hw ne).mpr far)
    · intro near
      have mem : w ∈ reverseBall D V v (i-1) := by
        simp only [reverseBall, mem_filter]; exact ⟨hw, near⟩
      have sub := reverseBall_subset_complement (v := v) (i := i+2) (j := i-1) R.free
        (by rw [R.odd]; omega) mem
      rcases mem_union.mp sub with h | h
      · exact (mem_sdiff.mp h).2 hb
      · exact ne (mem_singleton.mp h).symm
  · rintro ⟨hb, hvi, hvn⟩
    have ne : v ≠ w := by
      rintro rfl
      exact hvn (self_mem_ball hv)
    exact ⟨hb, fun close => (dich' R hv hw ne).mp close hvi⟩

/-- Labels that reach `v` in exactly `i` steps but are not within `i + 2` of `v`. -/
noncomputable def stuck (D : CH.Digraph) (V : Finset ℕ) (i v : ℕ) : Finset ℕ :=
  (reverseBall D V v i \ reverseBall D V v (i-1)).filter (fun w => w ∉ ball D V v (i+2))

/-- **The layer at distance `i + 2`, counted.** -/
theorem card_layer_next (R : Rigid D V q s i) (hi : 1 ≤ i) {v : ℕ} (hv : v ∈ V) :
    (layer D V (i+2) v).card + (stuck D V i v).card + (reverseBall D V v (i-1)).card
      = s*i + 1 := by
  classical
  have mono : reverseBall D V v (i-1) ⊆ reverseBall D V v i := by
    intro w hw
    simp only [reverseBall, mem_filter] at hw ⊢
    exact ⟨hw.1, ball_mono_radius (by omega) hw.2⟩
  have lay : layer D V (i+2) v =
      (reverseBall D V v i \ reverseBall D V v (i-1)).filter (fun w => w ∈ ball D V v (i+2)) := by
    ext w
    by_cases hw : w ∈ V
    · rw [mem_layer_next R hi hv hw]
      simp only [reverseBall, mem_filter, mem_sdiff, hw, true_and]
      tauto
    · constructor
      · intro h
        exact (hw (ball_subset (mem_layer.mp h).1)).elim
      · intro h
        exact (hw (ball_subset (mem_filter.mp h).2)).elim
  have split := Finset.card_filter_add_card_filter_not
    (s := reverseBall D V v i \ reverseBall D V v (i-1)) (fun w => w ∈ ball D V v (i+2))
  have c := Finset.card_sdiff_of_subset mono
  have r := rev_inner R v hv
  have le := card_le_card mono
  rw [lay]
  unfold stuck
  omega

/-- **The Seymour vertex is short on the way in.** Some vertex has
`|reverseBall v (i-1)| + |stuck v| ≤ s (i-1)`: its in-ball of radius `i - 1` is below the
flat line by at least one more than its number of stuck labels. -/
theorem seymour_vertex_deficit (R : Rigid D V q s i) {k : ℕ} (hk : i + 2 = 2*k) (hi : 2 ≤ i)
    (ne : V.Nonempty) :
    ∃ y ∈ V, (reverseBall D V y (i-1)).card + (stuck D V i y).card ≤ s*(i-1) := by
  obtain ⟨y, hy, big⟩ := exists_big_next R hk hi ne
  refine ⟨y, hy, ?_⟩
  have e : (ball D V y (i+2)).card = (layer D V (i+2) y).card + (ball D V y (i+1)).card :=
    card_ball_succ (D := D) (V := V) (u := y) (i+1)
  rw [R.outer y hy] at e
  have c := card_layer_next R (by omega) hy
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at c ⊢
  have e1 : s*(j+1+2) = s*(j+1+1) + s := by ring
  have e2 : s*(j+1) = s*j + s := by ring
  omega

/-- **Instance.** At the even-degree top order of the fifth strip (`a` odd, `s = a + 7`,
`q = 2 a + 7`, order `q s`) the ball of radius `a + 5` is not the same size at every vertex. -/
theorem fifth_top_next_not_constant {a m : ℕ} (hm : a = 2*m+1) (m1 : 1 ≤ m) (L : LedgerFloors a)
    (tc : Top a ((2*a+7)*(a+7))) {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (size : V.card = (2*a+7)*(a+7)) :
    ¬ ∃ c, ∀ v ∈ V, (ball D V v (a+5)).card = c := by
  have R := rigid_of_top (by omega) L tc free degree size
  have ne : V.Nonempty := by
    rw [← card_pos, size]; positivity
  exact next_not_constant R (k := m+3) (by omega) (by omega) ne

#print axioms sum_next_le
#print axioms exists_big_next
#print axioms exists_small_next
#print axioms next_not_constant
#print axioms mem_layer_next
#print axioms card_layer_next
#print axioms seymour_vertex_deficit
#print axioms fifth_top_next_not_constant
end LeanCH.BR.RigidNext
