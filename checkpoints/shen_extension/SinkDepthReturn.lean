import checkpoints.shen_extension.SinkTransit

/-!
# Sink depth bounds the targets of short returns

Let `X` be a set of rows inside a `q`-free graph on `V` (for instance a layer of a
punctured ball). Inside `X` the graph is acyclic as soon as `|X| ≤ q`, so every
row reaches an `X`-sink inside `X`. Say `x` is *`t`-deep in `X`* if every walk
inside `X` from `x` to an `X`-sink has length at least `t`; this is
`t ≤ len` for the shortest sink path `ShortestSinkPath D X x`.

* `return_deep`: if every `X`-sink reaches `w` within `m` steps, an arc `w → x`
  forces `x` to be `(q - m)`-deep.
* `return_deep_next`: the same when every `X`-sink heads all of a nonempty next
  set `Y` and `w` is reached from some `y ∈ Y` within `l` steps (`m = l + 1`).
* `deep_card`: at most `|X| - t` rows of `X` are `t`-deep.
* `deep_heads`: a `t`-deep row has at most `|X| - t` heads inside `X`.
* `return_targets`: combining the first and third: all targets of returns from
  `w` lie in a set of size at most `|X| - (q - m)`.

Everything is stated for arbitrary `D`, `V`, `X`, `q`, `m`, `t`.
-/

namespace LeanCH.BR.SinkDepthReturn
open Finset BRq2 BRq3 SinkReturnAncestors

/-- Every walk inside `X` from `x` to an `X`-sink has length at least `t`. -/
def Deep (D : CH.Digraph) (X : Finset ℕ) (t x : ℕ) : Prop :=
  ∀ s ∈ X, Sink D X s → ∀ k, Walk D X x s k → t ≤ k

theorem Deep.mono {D X t t' x} (h : Deep D X t x) (le : t' ≤ t) : Deep D X t' x :=
  fun s sm stop k walk => le.trans (h s sm stop k walk)

/-- The shortest sink path realises depth. -/
theorem deep_iff_len {D X t x} (p : ShortestSinkPath D X x) : Deep D X t x ↔ t ≤ p.len := by
  constructor
  · intro deep
    have walk := p.walk (Nat.zero_le _) le_rfl
    simp only [p.start, Nat.sub_zero] at walk
    exact deep _ (p.mem _ le_rfl) (fun z zm => p.sink z zm) _ walk
  · intro le s sm stop k walk
    exact le.trans (p.minimal s sm (fun z zm h => stop z zm h) k walk)

/-- **Return depth.** If every `X`-sink reaches `w` in at most `m` steps (in `V`), an
arc `w → x` with `x ∈ X` forces `x` to be `(q - m)`-deep in `X`. -/
theorem return_deep {D V X q x w m} (free : QFree D V q) (xv : X ⊆ V)
    (xm : x ∈ X) (reach : ∀ s ∈ X, Sink D X s → Walk D V s w m)
    (ret : D w x = true) : Deep D X (q - m) x := by
  intro s sm stop k walk
  by_contra! short
  have loop := ((walk.mono xv).append (reach s sm stop)).snoc (xv xm) ret
  exact free x (k + m + 1) (by omega) (by omega) loop

/-- **Return depth through the next set.** If every `X`-sink heads all of `Y`, and `w`
is reached within `l` steps from some `y ∈ Y`, then an arc `w → x` with `x ∈ X`
forces `x` to be `(q - (l + 1))`-deep in `X`. -/
theorem return_deep_next {D V X Y q x w l y} (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V)
    (xm : x ∈ X) (full : ∀ s ∈ X, Sink D X s → Y ⊆ outN D V s)
    (ym : y ∈ Y) (tail : Walk D V y w l) (ret : D w x = true) :
    Deep D X (q - (l + 1)) x :=
  return_deep free xv xm (fun s sm stop =>
    Walk.step (yv ym) (mem_outN.mp (full s sm stop ym)).2 tail) ret

/-- A `t`-deep row has at most `|X| - t` heads inside `X`. -/
theorem deep_heads {D X q t x} (free : QFree D X q) (size : X.card ≤ q) (xm : x ∈ X)
    (deep : Deep D X t x) : t + (outN D X x).card ≤ X.card := by
  obtain ⟨p⟩ := exists_shortest_sink_path free size xm
  have len := (deep_iff_len p).mp deep
  have := SinkTransit.internal_depth free size p
  omega

open scoped Classical in
/-- At most `|X| - t` rows of `X` are `t`-deep: the shortest sink path of any deep row
passes through `t` distinct rows that are not deep. -/
theorem deep_card {D X q t} (free : QFree D X q) (size : X.card ≤ q) :
    t + (X.filter (Deep D X t)).card ≤ X.card ∨ (X.filter (Deep D X t)) = ∅ := by
  classical
  by_cases empty : X.filter (Deep D X t) = ∅
  · exact Or.inr empty
  left
  obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.mpr empty
  obtain ⟨x0m, deep0⟩ := mem_filter.mp hx0
  obtain ⟨p⟩ := exists_shortest_sink_path free size x0m
  have len := (deep_iff_len p).mp deep0
  -- the last t rows of the path are shallow
  let f := fun j => p.vertex (p.len - j)
  let S := (range t).image f
  have shallow : ∀ a ∈ S, a ∈ X ∧ ¬Deep D X t a := by
    intro a am
    obtain ⟨j, jm, rfl⟩ := mem_image.mp am
    have jt := mem_range.mp jm
    refine ⟨p.mem _ (by omega), fun deep => ?_⟩
    have walk := p.walk (i := p.len - j) (j := p.len) (by omega) le_rfl
    have bound := deep _ (p.mem _ le_rfl) (fun z zm => p.sink z zm) _ walk
    omega
  have inj : Set.InjOn f (range t) := by
    intro i hi j hj eq
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have e := p.injective free size (x₁ := p.len - i) (x₂ := p.len - j)
      (by simp only [coe_range, Set.mem_Iio]; omega) (by simp only [coe_range, Set.mem_Iio]; omega) eq
    omega
  have cardS : S.card = t := by
    dsimp only [S]; rw [card_image_of_injOn inj, card_range]
  have disj : Disjoint S (X.filter (Deep D X t)) := by
    rw [disjoint_left]
    intro a aS aD
    exact (shallow a aS).2 (mem_filter.mp aD).2
  have sub : S ∪ X.filter (Deep D X t) ⊆ X :=
    union_subset (fun a aS => (shallow a aS).1) (filter_subset _ _)
  have := card_le_card sub
  rw [card_union_of_disjoint disj, cardS] at this
  exact this

open scoped Classical in
/-- **Return targets.** All rows of `X` receiving an arc from `w` are `(q - m)`-deep;
there are at most `|X| - (q - m)` of them. -/
theorem return_targets {D V X q w m} (free : QFree D V q) (xv : X ⊆ V) (size : X.card ≤ q)
    (reach : ∀ s ∈ X, Sink D X s → Walk D V s w m) :
    q - m + (outN D X w).card ≤ X.card ∨ (outN D X w) = ∅ := by
  classical
  have sub : outN D X w ⊆ X.filter (Deep D X (q - m)) := by
    intro x hx
    obtain ⟨xm, ret⟩ := mem_outN.mp hx
    exact mem_filter.mpr ⟨xm, return_deep free xv xm reach ret⟩
  rcases deep_card (t := q - m) (free.mono_set xv) size with bound | empty
  · left
    have := card_le_card sub
    omega
  · right
    exact subset_empty.mp (empty ▸ sub)

#print axioms return_deep
#print axioms return_deep_next
#print axioms deep_heads
#print axioms deep_card
#print axioms return_targets
end LeanCH.BR.SinkDepthReturn
