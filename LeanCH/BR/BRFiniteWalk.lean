import LeanCH.BR.BRq3Base

/-! Finite walk tools for structural arguments on almost acyclic sets. -/

namespace LeanCH.BR.BRq2

open BRq3

variable {D : CH.Digraph} {W : Finset ℕ}

theorem walk_of_edges {f : ℕ → ℕ} {m : ℕ}
    (hf : ∀ i, i < m → f (i + 1) ∈ W ∧ D (f i) (f (i + 1)) = true) :
    Walk D W (f 0) (f m) m := by
  induction m with
  | zero => exact .refl _
  | succ m ih =>
    exact (ih (fun i hi => hf i (by omega))).snoc (hf m (by omega)).1 (hf m (by omega)).2

theorem walk_between {f : ℕ → ℕ} {m i j : ℕ}
    (hf : ∀ k, k < m → f (k + 1) ∈ W ∧ D (f k) (f (k + 1)) = true)
    (hij : i ≤ j) (hjm : j ≤ m) : Walk D W (f i) (f j) (j - i) := by
  have h := walk_of_edges (f := fun k => f (i + k)) (m := j - i) (fun k hk => by
    simpa only [Nat.add_assoc] using hf (i + k) (by omega))
  simpa only [Nat.add_zero, Nat.add_sub_cancel' hij] using h

/-- A closed walk one step beyond the cutoff covers a host of that order. -/
theorem minOut_of_boundary_closed_walk {q a : ℕ} (hf : QFree D W q)
    (hcard : W.card = q + 1) (w : Walk D W a a (q + 1)) :
    ∀ x ∈ W, 1 ≤ (outN D W x).card := by
  classical
  obtain ⟨f, h0, hm, he⟩ := w.toFun
  have hmem : ∀ i, i ≤ q + 1 → f i ∈ W := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [h0, ← hm]
      exact (he q (by omega)).1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i - 1) (by omega)).1
  have hinj : Set.InjOn f (Finset.range (q + 1)) := by
    intro i hi j hj heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hij | hji
    · have wc := walk_between he hij.le (by omega : j ≤ q + 1)
      rw [← heq] at wc
      exact hf (f i) (j - i) (by omega) (by omega) wc
    · have wc := walk_between he hji.le (by omega : i ≤ q + 1)
      rw [heq] at wc
      exact hf (f j) (i - j) (by omega) (by omega) wc
  have hsub : (Finset.range (q + 1)).image f ⊆ W := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (by have := Finset.mem_range.mp hi; omega)
  have hspan := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, hcard])
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hspan.symm ▸ hx)
  exact Finset.card_pos.mpr ⟨f (i + 1), mem_outN.mpr (he i (Finset.mem_range.mp hi))⟩

/-- A closed walk one step beyond the cutoff has a support of exactly that size. -/
theorem boundary_closed_walk_support {q a : ℕ} (hf : QFree D W q)
    (w : Walk D W a a (q + 1)) :
    ∃ M ⊆ W, M.card = q + 1 ∧ ∀ x ∈ M, 1 ≤ (outN D M x).card := by
  classical
  obtain ⟨f, h0, hm, he⟩ := w.toFun
  have hmem : ∀ i, i ≤ q + 1 → f i ∈ W := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [h0, ← hm]
      exact (he q (by omega)).1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i - 1) (by omega)).1
  have hinj : Set.InjOn f (Finset.range (q + 1)) := by
    intro i hi j hj heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hij | hji
    · have wc := walk_between he hij.le (by omega : j ≤ q + 1)
      rw [← heq] at wc
      exact hf (f i) (j - i) (by omega) (by omega) wc
    · have wc := walk_between he hji.le (by omega : i ≤ q + 1)
      rw [heq] at wc
      exact hf (f j) (i - j) (by omega) (by omega) wc
  let M := (Finset.range (q + 1)).image f
  have hMi : ∀ i, i < q + 1 → f i ∈ M := fun i hi =>
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  refine ⟨M, ?_, (Finset.card_image_of_injOn hinj).trans (Finset.card_range _), ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (by have := Finset.mem_range.mp hi; omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hiq := Finset.mem_range.mp hi
    have hnext : f (i + 1) ∈ M := by
      by_cases hlast : i = q
      · rw [hlast, hm, ← h0]
        exact hMi 0 (by omega)
      · exact hMi (i + 1) (by omega)
    exact Finset.card_pos.mpr ⟨f (i + 1), mem_outN.mpr ⟨hnext, (he i hiq).2⟩⟩

/-- A sink excludes the only extra cycle length at boundary order for degree one. -/
theorem qfree_succ_of_sink {q t : ℕ} (hf : QFree D W q)
    (hcard : W.card = q + 1) (ht : t ∈ W)
    (hsink : ∀ z ∈ W, ¬ D t z = true) : QFree D W (q + 1) := by
  intro a m hm hmq w
  by_cases hle : m ≤ q
  · exact hf a m hm hle w
  · have heq : m = q + 1 := by omega
    subst m
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (minOut_of_boundary_closed_walk hf hcard w t ht)
    exact hsink z (mem_outN.mp hz).1 (mem_outN.mp hz).2

/-- An acyclic finite set has a sink reachable from each vertex in at most `|W|-1` steps. -/
theorem reach_sink_of_card {q a : ℕ} (hf : QFree D W q)
    (hcard : W.card ≤ q) (ha : a ∈ W) :
    ∃ t ∈ W, (∀ z ∈ W, ¬ D t z = true) ∧
      ∃ m, m < W.card ∧ Walk D W a t m := by
  classical
  suffices ∀ n, ∀ (T : Finset ℕ), T.card = n → QFree D T q → T.card ≤ q →
      ∀ a ∈ T, ∃ t ∈ T, (∀ z ∈ T, ¬ D t z = true) ∧
        ∃ m, m < T.card ∧ Walk D T a t m from this W.card W rfl hf hcard a ha
  intro n
  induction n with
  | zero =>
    intro T hT _ _ a ha
    have := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  | succ n ih =>
    intro T hT hfree hc a ha
    by_cases hh : ∃ b ∈ T, D a b = true
    · obtain ⟨b, hb, hab⟩ := hh
      have hba : b ≠ a := by
        intro h
        exact loopfree hfree (by omega) ha (h ▸ hab)
      have hTc : (T.erase a).card = n := by rw [Finset.card_erase_of_mem ha, hT]; omega
      obtain ⟨t, ht, hsink, m, hm, w⟩ := ih (T.erase a) hTc
        (hfree.mono_set (Finset.erase_subset _ _)) (by rw [hTc]; omega)
        b (Finset.mem_erase.mpr ⟨hba, hb⟩)
      have wat : Walk D T a t (m + 1) := .step hb hab (w.mono (Finset.erase_subset _ _))
      refine ⟨t, Finset.mem_of_mem_erase ht, ?_, m + 1, ?_, wat⟩
      · intro z hz htz
        by_cases hza : z = a
        · exact hfree a (m + 1 + 1) (by omega) (by rw [hTc] at hm; omega)
            (wat.snoc ha (hza ▸ htz))
        · exact hsink z (Finset.mem_erase.mpr ⟨hza, hz⟩) htz
      · rw [hTc] at hm
        omega
    · refine ⟨a, ha, ?_, 0, Finset.card_pos.mpr ⟨a, ha⟩, .refl a⟩
      intro z hz haz
      exact hh ⟨z, hz, haz⟩

/-- A shortest path from a specified vertex to any sink of the induced graph. -/
structure ShortestSinkPath (D : CH.Digraph) (W : Finset ℕ) (a : ℕ) where
  len : ℕ
  vertex : ℕ → ℕ
  start : vertex 0 = a
  bounded : len < W.card
  mem : ∀ i, i ≤ len → vertex i ∈ W
  edge : ∀ i, i < len → D (vertex i) (vertex (i + 1)) = true
  sink : ∀ z ∈ W, ¬ D (vertex len) z = true
  minimal : ∀ t ∈ W, (∀ z ∈ W, ¬ D t z = true) →
    ∀ m, Walk D W a t m → len ≤ m

theorem exists_shortest_sink_path {q a : ℕ} (hf : QFree D W q)
    (hc : W.card ≤ q) (ha : a ∈ W) : Nonempty (ShortestSinkPath D W a) := by
  classical
  let P (m : ℕ) : Prop := ∃ t ∈ W, (∀ z ∈ W, ¬ D t z = true) ∧ Walk D W a t m
  obtain ⟨t, ht, hts, m, hm, w⟩ := reach_sink_of_card hf hc ha
  have hex : ∃ m, P m := ⟨m, t, ht, hts, w⟩
  obtain ⟨b, hb, hbs, wb⟩ := Nat.find_spec hex
  obtain ⟨f, h0, hlast, he⟩ := wb.toFun
  refine ⟨{
    len := Nat.find hex
    vertex := f
    start := h0
    bounded := (Nat.find_min' hex ⟨t, ht, hts, w⟩).trans_lt hm
    mem := ?_
    edge := fun i hi => (he i hi).2
    sink := ?_
    minimal := ?_ }⟩
  · intro i hi
    by_cases hi0 : i = 0
    · simpa only [hi0, h0] using ha
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i - 1) (by omega)).1
  · simpa only [hlast] using hbs
  · intro z hz hzs k wk
    exact Nat.find_min' hex ⟨z, hz, hzs, wk⟩

namespace ShortestSinkPath

variable {a q : ℕ} (p : ShortestSinkPath D W a)

theorem walk {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.len) :
    Walk D W (p.vertex i) (p.vertex j) (j - i) :=
  walk_between (fun k hk => ⟨p.mem (k + 1) (by omega), p.edge k hk⟩) hij hj

theorem injective (hf : QFree D W q) (hc : W.card ≤ q) :
    Set.InjOn p.vertex (Finset.range (p.len + 1)) := by
  intro i hi j hj heq
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hlen := p.bounded
  by_contra hn
  rcases Nat.lt_or_gt_of_ne hn with hij | hji
  · have w := p.walk hij.le (by omega : j ≤ p.len)
    rw [← heq] at w
    exact hf (p.vertex i) (j - i) (by omega) (by omega) w
  · have w := p.walk hji.le (by omega : i ≤ p.len)
    rw [heq] at w
    exact hf (p.vertex j) (i - j) (by omega) (by omega) w

/-- Among path vertices the only possible arcs are its consecutive arcs. -/
theorem no_chord (hf : QFree D W q) (hc : W.card ≤ q)
    {i j : ℕ} (hi : i ≤ p.len) (hj : j ≤ p.len)
    (hij : D (p.vertex i) (p.vertex j) = true) : j = i + 1 := by
  have hlen := p.bounded
  by_cases hji : j ≤ i
  · exact (hf (p.vertex j) (i - j + 1) (by omega) (by omega)
      ((p.walk hji hi).snoc (p.mem j hj) hij)).elim
  · have w1 := p.walk (Nat.zero_le i) hi
    have w2 := p.walk hj le_rfl
    have w := (w1.snoc (p.mem j hj) hij).append w2
    rw [p.start] at w
    have hmin := p.minimal (p.vertex p.len) (p.mem _ le_rfl) p.sink
      (i - 0 + 1 + (p.len - j)) w
    omega

end ShortestSinkPath

end LeanCH.BR.BRq2
