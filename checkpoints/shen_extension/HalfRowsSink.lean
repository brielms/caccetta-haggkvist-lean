import checkpoints.shen_extension.TightRowCapstone

/-!
# Half the rows are tight when out-neighbourhoods have sinks (cutoff 3)

Lean 4.35.0. Paper: `checkpoints/shen_extension/triangle_20261118/HalfLaw_20261118.md`.

Setting: a `3`-free digraph on `3d+2` vertices with every outdegree at least `d`. A row is tight if its outdegree
is exactly `d`.

* `sink_bound`: if `a` is a head of `u` with no head among the heads of `u`, then
  `out(a) + out(u) + in(u) + 1 ≤ n`. (The heads of `a` avoid the heads of `u`, the parents of `u`, and `u`.)
* `half_of_sinks`: if every out-neighbourhood has such a sink, at least half the rows are tight: `n ≤ 2t`.
  This is the one-above-the-boundary analogue of the project's sink lemma (boundary graphs with sinks are regular).
* `tight_of_sinks`: hence the tight-row conclusion `d + 2 ≤ t` for `d ≥ 1`, in the shape of `TightRow.TightLaw`.
* `sink_of_small`: in a `3`-free digraph a nonempty set of at most three vertices has a sink.
* `half_small`: so for `1 ≤ d ≤ 2` the half-rows statement holds for EVERY such digraph (trim heavy rows to
  outdegree `d+1 ≤ 3`; all out-neighbourhoods then have sinks).
* `tightLaw_three_one`, `tightLaw_three_two`: `TightLaw 3 1` and `TightLaw 3 2` are theorems.
* `capstone_three_two`, `capstone_three_three`: the literal capstone statement at `(3,2)` and `(3,3)` through the
  tight-row chain, with no supplied hypothesis. (Both cases were already known by other routes; the point is that
  the supplier chain runs end to end.)

* `source_sink_indeg`, `source_heads_have_heads`, `source_cyclic_neighbourhood`: the same local count on a
  hypothetical source (order at most `3s`, every outdegree at least `s`): a vertex of indegree at least `s` has no
  sink in its out-neighbourhood, and such a vertex exists. So every source carries a cyclic out-neighbourhood.

For `d ≥ 3` the hypothesis `HasSinks` is NOT automatic: a heavy row can have a directed 4-cycle as its
out-neighbourhood. That is the open case; nothing here closes CH.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.HalfRows

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.TightRow

variable {D : CH.Digraph} {V : Finset ℕ}

/-- In-neighbours inside `V` (the filter used in `TightRow.sum_indeg_eq_sum_outdeg`). -/
def inN (D : CH.Digraph) (V : Finset ℕ) (x : ℕ) : Finset ℕ := V.filter (fun y => D y x = true)

/-- Every out-neighbourhood has a sink: a head with no head among the heads. -/
def HasSinks (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ u ∈ V, ∃ a ∈ outN D V u, ∀ z ∈ outN D V a, z ∉ outN D V u

/-- The local count at a sink. -/
theorem sink_bound (free : QFree D V 3) {u a : ℕ} (hu : u ∈ V) (ha : a ∈ outN D V u)
    (sink : ∀ z ∈ outN D V a, z ∉ outN D V u) :
    (outN D V a).card + (outN D V u).card + (inN D V u).card + 1 ≤ V.card := by
  obtain ⟨haV, hua⟩ := mem_outN.mp ha
  have d1 : Disjoint (outN D V a) (outN D V u) := Finset.disjoint_left.mpr sink
  have d2 : Disjoint (outN D V a ∪ outN D V u) (inN D V u) := by
    rw [Finset.disjoint_left]
    intro z hz hzin
    have hzu : D z u = true := (Finset.mem_filter.mp hzin).2
    have hzV : z ∈ V := (Finset.mem_filter.mp hzin).1
    rcases Finset.mem_union.mp hz with h | h
    · exact free u 3 (by omega) le_rfl
        (.step haV hua (.step hzV (mem_outN.mp h).2 (.step hu hzu (.refl u))))
    · exact digonfree free (by omega) hu hzV (mem_outN.mp h).2 hzu
  have d3 : Disjoint (outN D V a ∪ outN D V u ∪ inN D V u) {u} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact digonfree free (by omega) hu haV hua (mem_outN.mp h).2
      · exact loopfree free (by omega) hu (mem_outN.mp h).2
    · exact loopfree free (by omega) hu (Finset.mem_filter.mp h).2
  have sub : outN D V a ∪ outN D V u ∪ inN D V u ∪ {u} ⊆ V := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with ((h | h) | h) | h
    · exact outN_subset h
    · exact outN_subset h
    · exact (Finset.mem_filter.mp h).1
    · exact h ▸ hu
  have c := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, Finset.card_singleton] at c
  exact c

/-- **Half the rows are tight** when every out-neighbourhood has a sink. -/
theorem half_of_sinks {d : ℕ} (free : QFree D V 3) (card : V.card = 3 * d + 2)
    (deg : ∀ x ∈ V, d ≤ (outN D V x).card) (sinks : HasSinks D V) :
    V.card ≤ 2 * (V.filter (fun x => (outN D V x).card = d)).card := by
  classical
  have ex : ∀ u, ∃ a, u ∈ V → a ∈ outN D V u ∧ ∀ z ∈ outN D V a, z ∉ outN D V u := by
    intro u
    by_cases hu : u ∈ V
    · obtain ⟨a, ha, hs⟩ := sinks u hu
      exact ⟨a, fun _ => ⟨ha, hs⟩⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose σ hσ using ex
  have pt : ∀ u ∈ V,
      (outN D V (σ u)).card + (outN D V u).card + (inN D V u).card + 1 ≤ V.card :=
    fun u hu => sink_bound free hu (hσ u hu).1 (hσ u hu).2
  have s1 := Finset.sum_le_sum pt
  simp only [Finset.sum_add_distrib, Finset.sum_const] at s1
  have hs1 : V.card • (1 : ℕ) = V.card := by simp
  have hs2 : V.card • V.card = V.card * V.card := by simp
  rw [hs1, hs2] at s1
  have sin : ∑ u ∈ V, (inN D V u).card = ∑ u ∈ V, (outN D V u).card :=
    sum_indeg_eq_sum_outdeg D V
  have lo1 : d * V.card ≤ ∑ u ∈ V, (outN D V (σ u)).card := by
    have := Finset.card_nsmul_le_sum V (fun u => (outN D V (σ u)).card) d
      (fun u hu => deg (σ u) (outN_subset (hσ u hu).1))
    simpa [mul_comm] using this
  have lo2 : (d + 1) * V.card ≤
      ∑ u ∈ V, (outN D V u).card + (V.filter (fun x => (outN D V x).card = d)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have := Finset.card_nsmul_le_sum V
      (fun u => (outN D V u).card + if (outN D V u).card = d then 1 else 0) (d + 1)
      (fun u hu => by have := deg u hu; split_ifs <;> omega)
    simpa [mul_comm] using this
  have sq : V.card * V.card = 3 * (d * V.card) + 2 * V.card := by
    have h : V.card * V.card = (3 * d + 2) * V.card := by rw [card]
    rw [h, Nat.add_mul, Nat.mul_assoc]
  have e2 : (d + 1) * V.card = d * V.card + V.card := by rw [Nat.add_mul, Nat.one_mul]
  rw [sin] at s1
  omega

/-! ### The same count on a hypothetical source (order at most `3s`, every outdegree at least `s`) -/

/-- On a source, a vertex whose out-neighbourhood has a sink has indegree at most `s - 1`. -/
theorem source_sink_indeg {s : ℕ} (free : QFree D V 3) (order : V.card ≤ 3 * s)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) {u a : ℕ} (hu : u ∈ V) (ha : a ∈ outN D V u)
    (sink : ∀ z ∈ outN D V a, z ∉ outN D V u) : (inN D V u).card + 1 ≤ s := by
  have h1 := sink_bound free hu ha sink
  have h2 := deg u hu
  have h3 := deg a (outN_subset ha)
  omega

/-- Equivalently: on a source, every head of a vertex of indegree at least `s` has a head among its heads. -/
theorem source_heads_have_heads {s : ℕ} (free : QFree D V 3) (order : V.card ≤ 3 * s)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) {u : ℕ} (hu : u ∈ V) (big : s ≤ (inN D V u).card) :
    ∀ a ∈ outN D V u, ∃ z ∈ outN D V a, z ∈ outN D V u := by
  intro a ha
  by_contra h
  push Not at h
  have := source_sink_indeg free order deg hu ha h
  omega

/-- **Every nonempty source has a vertex whose out-neighbourhood has no sink**: each of its heads has a head
among its heads (so its out-neighbourhood contains a directed cycle). -/
theorem source_cyclic_neighbourhood {s : ℕ} (free : QFree D V 3) (ne : V.Nonempty) (order : V.card ≤ 3 * s)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) :
    ∃ u ∈ V, ∀ a ∈ outN D V u, ∃ z ∈ outN D V a, z ∈ outN D V u := by
  obtain ⟨u, hu, big⟩ : ∃ u ∈ V, s ≤ (inN D V u).card := by
    by_contra bad
    push Not at bad
    have up : ∑ x ∈ V, (inN D V x).card < ∑ _x ∈ V, s :=
      Finset.sum_lt_sum_of_nonempty ne (fun x hx => bad x hx)
    have lo : ∑ _x ∈ V, s ≤ ∑ y ∈ V, (outN D V y).card := Finset.sum_le_sum deg
    have eq : ∑ x ∈ V, (inN D V x).card = ∑ y ∈ V, (outN D V y).card := sum_indeg_eq_sum_outdeg D V
    omega
  exact ⟨u, hu, source_heads_have_heads free order deg hu big⟩

/-- The tight-row conclusion, in the shape of `TightRow.TightLaw 3 d`, for digraphs with sinks. -/
theorem tight_of_sinks {d : ℕ} (hd : 1 ≤ d) (free : QFree D V 3) (card : V.card + 1 = 3 * (d + 1))
    (deg : ∀ x ∈ V, d ≤ (outN D V x).card) (sinks : HasSinks D V) :
    d + 2 ≤ (V.filter (fun x => (outN D V x).card = d)).card := by
  have := half_of_sinks free (by omega) deg sinks
  omega

/-- In a `3`-free digraph a nonempty set of at most three vertices has a sink. -/
theorem sink_of_small (free : QFree D V 3) {A : Finset ℕ} (hA : A ⊆ V) (ne : A.Nonempty)
    (small : A.card ≤ 3) : ∃ a ∈ A, ∀ z ∈ A, ¬ D a z = true := by
  classical
  by_contra h
  push Not at h
  have ex : ∀ a, ∃ z, a ∈ A → z ∈ A ∧ D a z = true := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨z, hz, arc⟩ := h a ha
      exact ⟨z, fun _ => ⟨hz, arc⟩⟩
    · exact ⟨0, fun h' => absurd h' ha⟩
  choose f hf using ex
  obtain ⟨a0, h0⟩ := ne
  have h1 := (hf a0 h0).1
  have e01 := (hf a0 h0).2
  have h2 := (hf (f a0) h1).1
  have e12 := (hf (f a0) h1).2
  have h3 := (hf (f (f a0)) h2).1
  have e23 := (hf (f (f a0)) h2).2
  have v0 := hA h0
  have v1 := hA h1
  have v2 := hA h2
  have v3 := hA h3
  have n01 : a0 ≠ f a0 := fun e => loopfree free (by omega) v0 (by rw [← e] at e01; exact e01)
  have n12 : f a0 ≠ f (f a0) := fun e => loopfree free (by omega) v1 (by rw [← e] at e12; exact e12)
  have n23 : f (f a0) ≠ f (f (f a0)) :=
    fun e => loopfree free (by omega) v2 (by rw [← e] at e23; exact e23)
  have n02 : a0 ≠ f (f a0) :=
    fun e => digonfree free (by omega) v0 v1 e01 (by rw [← e] at e12; exact e12)
  have n13 : f a0 ≠ f (f (f a0)) :=
    fun e => digonfree free (by omega) v1 v2 e12 (by rw [← e] at e23; exact e23)
  have n03 : a0 ≠ f (f (f a0)) := fun e =>
    free a0 3 (by omega) le_rfl
      (.step v1 e01 (.step v2 e12 (.step v0 (by rw [← e] at e23; exact e23) (.refl a0))))
  have s : ({a0, f a0, f (f a0), f (f (f a0))} : Finset ℕ) ⊆ A := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with e | e | e | e <;> rw [e] <;> assumption
  have k : ({a0, f a0, f (f a0), f (f (f a0))} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [n01, n02, n03]),
      Finset.card_insert_of_notMem (by simp [n12, n13]),
      Finset.card_insert_of_notMem (by simp [n23]), Finset.card_singleton]
  have := Finset.card_le_card s
  omega

/-- Trim every row to at most `d+1` heads. -/
theorem exists_trim {G : CH.Digraph} {d : ℕ} :
    ∃ G' : CH.Digraph, (∀ a b, G' a b = true → G a b = true) ∧
      ∀ v ∈ V, (outN G' V v).card = min (d + 1) (outN G V v).card := by
  classical
  have hex : ∀ a, ∃ t ⊆ outN G V a, t.card = min (d + 1) (outN G V a).card :=
    fun a => Finset.exists_subset_card_eq (min_le_right _ _)
  choose sel hsel hcard using hex
  refine ⟨fun a b => decide (b ∈ sel a), ?_, ?_⟩
  · intro a b hab
    exact (mem_outN.mp (hsel a (of_decide_eq_true hab))).2
  · intro v _
    have e : outN (fun a b => decide (b ∈ sel a)) V v = sel v := by
      ext z
      rw [mem_outN, decide_eq_true_eq]
      constructor
      · exact fun hz => hz.2
      · exact fun hz => ⟨(mem_outN.mp (hsel v hz)).1, hz⟩
    rw [e, hcard]

/-- **Half the rows are tight, unconditionally, for `1 ≤ d ≤ 2`.** -/
theorem half_small {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ 2) (free : QFree D V 3)
    (card : V.card = 3 * d + 2) (deg : ∀ x ∈ V, d ≤ (outN D V x).card) :
    V.card ≤ 2 * (V.filter (fun x => (outN D V x).card = d)).card := by
  obtain ⟨G, sub, trim⟩ := exists_trim (V := V) (G := D) (d := d)
  have gfree : QFree G V 3 := qfree_sub sub free
  have gdeg : ∀ x ∈ V, d ≤ (outN G V x).card := by
    intro x hx
    have := deg x hx
    rw [trim x hx]
    omega
  have gs : HasSinks G V := by
    intro u hu
    have c := trim u hu
    have lo := gdeg u hu
    obtain ⟨a, ha, hs⟩ := sink_of_small gfree (A := outN G V u) outN_subset
      (Finset.card_pos.mp (by omega)) (by omega)
    exact ⟨a, ha, fun z hz hzu => hs z hzu (mem_outN.mp hz).2⟩
  have key := half_of_sinks gfree card gdeg gs
  have same : V.filter (fun x => (outN G V x).card = d) = V.filter (fun x => (outN D V x).card = d) := by
    apply Finset.filter_congr
    intro x hx
    have := deg x hx
    rw [trim x hx]
    omega
  rw [same] at key
  exact key

/-- `TightLaw 3 1` is a theorem. -/
theorem tightLaw_three_one : TightLaw 3 1 := by
  intro E U free card deg
  have := half_small (d := 1) le_rfl (by omega) free (by omega) deg
  omega

/-- `TightLaw 3 2` is a theorem. -/
theorem tightLaw_three_two : TightLaw 3 2 := by
  intro E U free card deg
  have := half_small (d := 2) (by omega) le_rfl free (by omega) deg
  omega

/-- The literal capstone statement at `(3,2)` through the tight-row chain. -/
theorem capstone_three_two {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (order : n ≤ 3 * 2)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 2) :
    CH.HasDirectedCycleAtMost D n 3 :=
  capstone_of_tightLaw hn (by omega) order loop degree tightLaw_three_one

/-- The literal capstone statement at `(3,3)` through the tight-row chain. -/
theorem capstone_three_three {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (order : n ≤ 3 * 3)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 3) :
    CH.HasDirectedCycleAtMost D n 3 :=
  capstone_of_tightLaw hn (by omega) order loop degree tightLaw_three_two

end LeanCH.BR.HalfRows

open LeanCH.BR.HalfRows in
#print axioms half_of_sinks
open LeanCH.BR.HalfRows in
#print axioms tightLaw_three_two
open LeanCH.BR.HalfRows in
#print axioms capstone_three_three
open LeanCH.BR.HalfRows in
#print axioms source_cyclic_neighbourhood
