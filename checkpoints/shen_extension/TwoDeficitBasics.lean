import checkpoints.shen_extension.TiedDual

/-!
Counting tools for an oriented graph without directed triangles: the partition of the
vertex set around a vertex, sums of a supported weight, tournaments, and the subgraph
obtained by deleting two vertices.
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The reversed relation. -/
abbrev rev (r : V → V → Prop) : V → V → Prop := fun a b => r b a

/-- The other vertices not adjacent to `u`. -/
noncomputable def nonadj (r : V → V → Prop) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun z => z ≠ u ∧ ¬ r u z ∧ ¬ r z u)

theorem mem_nonadj {r : V → V → Prop} {u z : V} :
    z ∈ nonadj r u ↔ z ≠ u ∧ ¬ r u z ∧ ¬ r z u := by
  classical
  simp [nonadj]

theorem partition_facts (r : V → V → Prop) (hr : IsOriented r) (u : V) :
    (Finset.univ : Finset V) =
        insert u (firstNeighbors r u ∪ firstNeighbors (rev r) u ∪ nonadj r u) ∧
      u ∉ firstNeighbors r u ∪ firstNeighbors (rev r) u ∪ nonadj r u ∧
      Disjoint (firstNeighbors r u) (firstNeighbors (rev r) u) ∧
      Disjoint (firstNeighbors r u ∪ firstNeighbors (rev r) u) (nonadj r u) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · intro _
      by_cases h1 : z = u
      · exact Finset.mem_insert.mpr (Or.inl h1)
      · apply Finset.mem_insert.mpr
        right
        by_cases h2 : r u z
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (mem_firstNeighbors.mpr h2))))
        · by_cases h3 : r z u
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
              (Or.inr ((mem_firstNeighbors (r := rev r)).mpr h3))))
          · exact Finset.mem_union.mpr (Or.inr (mem_nonadj.mpr ⟨h1, h2, h3⟩))
    · intro _
      exact Finset.mem_univ z
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · exact hr.loopless u (mem_firstNeighbors.mp hu)
      · exact hr.loopless u ((mem_firstNeighbors (r := rev r)).mp hu)
    · exact (mem_nonadj.mp hu).1 rfl
  · apply Finset.disjoint_left.mpr
    intro z h1 h2
    exact hr.asymmetric (mem_firstNeighbors.mp h1) ((mem_firstNeighbors (r := rev r)).mp h2)
  · apply Finset.disjoint_left.mpr
    intro z h1 h2
    obtain ⟨_, hn1, hn2⟩ := mem_nonadj.mp h2
    rcases Finset.mem_union.mp h1 with h | h
    · exact hn1 (mem_firstNeighbors.mp h)
    · exact hn2 ((mem_firstNeighbors (r := rev r)).mp h)

theorem sum_partition (r : V → V → Prop) (hr : IsOriented r) (f : V → ℝ) (u : V) :
    ∑ z, f z = f u + ∑ z ∈ firstNeighbors r u, f z +
      ∑ z ∈ firstNeighbors (rev r) u, f z + ∑ z ∈ nonadj r u, f z := by
  classical
  obtain ⟨hcover, hu, hd1, hd2⟩ := partition_facts r hr u
  have h : ∑ z, f z =
      ∑ z ∈ insert u (firstNeighbors r u ∪ firstNeighbors (rev r) u ∪ nonadj r u), f z := by
    rw [← hcover]
  rw [h, Finset.sum_insert hu, Finset.sum_union hd2, Finset.sum_union hd1]
  ring

theorem card_partition (r : V → V → Prop) (hr : IsOriented r) (u : V) :
    Fintype.card V = 1 + (firstNeighbors r u).card + (firstNeighbors (rev r) u).card +
      (nonadj r u).card := by
  classical
  obtain ⟨hcover, hu, hd1, hd2⟩ := partition_facts r hr u
  have h := congrArg Finset.card hcover
  rw [Finset.card_univ, Finset.card_insert_of_notMem hu, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1] at h
  omega

theorem second_subset_nonadj (r : V → V → Prop)
    (htri : ∀ a b c, r a b → r b c → ¬ r c a) (u : V) :
    secondNeighbors r u ⊆ nonadj r u := by
  intro z hz
  obtain ⟨hne, hnot, a, hua, haz⟩ := mem_secondNeighbors.mp hz
  exact mem_nonadj.mpr ⟨hne, hnot, htri u a z hua haz⟩

omit [Fintype V] in
theorem sum_le_of_support {A B : Finset V} (δ : V → ℝ) (h0 : ∀ z, 0 ≤ δ z)
    (hsupp : ∀ z ∈ A, z ∉ B → δ z = 0) : ∑ z ∈ A, δ z ≤ ∑ z ∈ B, δ z := by
  classical
  have h1 : ∑ z ∈ A.filter (fun z => z ∈ B), δ z = ∑ z ∈ A, δ z :=
    Finset.sum_filter_of_ne (fun z hzA hne => by
      by_contra hzB
      exact hne (hsupp z hzA hzB))
  have h3 : ∑ z ∈ A.filter (fun z => z ∈ B), δ z ≤ ∑ z ∈ B, δ z :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z _ _ => h0 z)
  linarith

omit [Fintype V] in
theorem sum_add_le_of_support {A B : Finset V} (δ : V → ℝ) (h0 : ∀ z, 0 ≤ δ z)
    (hsupp : ∀ z ∈ A, z ∉ B → δ z = 0) (c : V) (hcB : c ∈ B) (hcA : c ∉ A) :
    ∑ z ∈ A, δ z + δ c ≤ ∑ z ∈ B, δ z := by
  classical
  have h1 : ∑ z ∈ A, δ z ≤ ∑ z ∈ B.erase c, δ z := by
    apply sum_le_of_support δ h0
    intro z hzA hz
    apply hsupp z hzA
    intro hzB
    apply hz
    refine Finset.mem_erase.mpr ⟨?_, hzB⟩
    intro hzc
    rw [hzc] at hzA
    exact hcA hzA
  have h2 := Finset.add_sum_erase B δ hcB
  linarith

/-- A nonempty set of pairwise adjacent vertices, each with an in-neighbour in the set,
contains a directed triangle. -/
theorem no_tournament_sourceless (r : V → V → Prop) (hr : IsOriented r)
    (htri : ∀ a b c, r a b → r b c → ¬ r c a) (T : Finset V) (hT : T.Nonempty)
    (hadj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → r a b ∨ r b a)
    (hpred : ∀ v ∈ T, ∃ u ∈ T, r u v) : False := by
  classical
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image T
    (fun v => (firstNeighbors r v ∩ T).card) hT
  obtain ⟨u, hu, huv⟩ := hpred v hv
  have hsub : insert v (firstNeighbors r v ∩ T) ⊆ firstNeighbors r u ∩ T := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzv | hz
    · rw [hzv]
      exact Finset.mem_inter.mpr ⟨mem_firstNeighbors.mpr huv, hv⟩
    · obtain ⟨hvz, hzT⟩ := Finset.mem_inter.mp hz
      have hvz' := mem_firstNeighbors.mp hvz
      have hzu : z ≠ u := by
        intro heq
        rw [heq] at hvz'
        exact hr.asymmetric huv hvz'
      rcases hadj z hzT u hu hzu with h1 | h1
      · exact absurd huv (htri v z u hvz' h1)
      · exact Finset.mem_inter.mpr ⟨mem_firstNeighbors.mpr h1, hzT⟩
  have hnot : v ∉ firstNeighbors r v ∩ T := fun hc =>
    hr.loopless v (mem_firstNeighbors.mp (Finset.mem_inter.mp hc).1)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at h1
  have h2 := hmax u hu
  omega

omit [Fintype V] in
theorem card_erase_two (A : Finset V) (x y : V) (hxy : x ≠ y) :
    ((A.erase x).erase y).card + (if x ∈ A then 1 else 0) + (if y ∈ A then 1 else 0) =
      A.card := by
  classical
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · have hy' : y ∈ A.erase x := Finset.mem_erase.mpr ⟨fun h => hxy h.symm, hy⟩
      have h1 := Finset.card_erase_add_one hy'
      have h2 := Finset.card_erase_add_one hx
      simp only [hx, hy, ↓reduceIte]
      omega
    · have hy' : y ∉ A.erase x := fun h => hy (Finset.mem_erase.mp h).2
      have h2 := Finset.card_erase_add_one hx
      rw [Finset.erase_eq_of_notMem hy']
      simp only [hx, hy, ↓reduceIte]
      omega
  · rw [Finset.erase_eq_of_notMem hx]
    by_cases hy : y ∈ A
    · have h1 := Finset.card_erase_add_one hy
      simp only [hx, hy, ↓reduceIte]
      omega
    · rw [Finset.erase_eq_of_notMem hy]
      simp only [hx, hy, ↓reduceIte]
      omega

section Sub

variable (x y : V)

/-- A relation restricted to the vertices other than `x` and `y`. -/
def sub (q : V → V → Prop) :
    {v : V // v ≠ x ∧ v ≠ y} → {v : V // v ≠ x ∧ v ≠ y} → Prop :=
  fun a b => q a.1 b.1

/-- The inclusion of the remaining vertices. -/
def subEmb : {v : V // v ≠ x ∧ v ≠ y} ↪ V := Function.Embedding.subtype _

theorem first_sub_map (q : V → V → Prop) (u : {v : V // v ≠ x ∧ v ≠ y}) :
    (firstNeighbors (sub x y q) u).map (subEmb x y) =
      ((firstNeighbors q u.1).erase x).erase y := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨z₀, hz₀, hzz⟩ := Finset.mem_map.mp hz
    have hzv : z₀.1 = z := hzz
    have hq : q u.1 z₀.1 := (mem_firstNeighbors (r := sub x y q)).mp hz₀
    rw [← hzv]
    exact Finset.mem_erase.mpr ⟨z₀.2.2, Finset.mem_erase.mpr ⟨z₀.2.1, mem_firstNeighbors.mpr hq⟩⟩
  · intro hz
    obtain ⟨hzy, hz'⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzx, hzq⟩ := Finset.mem_erase.mp hz'
    have hq : q u.1 z := mem_firstNeighbors.mp hzq
    exact Finset.mem_map.mpr ⟨⟨z, hzx, hzy⟩,
      (mem_firstNeighbors (r := sub x y q)).mpr hq, rfl⟩

theorem univ_sub_map :
    (Finset.univ : Finset {v : V // v ≠ x ∧ v ≠ y}).map (subEmb x y) =
      ((Finset.univ : Finset V).erase x).erase y := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨z₀, _, hzz⟩ := Finset.mem_map.mp hz
    have hzv : z₀.1 = z := hzz
    rw [← hzv]
    exact Finset.mem_erase.mpr ⟨z₀.2.2, Finset.mem_erase.mpr ⟨z₀.2.1, Finset.mem_univ _⟩⟩
  · intro hz
    obtain ⟨hzy, hz'⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzx, _⟩ := Finset.mem_erase.mp hz'
    exact Finset.mem_map.mpr ⟨⟨z, hzx, hzy⟩, Finset.mem_univ _, rfl⟩

end Sub

end LeanCH.BR.TwoSeymour
