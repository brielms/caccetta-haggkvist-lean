import OAI.Combinatorics.SecondNeighborhood.Main

/-!
End game with weak subset deficits and a marked vertex.

`r` is an oriented graph on `W` with positive in-degrees in which every nonempty proper
source set has `|N(N(S)) \ N(S)| ≤ |N(S) \ S|`, strictly when a marked vertex `h` is not
reached from `S` in one or two steps. Such a graph does not exist. The proof is the
vendored extremal argument on the transitive blow-up with blocks of size `k² + 2`
(`k = |W|`): the `k² + 1` columns over `h` with a positive block index avoid every vertex
reaching `h`, so each gains a whole block, which pays for the loss `k` of all other columns.
(After M. Kang, October 2026.)
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open OAI.SeymourSecondNeighborhood.Extremal
open scoped BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem card_add_card_le_of_sdiff {α : Type*} [DecidableEq α]
    (U X Y : Finset α) (e c : ℕ)
    (h : (U \ X).card + (Y \ X).card + e ≤ (X \ U).card + c) :
    U.card + Y.card + e ≤ 2 * X.card + c := by
  have hUX := Finset.card_sdiff_add_card U X
  have hXU := Finset.card_sdiff_add_card X U
  rw [Finset.union_comm X U] at hXU
  have hY : Y.card ≤ (Y \ X).card + X.card :=
    Finset.card_le_card_sdiff_add_card
  omega

/-- Every nonempty set of the blow-up loses at most `|W|`. -/
theorem blowup_growth {r : W → W → Prop} {m : ℕ} (hi : PositiveIndegree r)
    (hweak : ∀ S : Finset W, S.Nonempty → S ≠ Finset.univ →
      (image r (image r S) \ image r S).card ≤ (image r S \ S).card)
    (U : Finset (W × Fin m)) (hU : U.Nonempty) :
    U.card + (image (blowup r m) (image (blowup r m) U)).card ≤
      2 * (image (blowup r m) U).card + Fintype.card W := by
  classical
  by_cases hS : U.image Prod.fst = Finset.univ
  · have hX := blowup_image_eq_univ_of_full_support hi U hS
    have h1 : U.card ≤ (Finset.univ : Finset (W × Fin m)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    have h2 : (image (blowup r m) (image (blowup r m) U)).card ≤
        (Finset.univ : Finset (W × Fin m)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simp only [hX] at h2 ⊢
    omega
  · have hSne : (U.image Prod.fst).Nonempty := by
      obtain ⟨p, hp⟩ := hU
      exact ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hdef := hweak (U.image Prod.fst) hSne hS
    have hgain :
        (image (blowup r m) (image (blowup r m) U) \ image (blowup r m) U).card ≤
          (image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card * m := by
      simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_le_card (blowup_second_sdiff_subset (r := r) U))
    have hloss :
        (image r (U.image Prod.fst) \ U.image Prod.fst).card * m ≤
          (image (blowup r m) U \ U).card := by
      simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_le_card (blowup_boundary_product_subset (r := r) U))
    have hsource := blowup_source_sdiff_card_le (r := r) U
    have hamp := Nat.mul_le_mul_right m hdef
    have key := card_add_card_le_of_sdiff U (image (blowup r m) U)
      (image (blowup r m) (image (blowup r m) U)) 0 (Fintype.card W) (by omega)
    omega

/-- A set whose base support does not reach `h` in one or two steps gains a whole block. -/
theorem blowup_growth_strict {r : W → W → Prop} {m : ℕ} (hi : PositiveIndegree r) (h : W)
    (hstrict : ∀ S : Finset W, S.Nonempty → S ≠ Finset.univ →
      h ∉ image r S → h ∉ image r (image r S) →
      (image r (image r S) \ image r S).card < (image r S \ S).card)
    (U : Finset (W × Fin m)) (hU : U.Nonempty)
    (h1 : h ∉ image r (U.image Prod.fst))
    (h2 : h ∉ image r (image r (U.image Prod.fst))) :
    U.card + (image (blowup r m) (image (blowup r m) U)).card + m ≤
      2 * (image (blowup r m) U).card + Fintype.card W := by
  classical
  have hS : U.image Prod.fst ≠ Finset.univ := by
    intro hS
    obtain ⟨u, hu⟩ := hi h
    apply h1
    apply mem_image.mpr
    refine ⟨u, ?_, hu⟩
    rw [hS]
    exact Finset.mem_univ u
  have hSne : (U.image Prod.fst).Nonempty := by
    obtain ⟨p, hp⟩ := hU
    exact ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hdef := hstrict (U.image Prod.fst) hSne hS h1 h2
  have hgain :
      (image (blowup r m) (image (blowup r m) U) \ image (blowup r m) U).card ≤
        (image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card * m := by
    simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
      Fintype.card_fin] using
      (Finset.card_le_card (blowup_second_sdiff_subset (r := r) U))
  have hloss :
      (image r (U.image Prod.fst) \ U.image Prod.fst).card * m ≤
        (image (blowup r m) U \ U).card := by
    simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
      Fintype.card_fin] using
      (Finset.card_le_card (blowup_boundary_product_subset (r := r) U))
  have hsource := blowup_source_sdiff_card_le (r := r) U
  have hamp :
      (image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card * m + m ≤
        (image r (U.image Prod.fst) \ U.image Prod.fst).card * m := by
    have hstep :
        ((image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card + 1) * m ≤
          (image r (U.image Prod.fst) \ U.image Prod.fst).card * m :=
      Nat.mul_le_mul_right m (Nat.succ_le_of_lt hdef)
    simpa only [Nat.add_mul, Nat.one_mul] using hstep
  exact card_add_card_le_of_sdiff U (image (blowup r m) U)
    (image (blowup r m) (image (blowup r m) U)) m (Fintype.card W) (by omega)

/-- The marked indices: the block over `h`, without its first element. -/
def marked (h : W) (n : ℕ) : Finset (W × Fin (n + 1)) :=
  ({h} : Finset W) ×ˢ ({0}ᶜ : Finset (Fin (n + 1)))

omit [Fintype W] [DecidableEq W] in
theorem marked_card (h : W) (n : ℕ) : (marked h n).card = n := by
  classical
  simp [marked, Finset.card_compl]

theorem mem_marked {h : W} {n : ℕ} {j : W × Fin (n + 1)} :
    j ∈ marked h n ↔ j.1 = h ∧ j.2 ≠ 0 := by
  classical
  unfold marked
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_compl, Finset.mem_singleton]

/-- Total growth of a family of sets indexed by the blow-up, when the marked members
avoid everything that reaches `h`. -/
theorem family_total {r : W → W → Prop} {n : ℕ} (hi : PositiveIndegree r)
    (hweak : ∀ S : Finset W, S.Nonempty → S ≠ Finset.univ →
      (image r (image r S) \ image r S).card ≤ (image r S \ S).card)
    (h : W)
    (hstrict : ∀ S : Finset W, S.Nonempty → S ≠ Finset.univ →
      h ∉ image r S → h ∉ image r (image r S) →
      (image r (image r S) \ image r S).card < (image r S \ S).card)
    (c : W × Fin (n + 1) → Finset (W × Fin (n + 1)))
    (hne : ∀ j, (c j).Nonempty)
    (hfree : ∀ j ∈ marked h n, h ∉ image r ((c j).image Prod.fst) ∧
      h ∉ image r (image r ((c j).image Prod.fst))) :
    (∑ j, (c j).card) +
        (∑ j, (image (blowup r (n + 1)) (image (blowup r (n + 1)) (c j))).card) +
        n * (n + 1) ≤
      2 * (∑ j, (image (blowup r (n + 1)) (c j)).card) +
        Fintype.card W * (n + 1) * Fintype.card W := by
  classical
  have hpoint : ∀ j : W × Fin (n + 1),
      (c j).card + (image (blowup r (n + 1)) (image (blowup r (n + 1)) (c j))).card +
          (if j ∈ marked h n then n + 1 else 0) ≤
        2 * (image (blowup r (n + 1)) (c j)).card + Fintype.card W := by
    intro j
    by_cases hj : j ∈ marked h n
    · simp only [hj, ↓reduceIte]
      exact blowup_growth_strict hi h hstrict (c j) (hne j) (hfree j hj).1 (hfree j hj).2
    · simp only [hj, ↓reduceIte]
      have := blowup_growth hi hweak (c j) (hne j)
      omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (W × Fin (n + 1))))
    (fun j _ => hpoint j)
  have hite : (∑ j : W × Fin (n + 1), (if j ∈ marked h n then n + 1 else 0)) =
      n * (n + 1) := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul, marked_card]
  have hconst : (∑ _j : W × Fin (n + 1), Fintype.card W) =
      Fintype.card W * (n + 1) * Fintype.card W := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hite, hconst] at hsum
  exact hsum

/-- No oriented graph has weak subset deficits everywhere and strict ones away from `h`. -/
theorem endgame [Nonempty W] {r : W → W → Prop} (hr : IsOriented r)
    (hi : PositiveIndegree r)
    (hweak : ∀ S : Finset W, S.Nonempty → S ≠ Finset.univ →
      (image r (image r S) \ image r S).card ≤ (image r S \ S).card)
    (h : W)
    (hstrict : ∀ S : Finset W, S.Nonempty → S ≠ Finset.univ →
      h ∉ image r S → h ∉ image r (image r S) →
      (image r (image r S) \ image r S).card < (image r S \ S).card) : False := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card W * Fintype.card W + 1 := ⟨_, rfl⟩
  let B := blowup r (n + 1)
  have hB : IsOriented B := blowup_isOriented hr (n + 1)
  have hposB : PositiveIndegree B := blowup_positiveIndegree hi (n + 1)
  have : Nonempty (W × Fin (n + 1)) := ⟨(Classical.arbitrary W, 0)⟩
  obtain ⟨P, Q, hadm, hmax⟩ := exists_maximizing_pair B (Admissible B)
    ⟨diagonal, diagonal, diagonal_admissible hB⟩
  obtain ⟨P', Q', hp⟩ := Pruning.pruning B (leftCandidate B Q) (rightCandidate B P)
  have hnext : Admissible B P' Q' := pruning_preserves_diagonal hadm hp
  have hHc : (H B (leftCandidate B Q) (rightCandidate B P)).card ≤
      uncoveredCount B P Q := by
    exact H_candidates_card_le_uncovered B P Q
  -- columns of P
  have hleft := family_total (n := n) hi hweak h hstrict (fun j => column P j)
    (column_nonempty_of_diagonal hadm.diagonal_left) (by
      intro j hj
      obtain ⟨hj1, hj2⟩ := mem_marked.mp hj
      constructor
      · intro hmem
        obtain ⟨u, hu, huh⟩ := mem_image.mp hmem
        obtain ⟨p, hpc, hpu⟩ := Finset.mem_image.mp hu
        have hpP : (p, j) ∈ P := mem_column.mp hpc
        apply hadm.compatible (p, j) hpP ((h, 0), (h, 0))
          (hadm.diagonal_right (diagonal_mem _))
        refine ⟨Or.inl ?_, Or.inr ⟨hj1.symm, ?_⟩⟩
        · rw [hpu]
          exact huh
        · exact Fin.pos_of_ne_zero hj2
      · intro hmem
        obtain ⟨y, hy, hyh⟩ := mem_image.mp hmem
        obtain ⟨u, hu, huy⟩ := mem_image.mp hy
        obtain ⟨p, hpc, hpu⟩ := Finset.mem_image.mp hu
        have hpP : (p, j) ∈ P := mem_column.mp hpc
        apply hadm.compatible (p, j) hpP ((y, j.2), (y, j.2))
          (hadm.diagonal_right (diagonal_mem _))
        refine ⟨Or.inl ?_, Or.inl ?_⟩
        · rw [hpu]
          exact huy
        · rw [hj1]
          exact hyh)
  -- rows of Q
  have hright := family_total (n := n) hi hweak h hstrict (fun i => row Q i)
    (row_nonempty_of_diagonal hadm.diagonal_right) (by
      intro i hi'
      obtain ⟨hi1, hi2⟩ := mem_marked.mp hi'
      constructor
      · intro hmem
        obtain ⟨u, hu, huh⟩ := mem_image.mp hmem
        obtain ⟨s, hsc, hsu⟩ := Finset.mem_image.mp hu
        have hsQ : (i, s) ∈ Q := mem_row.mp hsc
        apply hadm.compatible ((h, 0), (h, 0)) (hadm.diagonal_left (diagonal_mem _))
          (i, s) hsQ
        refine ⟨Or.inr ⟨hi1.symm, ?_⟩, Or.inl ?_⟩
        · exact Fin.pos_of_ne_zero hi2
        · rw [hsu]
          exact huh
      · intro hmem
        obtain ⟨y, hy, hyh⟩ := mem_image.mp hmem
        obtain ⟨u, hu, huy⟩ := mem_image.mp hy
        obtain ⟨s, hsc, hsu⟩ := Finset.mem_image.mp hu
        have hsQ : (i, s) ∈ Q := mem_row.mp hsc
        apply hadm.compatible ((y, i.2), (y, i.2)) (hadm.diagonal_left (diagonal_mem _))
          (i, s) hsQ
        refine ⟨Or.inl ?_, Or.inl ?_⟩
        · rw [hi1]
          exact hyh
        · rw [hsu]
          exact huy)
  have eP := card_eq_sum_card_column P
  have eLP := card_eq_sum_card_column (leftImage B P)
  have eLLP := card_eq_sum_card_column (leftImage B (leftImage B P))
  have eQ := card_eq_sum_card_row Q
  have eRQ := card_eq_sum_card_row (rightImage B Q)
  have eRRQ := card_eq_sum_card_row (rightImage B (rightImage B Q))
  simp only [column_leftImage] at eLP eLLP
  simp only [row_rightImage] at eRQ eRRQ
  rw [← eP, ← eLLP, ← eLP] at hleft
  rw [← eQ, ← eRRQ, ← eRQ] at hright
  have hbig : Fintype.card W * (n + 1) * Fintype.card W + (n + 1) ≤ n * (n + 1) := by
    have h1 : (Fintype.card W * Fintype.card W + 1) * (n + 1) ≤ n * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) (le_of_eq hn.symm)
    have h2 : (Fintype.card W * Fintype.card W + 1) * (n + 1) =
        Fintype.card W * (n + 1) * Fintype.card W + (n + 1) := by ring
    omega
  have hgain : P.card + Q.card + 2 * uncoveredCount B P Q <
      (leftCandidate B Q).card + (rightCandidate B P).card := by
    have huncovered := uncoveredCount_add_images hadm.compatible
    have hR : (leftCandidate B Q).card +
        (rightImage B (rightImage B Q)).card =
          (Finset.univ : Finset ((W × Fin (n + 1)) × (W × Fin (n + 1)))).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    have hC : (rightCandidate B P).card +
        (leftImage B (leftImage B P)).card =
          (Finset.univ : Finset ((W × Fin (n + 1)) × (W × Fin (n + 1)))).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    omega
  have hbetter := objective_lt_of_pruning hp hHc hgain
  exact (not_lt_of_ge (hmax P' Q' hnext)) hbetter

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.endgame
