import LeanCH.BR.BRCycleReturn

/-! Equality in a shortest-cycle reentry window constrains the actual first
expansion. The cutoff and the return length remain arbitrary. -/
namespace LeanCH.BR.BRsub
open Finset BRq2 BRq3 BR45 BRsGen

theorem cycle_set_ball_growth_from {D : CH.Digraph} {M A : Finset ℕ} {q i : ℕ}
    (hq : 1 ≤ q) (hf : QFree D M q) (hM : M.card = q + 1) (hcyc : OutEq 1 D M)
    (hAM : A ⊆ M) (hAn : A.Nonempty) (k : ℕ) :
    min M.card ((ballSet D M A i).card + k) ≤ (ballSet D M A (i + k)).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hfull : ballSet D M A (i + k) = M
    · have hc := Finset.card_le_card
        (ballSet_mono (E := D) (V := M) (Y := A) (by omega : i + k ≤ i + (k + 1)))
      rw [hfull] at hc
      exact (Nat.min_le_left _ _).trans hc
    · have hlt : (ballSet D M A (i + k)).card < M.card := by
        by_contra hn
        exact hfull (Finset.eq_of_subset_of_card_le ballSet_subset (by omega))
      have hs := cycle_set_ball_step hq hf hM hcyc hAM hAn hfull
      have he : i + k + 1 = i + (k + 1) := by omega
      rw [he] at hs
      omega

/-- Reserve one genuine cycle-expansion step before applying the reentry cap. -/
theorem cycle_reentry_first_expansion {D : CH.Digraph} {V M A : Finset ℕ} {q z t : ℕ}
    (ht : t + 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : (inN D M z).Nonempty)
    (hAM : A ⊆ M) (hAn : A.Nonempty) (hreach : A ⊆ ball D V z t) :
    (inN D M z).card + (ballSet D M A 1).card ≤ t + 3 := by
  classical
  let B := ballSet D M A (q - t - 1)
  have hd : Disjoint (inN D M z) B := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxb
    obtain ⟨y, hy, hxy⟩ := mem_ballSet.mp hxb
    obtain ⟨_, i, hi, wy⟩ := mem_ball.mp (hreach hy)
    obtain ⟨_, j, hj, w⟩ := mem_ball.mp hxy
    exact hf z (i + j + 1) (by omega) (by omega)
      ((wy.append (w.mono hMV)).snoc hz (mem_inN.mp hxi).2)
  have hsub : inN D M z ∪ B ⊆ M :=
    Finset.union_subset (fun _ h => (mem_inN.mp h).1) ballSet_subset
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  have hg := cycle_set_ball_growth_from (i := 1) (by omega : 1 ≤ q)
    (hf.mono_set hMV) hM hcyc hAM hAn (q - t - 2)
  have he : 1 + (q - t - 2) = q - t - 1 := by omega
  rw [he] at hg
  have hi : 0 < (inN D M z).card := Finset.card_pos.mpr hin
  change min M.card ((ballSet D M A 1).card + (q - t - 2)) ≤ B.card at hg
  omega

theorem cycle_reentry_equality_expansion {D : CH.Digraph} {V M A : Finset ℕ} {q z t : ℕ}
    (ht : t + 2 ≤ q) (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hcyc : OutEq 1 D M) (hz : z ∈ V) (hin : (inN D M z).Nonempty)
    (hAM : A ⊆ M) (hAn : A.Nonempty) (hreach : A ⊆ ball D V z t)
    (heq : (inN D M z).card + A.card = t + 2) :
    (ballSet D M A 1).card ≤ A.card + 1 := by
  have h := cycle_reentry_first_expansion ht hf hMV hM hcyc hz hin hAM hAn hreach
  omega

/-- Two cycle vertices whose first ball has at most three vertices are adjacent. -/
theorem cycle_pair_adjacent_of_small_expansion {D : CH.Digraph} {M A : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D M q) (hcyc : OutEq 1 D M)
    (hind : ∀ v ∈ M, (inN D M v).card = 1)
    (hAM : A ⊆ M) (hA : A.card = 2) (hb : (ballSet D M A 1).card ≤ 3) :
    ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ D u v = true := by
  classical
  obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp hA
  have hx : x ∈ A := by rw [hpair]; simp
  have hy : y ∈ A := by rw [hpair]; simp
  by_contra hn
  have hnxy : ¬ D x y = true := fun h => hn ⟨x, hx, y, hy, hxy, h⟩
  have hnyx : ¬ D y x = true := fun h => hn ⟨y, hy, x, hx, hxy.symm, h⟩
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (by rw [hcyc x (hAM hx)]; decide)
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (by rw [hcyc y (hAM hy)]; decide)
  have hsM := outN_subset hs
  have htM := outN_subset ht
  have hxs := (mem_outN.mp hs).2
  have hyt := (mem_outN.mp ht).2
  have hsA : s ∉ A := by
    rw [hpair]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact loopfree hf hq (hAM hx) hxs
    · exact hnxy hxs
  have htA : t ∉ A := by
    rw [hpair]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hnyx hyt
    · exact loopfree hf hq (hAM hy) hyt
  have hst : s ≠ t := by
    intro he
    subst t
    exact hxy (Finset.card_le_one.mp (hind s hsM).le x
      (mem_inN.mpr ⟨hAM hx, hxs⟩) y (mem_inN.mpr ⟨hAM hy, hyt⟩))
  have hsB : s ∈ ballSet D M A 1 := mem_ballSet.mpr ⟨x, hx, ball_of_adj hsM hxs⟩
  have htB : t ∈ ballSet D M A 1 := mem_ballSet.mpr ⟨y, hy, ball_of_adj htM hyt⟩
  have hsub : insert s (insert t A) ⊆ ballSet D M A 1 :=
    Finset.insert_subset hsB (Finset.insert_subset htB (subset_ballSet hAM))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hst, hsA]),
    Finset.card_insert_of_notMem htA, hA] at hc
  omega

end LeanCH.BR.BRsub
