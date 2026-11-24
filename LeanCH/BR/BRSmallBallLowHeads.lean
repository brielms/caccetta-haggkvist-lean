import LeanCH.BR.BRHighHighProfile
import LeanCH.BR.BRLowRowPenalty
import LeanCH.BR.BRRootThinning

/-! High vertices with a small ball have at least three heads outside the high set. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem high_small_ball_low_heads_exact {D : CH.Digraph} {V H : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = 6)
    (hball : (ball D V u 4).card ≤ 15) : 3 ≤ (outN D (V \ H) u).card := by
  classical
  by_cases hex : ∃ v ∈ outN D V u, v ∈ H
  · obtain ⟨v, hv, hvH⟩ := hex
    have hsecond := (high_high_small_four_profile hf hmin hu hdegree hv
      (hhigh v hvH) hball).1
    have hh := small_first_high_heads_bound (d := 3) (s := 6)
      (by decide : 2 ≤ 5) (by decide) hf hu (by omega) hHV hhigh (by omega)
    have hs := card_outN_union (D := D) (show Disjoint H (V \ H) from Finset.disjoint_sdiff) u
    rw [Finset.union_sdiff_of_subset hHV] at hs
    omega
  · have hsub : outN D V u ⊆ outN D (V \ H) u := by
      intro v hv
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr
        ⟨(mem_outN.mp hv).1, fun hvH => hex ⟨v, hv, hvH⟩⟩, (mem_outN.mp hv).2⟩
    have hc := Finset.card_le_card hsub
    omega

theorem high_small_ball_low_heads {D : CH.Digraph} {V H : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hu : u ∈ V) (hdegree : 6 ≤ (outN D V u).card)
    (hball : (ball D V u 4).card ≤ 15) : 3 ≤ (outN D (V \ H) u).card := by
  classical
  obtain ⟨F, hsub, hdeg, _, hrows⟩ := exists_root_thinning
    (H := ∅) (Finset.empty_subset _) (by simp : (∅ : Finset ℕ).card ≤ 6) hdegree
  have hminF : ∀ v ∈ V, 3 ≤ (outN F V v).card := by
    intro v hv
    by_cases heq : v = u
    · subst v; omega
    · rw [hrows v heq]; exact hmin v hv
  have hhighF : ∀ v ∈ H, 6 ≤ (outN F V v).card := by
    intro v hv
    by_cases heq : v = u
    · subst v; omega
    · rw [hrows v heq]; exact hhigh v hv
  have hballF : (ball F V u 4).card ≤ 15 :=
    (Finset.card_le_card (ball_sub hsub)).trans hball
  apply (high_small_ball_low_heads_exact (qfree_sub hsub hf) hminF hHV hhighF
    hu hdeg hballF).trans
  apply Finset.card_le_card
  intro v hv
  exact mem_outN.mpr ⟨(mem_outN.mp hv).1, hsub u v (mem_outN.mp hv).2⟩

end LeanCH.BR.BRsGen
