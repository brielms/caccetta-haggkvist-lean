import LeanCH.BR.BRFiniteWalk

/-! Closed subsets of any prescribed size in a finite acyclic induced graph. -/

namespace LeanCH.BR.BRq2

open BRq3

theorem exists_closed_subset_of_card {D : CH.Digraph} {X : Finset ℕ} {q k : ℕ}
    (hf : QFree D X q) (hc : X.card ≤ q) (hk : k ≤ X.card) :
    ∃ P ⊆ X, P.card = k ∧ ∀ p ∈ P, ∀ x ∈ X, D p x = true → x ∈ P := by
  classical
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨P, hPX, hP, hclosed⟩ := ih (by omega)
    have hne : (X \ P).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hPX, hP]
      omega
    obtain ⟨x, hx, hsink⟩ := exists_sink (hf.mono_set Finset.sdiff_subset) hne
      ((Finset.card_le_card Finset.sdiff_subset).trans hc)
    obtain ⟨hxX, hxP⟩ := Finset.mem_sdiff.mp hx
    refine ⟨insert x P, Finset.insert_subset hxX hPX, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hxP, hP]
    · intro p hp y hy hpy
      rcases Finset.mem_insert.mp hp with rfl | hpP
      · by_cases hyP : y ∈ P
        · exact Finset.mem_insert_of_mem hyP
        · exact (hsink y (Finset.mem_sdiff.mpr ⟨hy, hyP⟩) hpy).elim
      · exact Finset.mem_insert_of_mem (hclosed p hpP y hy hpy)

end LeanCH.BR.BRq2
