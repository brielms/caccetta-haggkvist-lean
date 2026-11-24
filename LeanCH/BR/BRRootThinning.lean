import LeanCH.BR.BRq3Base

/-! Thin one row to a prescribed degree while retaining a designated set of heads. -/

namespace LeanCH.BR.BRq3

theorem exists_root_thinning {D : CH.Digraph} {V H : Finset ℕ} {u d : ℕ}
    (hH : H ⊆ outN D V u) (hHd : H.card ≤ d) (hd : d ≤ (outN D V u).card) :
    ∃ F : CH.Digraph, (∀ a b, F a b = true → D a b = true) ∧
      (outN F V u).card = d ∧ H ⊆ outN F V u ∧
      (∀ v, v ≠ u → outN F V v = outN D V v) := by
  classical
  obtain ⟨S, hHS, hS, hSc⟩ := Finset.exists_subsuperset_card_eq hH hHd hd
  let F : CH.Digraph := fun a b => if a = u then decide (b ∈ S) else D a b
  have hrow : outN F V u = S := by
    ext v
    constructor
    · intro hv
      simpa [F] using (mem_outN.mp hv).2
    · intro hv
      exact mem_outN.mpr ⟨(mem_outN.mp (hS hv)).1, by simp [F, hv]⟩
  refine ⟨F, ?_, by rw [hrow]; exact hSc, by rw [hrow]; exact hHS, ?_⟩
  · intro a b hab
    by_cases ha : a = u
    · subst a
      exact (mem_outN.mp (hS (by simpa [F] using hab))).2
    · simpa [F, ha] using hab
  · intro v hv
    ext w
    simp [mem_outN, F, hv]

end LeanCH.BR.BRq3
