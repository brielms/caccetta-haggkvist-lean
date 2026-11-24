import LeanCH.BR.BR45Base

/-! Entry into all but one vertex of an acyclic set gives a short exterior funnel. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {R S : Finset ℕ} {q d a : ℕ}

/-- An external row heading all but at most one vertex of R reaches every S-vertex in at most three steps. -/
theorem almost_full_entry_funnel (hf : QFree D R q) (hR : R.card ≤ q)
    (hR2 : 2 ≤ R.card) (hS : S.card = d)
    (hhigh : ∀ r ∈ R, d ≤ (outN D (R ∪ S) r).card)
    (hentry : R.card ≤ (outN D R a).card + 1) :
    ∀ w ∈ S, ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Walk D (R ∪ S) a w m := by
  classical
  let T := outN D R a
  have hTR : T ⊆ R := outN_subset
  have hTc : 1 ≤ T.card := by change R.card ≤ T.card + 1 at hentry; omega
  have hEc : (R \ T).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hTR]
    change R.card ≤ T.card + 1 at hentry
    omega
  intro w hw
  by_cases hdirect : ∃ t ∈ T, D t w = true
  · obtain ⟨t, ht, htw⟩ := hdirect
    exact ⟨2, by decide, by decide, .step (Finset.mem_union_left _ (hTR ht)) (mem_outN.mp ht).2
      (.step (Finset.mem_union_right _ hw) htw (.refl w))⟩
  have hminT : ∀ t ∈ T, 1 ≤ (outN D R t).card := by
    intro t ht
    have hsub : outN D (R ∪ S) t ⊆ outN D R t ∪ S.erase w := by
      intro v hv
      obtain ⟨hvU, htv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvU with hvR | hvS
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hvR, htv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
          ⟨fun h => hdirect ⟨t, ht, h ▸ htv⟩, hvS⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem hw, hS] at hc
    have hh := hhigh t (hTR ht)
    have hd : 1 ≤ d := by have := Finset.card_pos.mpr ⟨w, hw⟩; omega
    omega
  obtain ⟨c, hc, hcs⟩ := exists_sink hf (Finset.card_pos.mp (by omega : 0 < R.card)) hR
  have hcT : c ∉ T := by
    intro hcT
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (hminT c hcT)
    exact hcs v (mem_outN.mp hv).1 (mem_outN.mp hv).2
  have hfull : D c w = true := by
    have hsub : outN D (R ∪ S) c ⊆ S := by
      intro v hv
      obtain ⟨hvU, hcv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvU with hvR | hvS
      · exact (hcs v hvR hcv).elim
      · exact hvS
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hS]; exact hhigh c hc)
    exact (mem_outN.mp (heq.symm ▸ hw)).2
  obtain ⟨t, ht, hts⟩ := exists_sink (hf.mono_set hTR)
    (Finset.card_pos.mp hTc) ((Finset.card_le_card hTR).trans hR)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (hminT t ht)
  obtain ⟨hvR, htv⟩ := mem_outN.mp hv
  have hvT : v ∉ T := fun hvT => hts v hvT htv
  have hvc := Finset.card_le_one.mp hEc v (Finset.mem_sdiff.mpr ⟨hvR, hvT⟩)
    c (Finset.mem_sdiff.mpr ⟨hc, hcT⟩)
  exact ⟨3, by decide, le_rfl, .step (Finset.mem_union_left _ (hTR ht)) (mem_outN.mp ht).2
    (.step (Finset.mem_union_left _ hc) (hvc ▸ htv)
      (.step (Finset.mem_union_right _ hw) hfull (.refl w)))⟩

end LeanCH.BR.BRsGen
