import LeanCH.BR.BROneExtraClosure
import LeanCH.BR.BRAcyclicClosedSubset
import LeanCH.BR.BRHighThreeCore

/-! The next unequal-triple target: third-layer excess two and retained degree three. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

structure TwoExtraTriple (D : CH.Digraph) (X Y Z : Finset ℕ) (s : ℕ) : Prop where
  large : 6 ≤ s
  free : QFree D (X ∪ Y ∪ Z) (s - 1)
  disjoint_first : Disjoint X Y
  disjoint_third : Disjoint (X ∪ Y) Z
  card_first : X.card = s
  card_second : Y.card = s
  card_third : Z.card = s + 2
  high_first : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card
  high_second : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card
  low_third : ∀ z ∈ Z, 3 ≤ (outN D (X ∪ Y ∪ Z) z).card
  parents : ∀ z ∈ Z, ∃ y ∈ Y, D y z = true

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s : ℕ}

/-- Deleting a closed first-layer tail leaves a forbidden degree-three core. -/
theorem TwoExtraTriple.acyclic_false (h : TwoExtraTriple D X Y Z s)
    (hacy : QFree D X s) : False := by
  classical
  have hs := h.large
  have hf := h.free
  have hX := h.card_first
  have hY := h.card_second
  have hZ := h.card_third
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  obtain ⟨P, hPX, hPc, hclosed⟩ := exists_closed_subset_of_card hacy (by omega)
    (show s - 3 ≤ X.card by omega)
  have hPU := hPX.trans hXU
  have hexit : ∀ p ∈ P, ∃ t ∈ P, (∀ y ∈ Y, D t y = true) ∧
      ∃ m, m < s - 3 ∧ Walk D P p t m := by
    intro p hp
    obtain ⟨t, ht, hsink, m, hm, w⟩ := reach_sink_of_card
      (hacy.mono_set hPX) (by omega) hp
    have hsinkX : ∀ x ∈ X, ¬ D t x = true := by
      intro x hx htx
      exact hsink x (hclosed t ht x hx htx) htx
    have hsub : outN D (X ∪ Y) t ⊆ Y := by
      intro v hv
      obtain ⟨hvXY, htv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hsinkX v hvX htv).elim
      · exact hvY
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [hY]
      exact h.high_first t (hPX ht))
    refine ⟨t, ht, ?_, m, by omega, w⟩
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have hnoYP : ∀ y ∈ Y, ∀ p ∈ P, ¬ D y p = true := by
    intro y hy p hp hyp
    obtain ⟨t, ht, hall, m, hm, w⟩ := hexit p hp
    exact hf y (m + 1 + 1) (by omega) (by omega)
      ((Walk.step (hPU hp) hyp (w.mono hPU)).snoc (hYU hy) (hall y hy))
  have hnoZP : ∀ z ∈ Z, ∀ p ∈ P, ¬ D z p = true := by
    intro z hz p hp hzp
    obtain ⟨y, hy, hyz⟩ := h.parents z hz
    obtain ⟨t, ht, hall, m, hm, w⟩ := hexit p hp
    exact hf z (m + 1 + 1 + 1) (by omega) (by omega)
      (((Walk.step (hPU hp) hzp (w.mono hPU)).snoc (hYU hy) (hall y hy)).snoc (hZU hz) hyz)
  let K := X \ P
  let W := K ∪ Y ∪ Z
  have hKX : K ⊆ X := Finset.sdiff_subset
  have hKc : K.card = 3 := by
    change (X \ P).card = 3
    rw [Finset.card_sdiff_of_subset hPX, hX, hPc]
    omega
  have hWU : W ⊆ X ∪ Y ∪ Z :=
    Finset.union_subset_union (Finset.union_subset_union_left hKX) (Finset.Subset.refl _)
  have hYW : Y ⊆ W := Finset.subset_union_right.trans Finset.subset_union_left
  have hZW : Z ⊆ W := Finset.subset_union_right
  have hhighY : ∀ y ∈ Y, s ≤ (outN D W y).card := by
    intro y hy
    apply (h.high_second y hy).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvU, hyv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, hyv⟩
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hvX, fun hvP => hnoYP y hy v hvP hyv⟩))
      · exact hYW hvY
    · exact hZW hvZ
  have hlowZ : ∀ z ∈ Z, 3 ≤ (outN D W z).card := by
    intro z hz
    apply (h.low_third z hz).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvU, hzv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, hzv⟩
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hvX, fun hvP => hnoZP z hz v hvP hzv⟩))
      · exact hYW hvY
    · exact hZW hvZ
  have hlowK : ∀ x ∈ K, 3 ≤ (outN D W x).card := by
    intro x hx
    have hsub : outN D (X ∪ Y) x ⊆ outN D W x ∪ P := by
      intro v hv
      obtain ⟨hvXY, hxv⟩ := mem_outN.mp hv
      by_cases hvP : v ∈ P
      · exact Finset.mem_union_right _ hvP
      · refine Finset.mem_union_left _ (mem_outN.mpr ⟨?_, hxv⟩)
        rcases Finset.mem_union.mp hvXY with hvX | hvY
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨hvX, hvP⟩))
        · exact hYW hvY
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := h.high_first x (hKX hx)
    omega
  have hmin : ∀ v ∈ W, 3 ≤ (outN D W v).card := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvKY | hvZ
    · rcases Finset.mem_union.mp hvKY with hvK | hvY
      · exact hlowK v hvK
      · exact (by omega : 3 ≤ s).trans (hhighY v hvY)
    · exact hlowZ v hvZ
  have hWc : W.card ≤ 2 * s + 5 := by
    have h1 := Finset.card_union_le K Y
    have h2 := Finset.card_union_le (K ∪ Y) Z
    change (K ∪ Y ∪ Z).card ≤ 2 * s + 5
    omega
  exact three_core_high_rows_false hs (hf.mono_set hWU) hWc hmin hYW hY hhighY

end LeanCH.BR.BRsGen
