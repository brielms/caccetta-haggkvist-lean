import LeanCH.BR.BRPrefixRetention

/-! A small acyclic low set has at least as many exiting rows as the ambient minimum degree. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem small_low_exit_count {D : CH.Digraph} {V H : Finset ℕ} {q d : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hlo : d ≤ (V \ H).card) (hsmall : (V \ H).card ≤ q) :
    d ≤ ((V \ H).filter (fun v => (outN D H v).Nonempty)).card := by
  classical
  let L := V \ H
  let K := L.filter (fun v => (outN D H v).Nonempty)
  let R := L \ K
  have hKL : K ⊆ L := Finset.filter_subset _ _
  have hRL : R ⊆ L := Finset.sdiff_subset
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hRV := hRL.trans hLV
  have hRc : R.card + K.card = L.card := Finset.card_sdiff_add_card_eq_card hKL
  change d ≤ L.card at hlo
  change L.card ≤ q at hsmall
  change d ≤ K.card
  by_contra hn
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
  have hminR : ∀ v ∈ R, 1 ≤ (outN D R v).card := by
    intro v hv
    have hvL := hRL hv
    have hvK := (Finset.mem_sdiff.mp hv).2
    have hsub : outN D V v ⊆ outN D R v ∪ K := by
      intro w hw
      obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
      by_cases hwK : w ∈ K
      · exact Finset.mem_union_right _ hwK
      · have hwL : w ∈ L := Finset.mem_sdiff.mpr ⟨hwV, fun hwH =>
          hvK (Finset.mem_filter.mpr ⟨hvL, w, mem_outN.mpr ⟨hwH, hvw⟩⟩)⟩
        exact Finset.mem_union_left _ (mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨hwL, hwK⟩, hvw⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin v (hRV hv)
    omega
  obtain ⟨v, hv, hsink⟩ := exists_sink (hf.mono_set hRV) hRne (by omega)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (hminR v hv)
  exact hsink w (mem_outN.mp hw).1 (mem_outN.mp hw).2

end LeanCH.BR.BRsGen
