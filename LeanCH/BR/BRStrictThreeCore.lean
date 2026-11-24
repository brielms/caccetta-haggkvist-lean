import LeanCH.BR.BRHighPredecessorGrowth
import LeanCH.BR.BRHighThreeGrowth

/-! A small nonempty low set makes the minimum-three mixed-core inequality strict. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem three_core_six_density_strict {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hne : (V \ H).Nonempty) (hsmall : (V \ H).card ≤ 5) :
    16 * V.card + 5 * H.card + 1 ≤ V.card * V.card := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  obtain ⟨z, hz, hsink⟩ := exists_sink (hf.mono_set hLV) hne hsmall
  have hzV := hLV hz
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by have := hmin z hzV; omega : 0 < (outN D V z).card)
  have hwH : w ∈ H := by
    by_contra hn
    exact hsink w (Finset.mem_sdiff.mpr ⟨(mem_outN.mp hw).1, hn⟩) (mem_outN.mp hw).2
  have hcap : ∀ v ∈ V, (inN D V v).card + 13 ≤ V.card := by
    intro v hv
    have hb := ball_of_min (BRq3.ball_all 5 (by decide)) hf hmin v hv
    have hi := incoming_add_ball_le hf hv (by decide : 4 + 1 ≤ 5)
    change 13 ≤ (ball D V v 4).card at hb
    omega
  have hcapH : ∀ v ∈ H, (inN D V v).card + 15 ≤ V.card := by
    intro v hv
    have hb := high_three_ball_four_ge_fifteen hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by decide : 4 + 1 ≤ 5)
    omega
  have hzstrict : (inN D V z).card + 17 ≤ V.card + (outN D V z).card := by
    by_cases hz3 : (outN D V z).card = 3
    · have hb := high_predecessor_ball_four hf hmin hzV hw hz3 (hhigh w hwH)
      have hi := incoming_add_ball_le hf hzV (by decide : 4 + 1 ≤ 5)
      omega
    · have hi := hcap z hzV
      have ho := hmin z hzV
      omega
  have hgapH : ∀ v ∈ H, (inN D V v).card + 21 ≤ V.card + (outN D V v).card := by
    intro v hv
    have hi := hcapH v hv
    have ho := hhigh v hv
    omega
  have hgapL : ∀ v ∈ L.erase z,
      (inN D V v).card + 16 ≤ V.card + (outN D V v).card := by
    intro v hv
    have hvV := hLV (Finset.mem_of_mem_erase hv)
    have hi := hcap v hvV
    have ho := hmin v hvV
    omega
  have hsH := Finset.sum_le_sum hgapH
  have hsL := Finset.sum_le_sum hgapL
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsL
  have hiZ := Finset.sum_erase_add L (fun v => (inN D V v).card) hz
  have hoZ := Finset.sum_erase_add L (fun v => (outN D V v).card) hz
  have hcZ := Finset.card_erase_of_mem hz
  have hLpos : 0 < L.card := Finset.card_pos.mpr ⟨z, hz⟩
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  change L.card + H.card = V.card at hc
  change (∑ v ∈ L, (outN D V v).card) + _ = _ at ho
  change (∑ v ∈ L, (inN D V v).card) + _ = _ at hi
  have hcZ' : (L.erase z).card + 1 = L.card := by omega
  nlinarith

end LeanCH.BR.BRsGen
