import LeanCH.BR.BRTwoHighPredecessorGrowth
import LeanCH.BR.BRHighThreeGrowth

/-! Three successive sinks of a small low set supply five incoming exclusions. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem three_core_low_incoming_budget_five {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hlo : 3 ≤ (V \ H).card) (hsmall : (V \ H).card ≤ 5) :
    (∑ v ∈ V \ H, (inN D V v).card) + 13 * (V \ H).card + 5 ≤
      (V \ H).card * V.card := by
  classical
  let L := V \ H
  change 3 ≤ L.card at hlo
  change L.card ≤ 5 at hsmall
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hcap : ∀ v ∈ V, (inN D V v).card + 13 ≤ V.card := by
    intro v hv
    have hb := ball_of_min (BRq3.ball_all 5 (by decide)) hf hmin v hv
    have hi := incoming_add_ball_le hf hv (by decide : 4 + 1 ≤ 5)
    change 13 ≤ (ball D V v 4).card at hb
    omega
  have hcount : ∀ (R : Finset ℕ), R ⊆ L → ∀ v ∈ R,
      (∀ w ∈ R, ¬ D v w = true) → 3 ≤ (outN D H v).card + (L \ R).card := by
    intro R hRL v hv hsink
    have hsub : outN D V v ⊆ outN D H v ∪ (L \ R) := by
      intro w hw
      obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
      by_cases hwH : w ∈ H
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hwH, hvw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hwV, hwH⟩, fun hwR => hsink w hwR hvw⟩)
    exact (hmin v (hLV (hRL hv))).trans
      ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  have htwo : ∀ v ∈ L, 2 ≤ (outN D H v).card → (inN D V v).card + 15 ≤ V.card := by
    intro v hv htwo
    have hb := two_high_predecessor_ball_four_min hf hmin (hLV hv)
      (outN_mono hHV v) htwo (fun x hx => hhigh x (mem_outN.mp hx).1)
    have hi := incoming_add_ball_le hf (hLV hv) (by decide : 4 + 1 ≤ 5)
    omega
  obtain ⟨z, hz, hzs⟩ := exists_sink (hf.mono_set hLV)
    (Finset.card_pos.mp (by omega)) hsmall
  let L1 := L.erase z
  have hL1L : L1 ⊆ L := Finset.erase_subset _ _
  have hL1c : L1.card = L.card - 1 := Finset.card_erase_of_mem hz
  have hLpos : 0 < L.card := Finset.card_pos.mpr ⟨z, hz⟩
  obtain ⟨y, hy, hys⟩ := exists_sink (hf.mono_set (hL1L.trans hLV))
    (Finset.card_pos.mp (by omega)) (by omega)
  let L2 := L1.erase y
  have hL2L1 : L2 ⊆ L1 := Finset.erase_subset _ _
  have hL2c : L2.card = L1.card - 1 := Finset.card_erase_of_mem hy
  have hL1pos : 0 < L1.card := Finset.card_pos.mpr ⟨y, hy⟩
  obtain ⟨x, hx, hxs⟩ := exists_sink (hf.mono_set (hL2L1.trans (hL1L.trans hLV)))
    (Finset.card_pos.mp (by omega)) (by omega)
  have hL2pos : 0 < L2.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hzcap : (inN D V z).card + 15 ≤ V.card := by
    apply htwo z hz
    have hh := hcount L (fun _ h => h) z hz hzs
    simp only [Finset.sdiff_self, Finset.card_empty, Nat.add_zero] at hh
    omega
  have hycap : (inN D V y).card + 15 ≤ V.card := by
    apply htwo y (hL1L hy)
    have hh := hcount L1 hL1L y hy hys
    have hc := Finset.card_sdiff_add_card_eq_card hL1L
    omega
  have hxcap : (inN D V x).card + 14 ≤ V.card := by
    have hh := hcount L2 (hL2L1.trans hL1L) x hx hxs
    have hc := Finset.card_sdiff_add_card_eq_card (hL2L1.trans hL1L)
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (outN D H x).card)
    have hb := high_predecessor_ball_four_min hf hmin (hLV (hL1L (hL2L1 hx)))
      (outN_mono hHV x hw) (hhigh w (mem_outN.mp hw).1)
    have hi := incoming_add_ball_le hf (hLV (hL1L (hL2L1 hx))) (by decide : 4 + 1 ≤ 5)
    omega
  have hsL := Finset.sum_le_sum (s := L2.erase x)
    (fun v hv => hcap v (hLV (hL1L (hL2L1 (Finset.mem_of_mem_erase hv)))))
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsL
  have hs0 := Finset.sum_erase_add L (fun v => (inN D V v).card) hz
  have hs1 := Finset.sum_erase_add L1 (fun v => (inN D V v).card) hy
  have hs2 := Finset.sum_erase_add L2 (fun v => (inN D V v).card) hx
  change (∑ v ∈ L1, (inN D V v).card) + _ = _ at hs0
  change (∑ v ∈ L2, (inN D V v).card) + _ = _ at hs1
  have hc2 := Finset.card_erase_of_mem hx
  have hthree : (L2.erase x).card + 3 = L.card := by omega
  change (∑ v ∈ L, (inN D V v).card) + 13 * L.card + 5 ≤ L.card * V.card
  nlinarith

theorem three_core_six_incoming_budget_five {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hlo : 3 ≤ (V \ H).card) (hsmall : (V \ H).card ≤ 5) :
    (∑ v ∈ V, (inN D V v).card) + 13 * V.card + 2 * H.card + 5 ≤ V.card * V.card := by
  have hsL := three_core_low_incoming_budget_five hf hmin hHV hhigh hlo hsmall
  have hcapH : ∀ v ∈ H, (inN D V v).card + 15 ≤ V.card := by
    intro v hv
    have hb := high_three_ball_four_ge_fifteen hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by decide : 4 + 1 ≤ 5)
    omega
  have hsH := Finset.sum_le_sum hcapH
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsH
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  nlinarith

theorem three_core_six_density_five {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hlo : 3 ≤ (V \ H).card) (hsmall : (V \ H).card ≤ 5) :
    16 * V.card + 5 * H.card + 5 ≤ V.card * V.card := by
  have hi := three_core_six_incoming_budget_five hf hmin hHV hhigh hlo hsmall
  have hsH := Finset.sum_le_sum hhigh
  have hsL := Finset.sum_le_sum (s := V \ H)
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1)
  simp only [Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsL
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  nlinarith

theorem three_core_twenty_fifteen_degrees {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 20) (hH : H.card = 15) :
    (∀ v ∈ H, (outN D V v).card = 6) ∧
      (∀ v ∈ V \ H, (outN D V v).card = 3) := by
  classical
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have hi := three_core_six_incoming_budget_five hf hmin hHV hhigh (by omega) (by omega)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  let f := fun v => if v ∈ H then 6 else 3
  have hrow : ∀ v ∈ V, f v ≤ (outN D V v).card := by
    intro v hv
    by_cases hvH : v ∈ H
    · simpa [f, hvH] using hhigh v hvH
    · simpa [f, hvH] using hmin v hv
  have hsH : (∑ v ∈ H, f v) = 6 * H.card := by
    rw [Finset.sum_const_nat (fun v hv => show f v = 6 by simp [f, hv]), Nat.mul_comm]
  have hsL : (∑ v ∈ V \ H, f v) = 3 * (V \ H).card := by
    rw [Finset.sum_const_nat (fun v hv => show f v = 3 by
      simp [f, (Finset.mem_sdiff.mp hv).2]), Nat.mul_comm]
  have hsplit := Finset.sum_sdiff hHV (f := f)
  have hsum := Finset.sum_le_sum hrow
  have hsumEq : (∑ v ∈ V, f v) = ∑ v ∈ V, (outN D V v).card := by
    rw [hV, hH] at hi
    omega
  have hpoint := (Finset.sum_eq_sum_iff_of_le hrow).mp hsumEq
  constructor
  · intro v hv
    simpa [f, hv] using (hpoint v (hHV hv)).symm
  · intro v hv
    simpa [f, (Finset.mem_sdiff.mp hv).2] using (hpoint v (Finset.mem_sdiff.mp hv).1).symm

theorem three_core_twenty_fifteen_incoming {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 20) (hH : H.card = 15) :
    ∀ v ∈ H, (inN D V v).card = 5 ∧ (ball D V v 4).card = 15 := by
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have hsL := three_core_low_incoming_budget_five hf hmin hHV hhigh (by omega) (by omega)
  have hcapH : ∀ v ∈ H, (inN D V v).card ≤ 5 := by
    intro v hv
    have hb := high_three_ball_four_ge_fifteen hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by decide : 4 + 1 ≤ 5)
    omega
  have hsumH := Finset.sum_le_sum hcapH
  have hsumO := Finset.sum_le_sum hhigh
  have hsumL := Finset.sum_le_sum (s := V \ H)
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1)
  simp only [Finset.sum_const_nat (fun _ _ => rfl)] at hsumH hsumO hsumL
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hsumEq : (∑ v ∈ H, (inN D V v).card) = ∑ _v ∈ H, 5 := by
    rw [Finset.sum_const_nat (fun _ _ => rfl)]
    rw [hV] at hsL
    have hL : (V \ H).card = 5 := by omega
    rw [hL] at hsL
    omega
  have hpoint := (Finset.sum_eq_sum_iff_of_le hcapH).mp hsumEq
  intro v hv
  have hb := high_three_ball_four_ge_fifteen hf hmin (hHV hv) (hhigh v hv)
  have hcap := incoming_add_ball_le hf (hHV hv) (by decide : 4 + 1 ≤ 5)
  exact ⟨hpoint v hv, by have := hpoint v hv; omega⟩

end LeanCH.BR.BRsGen
