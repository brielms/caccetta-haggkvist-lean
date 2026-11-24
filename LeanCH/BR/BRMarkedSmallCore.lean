import LeanCH.BR.BRDegreeTwoStrictGrowth
import LeanCH.BR.BRStrictPrefixDeficiency

/-! A forced copy of a marked row makes the degree-two completion too dense. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem marked_small_one_core_false {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hH : q + 1 ≤ H.card)
    (hhigh : ∀ v ∈ H, 3 ≤ (outN D V v).card)
    (hV : V.card ≤ 2 * q) (hbudget : V.card + (V \ H).card ≤ 2 * q + 2) : False := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hneH : H.Nonempty := Finset.card_pos.mp (by omega)
  have hneV := hneH.mono hHV
  have hb : Ball q 2 := by
    intro F U hf hout u hu
    exact ball_growth q (by omega) F U hf (fun v hv => (hout v hv).ge) u hu (q - 1) (by omega)
  have hstrict := deficiency_strict_of_order_le (by omega : 1 ≤ q) hb hf hmin hneV (by omega)
  have hz : (∑ v ∈ H, (2 - (outN D V v).card)) = 0 :=
    Finset.sum_eq_zero (fun v hv => by have := hhigh v hv; omega)
  have hlo : ∀ v ∈ L, 2 - (outN D V v).card ≤ 1 := by
    intro v hv
    have := hmin v (hLV hv)
    omega
  have hsum := Finset.sum_le_sum hlo
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have hsplit := Finset.sum_sdiff hHV (f := fun v => 2 - (outN D V v).card)
  change (∑ v ∈ L, (2 - (outN D V v).card)) + _ = _ at hsplit
  have hLc := Finset.card_sdiff_add_card_eq_card hHV
  change L.card + H.card = V.card at hLc
  change V.card + L.card ≤ 2 * q + 2 at hbudget
  have hcost : V.card + (∑ v ∈ V, (2 - (outN D V v).card)) = 2 * q + 2 := by omega
  have heq : (∑ v ∈ L, (2 - (outN D V v).card)) = ∑ _v ∈ L, 1 := by
    rw [Finset.sum_const_nat (fun _ _ => rfl)]
    omega
  have hone : ∀ v ∈ L, (outN D V v).card = 1 := by
    have hh := (Finset.sum_eq_sum_iff_of_le hlo).mp heq
    intro v hv
    have ha := hh v hv
    omega
  have hLpos : 0 < L.card := by omega
  have hLsmall : L.card ≤ q := by omega
  obtain ⟨z, hz, hsink⟩ := exists_sink (hf.mono_set hLV)
    (Finset.card_pos.mp hLpos) hLsmall
  have hheads : outN D V z ⊆ H := by
    intro w hw
    by_contra hn
    exact hsink w (Finset.mem_sdiff.mpr ⟨(mem_outN.mp hw).1, hn⟩) (mem_outN.mp hw).2
  obtain ⟨F, U, hF, hminF, hc, _, _, _, hmarked⟩ :=
    exists_deficiency_completion_marked (d := 2) hf hmin
  obtain ⟨J, hJU, hJ, hhighJ, hmore⟩ := hmarked H 3 hHV hhigh
  have hgain := hmore ⟨z, hLV hz, by rw [hone z hz]; decide, hheads⟩
  have hUc : U.card = 2 * q + 2 := hc.trans hcost
  have hd := two_core_three_density hq hF hminF hJU hhighJ
  rw [hUc] at hd
  nlinarith

end LeanCH.BR.BRsGen
