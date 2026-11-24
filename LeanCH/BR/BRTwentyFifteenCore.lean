import LeanCH.BR.BRHighHighProfile
import LeanCH.BR.BRFiveCreditCore
import LeanCH.BR.BRSmallHighSet

/-! The 20-vertex minimum-three core with fifteen degree-six rows is impossible. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem three_core_twenty_fifteen_false {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 20) (hH : H.card = 15) : False := by
  classical
  let L := V \ H
  have hLc : L.card = 5 := by
    have hc := Finset.card_sdiff_add_card_eq_card hHV
    change L.card + H.card = V.card at hc
    omega
  have hbudget := three_core_low_incoming_budget_five hf hmin hHV hhigh
    (by change 3 ≤ L.card; omega) (by change L.card ≤ 5; omega)
  change (∑ v ∈ L, (inN D V v).card) + 13 * L.card + 5 ≤ L.card * V.card at hbudget
  have hout := (three_core_twenty_fifteen_degrees hf hmin hHV hhigh hV hH).1
  have hball := three_core_twenty_fifteen_incoming hf hmin hHV hhigh hV hH
  have hlowheads : ∀ u ∈ H, 3 ≤ (outN D L u).card := by
    intro u hu
    have hdegree := hout u hu
    have hex : ∃ v ∈ outN D V u, v ∈ H := by
      by_contra hn
      have hsub : outN D V u ⊆ L := by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨(mem_outN.mp hv).1, fun hvH => hn ⟨v, hv, hvH⟩⟩
      have hc := Finset.card_le_card hsub
      omega
    obtain ⟨v, hv, hvH⟩ := hex
    have hsecond := (high_high_small_four_profile hf hmin (hHV hu) hdegree hv
      (hhigh v hvH) (by have := (hball u hu).2; omega)).1
    have hhighcap := small_first_high_heads_bound (d := 3) (s := 6)
      (by decide : 2 ≤ 5) (by decide) hf (hHV hu) (by omega) hHV hhigh (by omega)
    have hsplit := card_outN_union (D := D) (show Disjoint H L from Finset.disjoint_sdiff) u
    rw [show H ∪ L = V from Finset.union_sdiff_of_subset hHV] at hsplit
    omega
  have hsum := Finset.sum_le_sum hlowheads
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have he := dcount H L (fun u v => D u v = true)
  change (∑ u ∈ H, (outN D L u).card) = ∑ v ∈ L, (inN D H v).card at he
  have hsumIn : (∑ v ∈ L, (inN D H v).card) ≤ ∑ v ∈ L, (inN D V v).card :=
    Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset_filter _ hHV))
  rw [hV, hLc] at hbudget
  omega

end LeanCH.BR.BRsGen
