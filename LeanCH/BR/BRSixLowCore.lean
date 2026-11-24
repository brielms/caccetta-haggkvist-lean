import LeanCH.BR.BRSmallBallLowHeads
import LeanCH.BR.BRTwoHighPredecessorGrowth

/-! The weighted low-set penalty rules out the 20/14 minimum-three core. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem three_core_low_credit_budget {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card) :
    (∑ v ∈ V \ H, (inN D V v).card) + 13 * (V \ H).card +
      (∑ v ∈ V \ H, lowExitCredit (outN D (V \ H) v).card) ≤
      (V \ H).card * V.card := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hpoint : ∀ v ∈ L, (inN D V v).card + 13 +
      lowExitCredit (outN D L v).card ≤ V.card := by
    intro v hv
    have hi := incoming_add_ball_le hf (hLV hv) (by decide : 4 + 1 ≤ 5)
    have hsplit := card_outN_union (D := D) (show Disjoint H L from Finset.disjoint_sdiff) v
    rw [show H ∪ L = V from Finset.union_sdiff_of_subset hHV] at hsplit
    have hd := hmin v (hLV hv)
    by_cases htwo : (outN D L v).card ≤ 1
    · have hb := two_high_predecessor_ball_four_min hf hmin (hLV hv)
        (outN_mono hHV v) (by omega : 2 ≤ (outN D H v).card)
        (fun x hx => hhigh x (mem_outN.mp hx).1)
      unfold lowExitCredit
      omega
    · by_cases hone : (outN D L v).card = 2
      · obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (outN D H v).card)
        have hb := high_predecessor_ball_four_min hf hmin (hLV hv)
          (outN_mono hHV v hx) (hhigh x (mem_outN.mp hx).1)
        unfold lowExitCredit
        omega
      · have hb := ball_of_min (BRq3.ball_all 5 (by decide)) hf hmin v (hLV hv)
        change 13 ≤ (ball D V v 4).card at hb
        unfold lowExitCredit
        omega
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hs
  change (∑ v ∈ L, (inN D V v).card) + 13 * L.card +
    (∑ v ∈ L, lowExitCredit (outN D L v).card) ≤ L.card * V.card
  nlinarith

theorem three_core_high_large_ball_budget {D : CH.Digraph} {V H B : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hBH : B ⊆ H) (hbig : ∀ v ∈ B, 16 ≤ (ball D V v 4).card) :
    (∑ v ∈ H, (inN D V v).card) + 15 * H.card + B.card ≤ H.card * V.card := by
  have hcapH : ∀ v ∈ H \ B, (inN D V v).card + 15 ≤ V.card := by
    intro v hv
    have hvH := (Finset.mem_sdiff.mp hv).1
    have hb := high_three_ball_four_ge_fifteen hf hmin (hHV hvH) (hhigh v hvH)
    have hi := incoming_add_ball_le hf (hHV hvH) (by decide : 4 + 1 ≤ 5)
    omega
  have hcapB : ∀ v ∈ B, (inN D V v).card + 16 ≤ V.card := by
    intro v hv
    have hb := hbig v hv
    have hi := incoming_add_ball_le hf (hHV (hBH hv)) (by decide : 4 + 1 ≤ 5)
    omega
  have hsH := Finset.sum_le_sum hcapH
  have hsB := Finset.sum_le_sum hcapB
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsB
  have hi := Finset.sum_sdiff hBH (f := fun v => (inN D V v).card)
  have hc := Finset.card_sdiff_add_card_eq_card hBH
  nlinarith

theorem three_core_twenty_fourteen_false {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 20) (hH : H.card = 14) : False := by
  classical
  let L := V \ H
  let B := H.filter (fun v => 16 ≤ (ball D V v 4).card)
  let C := ∑ v ∈ L, lowExitCredit (outN D L v).card
  let E := ∑ v ∈ L, (outN D L v).card
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hLc : L.card = 6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hHV
    change L.card + H.card = V.card at hc
    omega
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hbig : ∀ v ∈ B, 16 ≤ (ball D V v 4).card :=
    fun _ hv => (Finset.mem_filter.mp hv).2
  have hlow := three_core_low_credit_budget hf hmin hHV hhigh
  change (∑ v ∈ L, (inN D V v).card) + 13 * L.card + C ≤ L.card * V.card at hlow
  rw [hV, hLc] at hlow
  have hlarge := three_core_high_large_ball_budget hf hmin hHV hhigh hBH hbig
  rw [hV, hH] at hlarge
  have hcost : B.card + C ≤ 10 := by
    have hsH := Finset.sum_le_sum hhigh
    have hsL := Finset.sum_le_sum (s := L) (fun v hv => hmin v (hLV hv))
    simp only [Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsL
    have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
    have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
    change (∑ v ∈ L, (inN D V v).card) + _ = _ at hi
    change (∑ v ∈ L, (outN D V v).card) + _ = _ at ho
    have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
      Compose.ThinRigid.sum_out_eq_sum_in D V
    rw [hH] at hsH
    rw [hLc] at hsL
    omega
  have hgood : ∀ u ∈ H \ B, 3 ≤ (outN D L u).card := by
    intro u hu
    obtain ⟨huH, huB⟩ := Finset.mem_sdiff.mp hu
    have hsmall : (ball D V u 4).card ≤ 15 := by
      have hn : ¬ 16 ≤ (ball D V u 4).card :=
        fun hh => huB (Finset.mem_filter.mpr ⟨huH, hh⟩)
      omega
    exact high_small_ball_low_heads hf hmin hHV hhigh (hHV huH) (hhigh u huH) hsmall
  have hsum := Finset.sum_le_sum hgood
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have hcross : E + C ≤ 3 * B.card := by
    have hc := Finset.card_sdiff_add_card_eq_card hBH
    have hsG := Finset.sum_sdiff hBH (f := fun v => (outN D L v).card)
    have hsL := Finset.sum_sdiff hHV (f := fun v => (outN D L v).card)
    change E + (∑ v ∈ H, (outN D L v).card) = _ at hsL
    have he := dcount V L (fun u v => D u v = true)
    change (∑ u ∈ V, (outN D L u).card) = ∑ v ∈ L, (inN D V v).card at he
    rw [hH] at hc
    omega
  have hpenalty := near_boundary_low_row_penalty (by decide : 2 ≤ 5)
    (hf.mono_set hLV) (by omega : 3 ≤ L.card) (by omega : L.card ≤ 5 + 1)
  change 3 * L.card + 13 ≤ E + 4 * C at hpenalty
  rw [hLc] at hpenalty
  omega

/-- The next 19/14 minimum-two core would need at least two degree-two rows. -/
theorem two_core_nineteen_fourteen_two_low_rows {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 19) (hH : H.card = 14) :
    2 ≤ (V.filter (fun v => (outN D V v).card = 2)).card := by
  classical
  have hdef : 2 ≤ ∑ v ∈ V, (3 - (outN D V v).card) := by
    by_contra hn
    obtain ⟨F, U, hF, hminF, hc, _, _, _, hmarked⟩ :=
      exists_deficiency_completion_marked (d := 3) hf (fun v hv => (by
        have hh := hmin v hv
        omega : 1 ≤ (outN D V v).card))
    obtain ⟨J, hJU, hJ, hhighJ, _⟩ := hmarked H 6 hHV hhigh
    have hJge : 14 ≤ J.card := by omega
    obtain ⟨K, hKJ, hKc⟩ := Finset.exists_subset_card_eq hJge
    have hKU : K ⊆ U := hKJ.trans hJU
    have hhighK : ∀ v ∈ K, 6 ≤ (outN F U v).card := fun v hv => hhighJ v (hKJ hv)
    have hcases : U.card = 19 ∨ U.card = 20 := by omega
    rcases hcases with h19 | h20
    · have hd := three_core_six_density hF hminF hKU hhighK
      rw [h19, hKc] at hd
      omega
    · exact three_core_twenty_fourteen_false hF hminF hKU hhighK h20 hKc
  have he : (∑ v ∈ V, (3 - (outN D V v).card)) =
      (V.filter (fun v => (outN D V v).card = 2)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v hv
    have hh := hmin v hv
    by_cases ht : (outN D V v).card = 2
    · simp [ht]
    · simp only [if_neg ht]
      omega
  omega

end LeanCH.BR.BRsGen
