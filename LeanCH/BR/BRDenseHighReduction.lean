import LeanCH.BR.BRHighGrowthTargets
import LeanCH.BR.BRHighPairDensity
import LeanCH.BR.BRsubSixThree

/-! Conditional consequences of the corrected dense-high growth target.
DenseHighGrowth remains an explicit, unproved hypothesis. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem nineteen_core_false_of_dense_growth (hgrowth : DenseHighGrowth)
    {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 19) (hH : H.card = 14) : False := by
  classical
  have hcount := Finset.card_sdiff_add_card_eq_card hHV
  have hhighcap : ∀ v ∈ H, (inN D V v).card ≤ 3 := by
    intro v hv
    have hb := hgrowth D V H 5 (by decide) hf hmin hHV hhigh (by omega) v hv
    have hi := incoming_add_ball_le hf (hHV hv) (by decide : 4 + 1 ≤ 5)
    omega
  have hlowcap : ∀ v ∈ V \ H, (inN D V v).card ≤ 10 := by
    intro v hv
    have hb := ball_growth 5 (by decide) D V hf hmin v (Finset.mem_sdiff.mp hv).1
      4 (by decide)
    have hi := incoming_add_ball_le hf (Finset.mem_sdiff.mp hv).1
      (by decide : 4 + 1 ≤ 5)
    omega
  have hiH := Finset.sum_le_sum hhighcap
  have hiL := Finset.sum_le_sum hlowcap
  have hoH := Finset.sum_le_sum hhigh
  have hoL := Finset.sum_le_sum (s := V \ H)
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1)
  simp only [Finset.sum_const_nat (fun _ _ => rfl)] at hiH hiL hoH hoL
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  omega

end LeanCH.BR.BRsGen

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

theorem no_eight_six_of_dense_growth (hgrowth : DenseHighGrowth)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24) (h1 : (outN D V u).card = 8)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 6) : False := by
  classical
  obtain ⟨h3, h4, hB4⟩ := eight_six_deficient_profile hf hu hmin hb4 h1 h2
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hUc : U.card = (ball D V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hU19 : U.card = 19 := by omega
  have hH14 : H.card = 14 := by omega
  have hminU : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by rw [h4])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  exact nineteen_core_false_of_dense_growth hgrowth (hf.mono_set hUV) hminU hHU hhigh hU19 hH14

end LeanCH.BR.BRsub
