import LeanCH.BR.BRsubSixThree
import LeanCH.BR.BRHighPairDensity

/-! The uniform high-pair gain inside the actual (8,6) capstone core. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

theorem eight_six_core_high_balls {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24) (h1 : (outN D V u).card = 8)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 6) :
    let U := (ball D V u 3).erase u
    let H := (ball D V u 2).erase u
    ∀ v ∈ H, 13 ≤ (ball D U v 4).card ∧ (inN D U v).card ≤ 6 := by
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
  have hcount := Finset.card_sdiff_add_card_eq_card hHU
  have hballs := two_core_dense_high_balls (by decide : 5 ≤ 5) (hf.mono_set hUV)
    hminU hHU hhigh (by omega)
  change ∀ v ∈ H, 13 ≤ (ball D U v 4).card ∧ (inN D U v).card ≤ 6
  intro v hv
  have hb := hballs v hv
  have hi := incoming_add_ball_le (hf.mono_set hUV) (hHU hv) (by decide : 4 + 1 ≤ 5)
  change 13 ≤ (ball D U v 4).card ∧ (inN D U v).card ≤ 6
  omega

end LeanCH.BR.BRsub
