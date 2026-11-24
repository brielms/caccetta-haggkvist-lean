import LeanCH.BR.BRsubFiveThree
import LeanCH.BR.BRTwoExitCore

/-! The two-exit core bound excludes the deficient `(8,7)` first pair. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

theorem no_eight_seven_deficient {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hb4 : (ball D V u 4).card ≤ 24)
    (h1 : (outN D V u).card = 8)
    (h2 : (ball D V u 2 \ ball D V u 1).card = 7) : False := by
  classical
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have h3 := third_layer_ge_four hf hu hmin hb4
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  have h4large : 4 ≤ (ball D V u 4 \ ball D V u 3).card := by
    by_contra hn
    have hh := fourth_three_third_ge_six hf hu hmin hb4 (by omega)
    omega
  have h3eq : (ball D V u 3 \ ball D V u 2).card = 4 := by omega
  let U := (ball D V u 2).erase u
  let H := outN D V u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have hU15 : U.card = 15 := by
    have he : U.card = (ball D V u 2).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    omega
  have hH8 : H.card = 8 := h1
  have hminU : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin (by rw [h3eq])
  have hhighH : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (outN_subset hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
        ((mem_ball_one hu).mpr (Or.inr hv))))
  exact two_core_fifteen_eight_false (hf.mono_set hUV) hminU hHU hhighH hU15 hH8

end LeanCH.BR.BRsub
