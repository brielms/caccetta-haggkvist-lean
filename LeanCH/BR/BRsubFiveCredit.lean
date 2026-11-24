import LeanCH.BR.BRFiveCreditCore

/-! Exact retained-core degrees at the remaining (third,fourth)=(5,3) tail. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

theorem five_three_core_rigid {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hB : (ball D V u 4).card = 24)
    (h3 : (ball D V u 3 \ ball D V u 2).card = 5)
    (h4 : (ball D V u 4 \ ball D V u 3).card = 3) :
    let U := (ball D V u 3).erase u
    let H := (ball D V u 2).erase u
    (∀ v ∈ H, (outN D U v).card = 6 ∧ (inN D U v).card = 5 ∧
      (ball D U v 4).card = 15) ∧
    (∀ v ∈ U \ H, (outN D U v).card = 3) := by
  classical
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hUc : U.card = 20 := by
    have he : U.card = (ball D V u 3).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    omega
  have hHc : H.card = 15 := by
    have he : H.card = (ball D V u 2).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    omega
  have hminU : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin (by rw [h4])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_of_mem_erase hv)))
  have hout := three_core_twenty_fifteen_degrees (hf.mono_set hUV) hminU hHU hhigh hUc hHc
  have hin := three_core_twenty_fifteen_incoming (hf.mono_set hUV) hminU hHU hhigh hUc hHc
  exact ⟨fun v hv => ⟨hout.1 v hv, hin v hv⟩, hout.2⟩

end LeanCH.BR.BRsub
