import LeanCH.BR.BRq5All
import LeanCH.BR.BRTightChain

/-! Lower-degree inputs and the first degree-six seeds below the uniform window. -/

namespace LeanCH.BR.BRq6
open BRq2 BRq3 BRq4 BR45 BRsGen

theorem lower_order {q d : ℕ} (hq : 5 ≤ q) (hd : 2 ≤ d) (hd6 : d < 6)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, d ≤ (outN D V v).card) (hn : V.Nonempty) : q * d + 1 ≤ V.card := by
  rcases (by omega : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5) with rfl | rfl | rfl | rfl
  · simpa only [Nat.mul_comm q 2] using corB (by omega) hf hm hn
  · exact dt_size (by omega) (ball_all q (by omega)) hf hm hn
  · exact dt_size (by omega) (ball_all4 q (by omega)) hf hm hn
  · exact BRq5.card_ge_five_mul hq hf hm hn

theorem card_ball_three_seven_free {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    19 ≤ (ball D V u 3).card :=
  third_ball_ge_of_lower_orders (by decide : 4 ≤ 6) (by decide : 6 + 1 ≤ 7)
    (fun _ hd hd6 _ _ hF hmF hn => lower_order (by decide) hd hd6 hF hmF hn) hf hm hu

theorem third_layer_of_cap {q : ℕ} (hq : 7 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V)
    (hcap : (ball D V u 3).card ≤ 19) :
    6 ≤ (ball D V u 3 \ ball D V u 2).card :=
  third_layer_ge_of_third_cap_and_lower_orders (by decide : 4 ≤ 6) hq
    (fun _ hd hd6 _ _ hF hmF hn => lower_order (by omega) hd hd6 hF hmF hn) hf hm hu hcap

theorem card_ball_four_eight_free {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 8) (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    25 ≤ (ball D V u 4).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hmin
  have hF := qfree_sub hsub hf
  suffices hh : 25 ≤ (ball F V u 4).card from hh.trans (Finset.card_le_card (ball_sub hsub))
  classical
  have hm : ∀ v ∈ V, 6 ≤ (outN F V v).card := fun v hv => (ho v hv).ge
  by_contra hn
  have hfour : (ball F V u 4).card ≤ 24 := by omega
  have hthree := card_ball_three_seven_free (hF.mono_bound (by decide)) hm hu
  have htwo := card_ball_two_ge_twice (by decide : 2 ≤ 6) (hF.mono_bound (by decide)) hm hu
  let t := (ball F V u 4 \ ball F V u 3).card
  have ht : t + (ball F V u 3).card = (ball F V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have ht5 : t ≤ 5 := by omega
  let U := (ball F V u 3).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hUc : U.card = (ball F V u 3).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  by_cases ht3 : t ≤ 3
  · have hmU : ∀ v ∈ U, 3 ≤ (outN F U v).card :=
      minOut_prefix_erase hF hu (by decide : 3 + 1 ≤ 8) hm (by change 3 + t ≤ 6; omega)
    have hh := lower_order (by decide : 5 ≤ 8) (by decide : 2 ≤ 3) (by decide)
      (hF.mono_set hUV) hmU hUne
    omega
  by_cases ht4 : t = 4
  · let H := (ball F V u 2).erase u
    have hHU : H ⊆ U := Finset.erase_subset_erase _ (ball_mono_radius (by decide))
    have hHc : 12 ≤ H.card := by
      have he := Finset.card_erase_of_mem (self_mem_ball (D := F) (k := 2) hu)
      change H.card = _ at he
      omega
    have hmU : ∀ v ∈ U, 2 ≤ (outN F U v).card :=
      minOut_prefix_erase hF hu (by decide : 3 + 1 ≤ 8) hm (by change 2 + t ≤ 6; omega)
    have hhigh : ∀ v ∈ H, 6 ≤ (outN F U v).card := by
      intro v hv
      exact (hm v (hUV (hHU hv))).trans (Finset.card_le_card
        (outN_prefix_erase_root hF hu (by decide : 2 + 1 ≤ 8) (Finset.mem_of_mem_erase hv)))
    have hb2 : Ball 8 2 := by
      intro G W hG hOut w hw
      exact ball_growth 8 (by decide) G W hG (fun v hv => (hOut v hv).ge) w hw 7 (by decide)
    have hd := mixed_degree_density_of_ball (by decide : 1 ≤ 8) hb2 (hF.mono_set hUV) hmU hHU hhigh
    rcases (by omega : U.card = 18 ∨ U.card = 19) with hN | hN <;> rw [hN] at hd <;> omega
  have hteq : t = 5 := by omega
  have hc := third_layer_of_cap (by decide : 7 ≤ 8) hF hm hu (by omega)
  have he3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := V) (u := u) (by decide : 2 ≤ 3))
  have hthird : (ball F V u 3 \ ball F V u 2).card = 6 := by omega
  have hfirst : (ball F V u 1).card = 7 := by
    rw [card_B1 (hF.mono_bound (by decide)) hu, ho u hu]
  have he2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := V) (u := u) (by decide : 1 ≤ 2))
  have hsecond : (ball F V u 2 \ ball F V u 1).card = 6 := by omega
  have hh := fourth_layer_of_two_tight_layers (by decide : 2 ≤ 6) hF ho hu hsecond hthird
  change 6 ≤ t at hh
  omega

theorem card_ball_four_seven_free_ge_twenty_three {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    23 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  have hthree := card_ball_three_seven_free hf hm hu
  have he := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  let U := (ball D V u 3).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hUc : U.card = (ball D V u 3).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hmU : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 7) hm
      (by change 3 + (ball D V u 4 \ ball D V u 3).card ≤ 6; omega)
  have hh := lower_order (by decide : 5 ≤ 7) (by decide : 2 ≤ 3) (by decide)
    (hf.mono_set hUV) hmU hne
  omega

end LeanCH.BR.BRq6
