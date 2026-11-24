import LeanCH.BR.BRq6Seeds
import LeanCH.BR.BR76Residual
import LeanCH.BR.BR66Cycle
import LeanCH.BR.BRPrefixDeficiencyStrict
import LeanCH.BR.BRFourthBallCap
import LeanCH.BR.BRHalfBallWindow

/-! The radius-five degree-six seed and boundary regularity at (9,6). -/

namespace LeanCH.BR.BRq6
open BRq2 BRq3 BRq4 BR45 BRsGen Compose.Boundary

theorem card_ball_five_nine_free {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 9) (hmin : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    31 ≤ (ball D V u 5).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hmin
  have hF := qfree_sub hsub hf
  suffices hh : 31 ≤ (ball F V u 5).card from hh.trans (Finset.card_le_card (ball_sub hsub))
  classical
  have hm : ∀ v ∈ V, 6 ≤ (outN F V v).card := fun v hv => (ho v hv).ge
  have htwo := card_ball_two_ge_twice (by decide : 2 ≤ 6) (hF.mono_bound (by decide)) hm hu
  have hthree := card_ball_three_seven_free (hF.mono_bound (by decide)) hm hu
  have hfour := card_ball_four_eight_free (hF.mono_bound (by decide)) hm hu
  by_contra hn
  have hcap : (ball F V u 5).card ≤ 30 := by omega
  let c := (ball F V u 4 \ ball F V u 3).card
  let t := (ball F V u 5 \ ball F V u 4).card
  let N := (ball F V u 4).card - 1
  have hc : c + (ball F V u 3).card = (ball F V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have ht : t + (ball F V u 4).card = (ball F V u 5).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have htlt : t < 6 := by omega
  have hct : c + t ≤ 11 := by omega
  have hN : N + t ≤ 29 := by dsimp only [N]; omega
  have hb := prefix_deficiency_of_size
    (fun _ _ hG hmG hne => BRq5.card_ge_five_mul (by decide : 5 ≤ 9) hG hmG hne)
    (k := 3) hF hu (by decide) hm (by decide : 5 ≤ 6) htlt
  change 46 ≤ N + c * (5 + t - 6) at hb
  by_cases ht3 : t ≤ 3
  · interval_cases t <;> simp_all <;> omega
  by_cases ht4 : t = 4
  · have hstrict := prefix_deficiency_strict_of_size_regular (by decide : 1 ≤ 9)
      (fun _ _ hG hmG hne => BRq5.card_ge_five_mul (by decide : 5 ≤ 9) hG hmG hne)
      (fun G W hG hmG hW => out_regular_of_second_ball_cap (by decide : 2 ≤ 5)
        (hG.mono_bound (by decide)) hmG (BRq5.boundary_second_ball_cap (by decide : 8 ≤ 9) hG hmG hW))
      (k := 3) hF hu (by decide) hm (by decide : 5 ≤ 6) htlt
      (by change (ball F V u 4).card - 1 < 46; omega)
    change 47 ≤ N + c * (5 + t - 6) at hstrict
    simp only [ht4, Nat.reduceAdd, Nat.reduceSub] at hstrict
    omega
  have hteq : t = 5 := by omega
  have hceq : c = 6 := by
    simp only [hteq, Nat.reduceAdd, Nat.reduceSub] at hb
    omega
  have hB4 : (ball F V u 4).card = 25 := by omega
  have hB3 : (ball F V u 3).card = 19 := by omega
  have hthird := third_layer_of_cap (by decide : 7 ≤ 9) hF hm hu hB3.le
  have he3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := V) (u := u) (by decide : 2 ≤ 3))
  have hB2 : (ball F V u 2).card = 13 := by omega
  have hB1 : (ball F V u 1).card = 7 := by
    rw [card_B1 (hF.mono_bound (by decide)) hu, ho u hu]
  have hB0 : (ball F V u 0).card = 1 := by
    have hsub0 : ball F V u 0 ⊆ {u} := fun _ hv => Finset.mem_singleton.mpr (eq_of_mem_ball_zero hv)
    have hlo := Finset.card_pos.mpr (⟨u, self_mem_ball hu⟩ : (ball F V u 0).Nonempty)
    have hhi := Finset.card_le_card hsub0
    simp only [Finset.card_singleton] at hhi
    omega
  have he2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := V) (u := u) (by decide : 1 ≤ 2))
  have he1 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := V) (u := u) (by decide : 0 ≤ 1))
  have htight : ∀ i, 1 ≤ i → i ≤ 4 → (ball F V u i \ ball F V u (i - 1)).card = 6 := by
    intro i hi hi4
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceSub]; omega
  have hh := tight_layers_expand (by decide : 2 ≤ 6) (by decide : 1 ≤ 4) hF hm hu htight
  change 6 ≤ t at hh
  omega

theorem card_ge_forty_nine {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 8) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hn : V.Nonempty) :
    49 ≤ V.card := by
  have hh := card_ge_of_two_balls hf (by decide : 4 + 4 ≤ 8)
    (fun _ hv => card_ball_four_eight_free hf hm hv)
    (fun _ hv => card_ball_four_eight_free hf hm hv) hn
  omega

theorem card_ge_fifty_five {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 9) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hn : V.Nonempty) :
    55 ≤ V.card := by
  have hh := card_ge_of_two_balls hf (by decide : 4 + 5 ≤ 9)
    (fun _ hv => card_ball_four_eight_free (hf.mono_bound (by decide)) hm hv)
    (fun _ hv => card_ball_five_nine_free hf hm hv) hn
  omega

theorem ch_eight_of_le_forty_eight {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (hsmall : n ≤ 48)
    (hloop : CH.Loopless D n) (hdeg : CH.MinOutdegreeAtLeast D n 6) :
    CH.HasDirectedCycleAtMost D n 8 := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, 6 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hdeg (Finset.mem_range.mp hv)
  have hh := card_ge_forty_nine hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hh
  omega

theorem boundary_second_cap_nine {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 9) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hV : V.card = 55) :
    ∀ u ∈ V, (ball D V u 2).card ≤ 13 := by
  have hfour : ∀ v ∈ V, 25 ≤ (ball D V v 4).card :=
    fun _ hv => card_ball_four_eight_free (hf.mono_bound (by decide)) hm hv
  have hfive : ∀ v ∈ V, 31 ≤ (ball D V v 5).card :=
    fun _ hv => card_ball_five_nine_free hf hm hv
  have heq := two_balls_boundary_cards hf (by decide : 4 + 5 ≤ 9) hfour hfive (by omega)
  intro u hu
  exact second_ball_cap_of_fourth_and_lower_orders (by decide : 4 ≤ 6) (by decide : 6 + 3 ≤ 9)
    (fun _ hd hd6 _ _ hG hmG hne => lower_order (by decide) hd hd6 hG hmG hne)
    hf hm hu (heq u hu).1.le

theorem br_nine_six : BoundaryRegular 9 6 := by
  apply br_of_second_ball_cap (by decide : 2 ≤ 6) (by decide : 6 ≤ 9)
  intro D hf hm
  exact boundary_second_cap_nine hf hm (by simp)

theorem ch_six_high_cutoff {q n : ℕ} (hq : 6 ≤ q) (hn : 0 < n) (hnq : n ≤ q * 6)
    {D : CH.Digraph} (hloop : CH.Loopless D n) (hdeg : CH.MinOutdegreeAtLeast D n 6) :
    CH.HasDirectedCycleAtMost D n q := by
  by_cases hq6 : q = 6
  · subst q; exact ch_six_of_le_thirty_six hn hnq hloop hdeg
  by_cases hq7 : q = 7
  · subst q; exact ch_seven_of_le_forty_two hn hnq hloop hdeg
  by_cases hq8 : q = 8
  · subst q; exact ch_eight_of_le_forty_eight hn hnq hloop hdeg
  by_cases hq9 : q = 9
  · subst q; exact ch_of_boundaryRegular (by decide) br_nine_six hn hnq hloop hdeg
  exact ch_in_window (by decide : 2 ≤ 6) (by omega) hn hnq hloop hdeg

end LeanCH.BR.BRq6
