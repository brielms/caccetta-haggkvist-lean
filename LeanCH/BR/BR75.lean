import LeanCH.BR.BR75Reduction
import LeanCH.BR.BRThreeTightStages

/-! The boundary case (7,5) closes using its full seven-free hypothesis. -/

namespace LeanCH.BR.BR75
open BRq2 BRq3 BRq4 BR45 BRsGen BRsub Compose.Boundary

theorem card_ball_four_seven_free {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hu : u ∈ V) :
    21 ≤ (ball D V u 4).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hmin
  have hF := qfree_sub hsub hf
  suffices hball : 21 ≤ (ball F V u 4).card from
    hball.trans (Finset.card_le_card (ball_sub hsub))
  classical
  by_contra hn
  have hsmall : (ball F V u 4).card ≤ 20 := by omega
  have hm : ∀ v ∈ V, 5 ≤ (outN F V v).card := fun v hv => (ho v hv).ge
  let b := (ball F V u 2 \ ball F V u 1).card
  let c := (ball F V u 3 \ ball F V u 2).card
  let t := (ball F V u 4 \ ball F V u 3).card
  have hp := deficient_five_ball_profile (hF.mono_bound (by decide)) ho hu hsmall
  have hb : 5 ≤ b := n2_ge_s (by decide) (hF.mono_bound (by decide)) ho hu
  have h1 : (ball F V u 1).card = 6 := by
    rw [card_B1 (hF.mono_bound (by decide)) hu, ho u hu]
  have h12 : b + (ball F V u 1).card = (ball F V u 2).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have h23 : c + (ball F V u 2).card = (ball F V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have h34 : t + (ball F V u 3).card = (ball F V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hnot3 : t ≠ 3 := by
    intro ht
    let U := (ball F V u 3).erase u
    let H := (ball F V u 2).erase u
    have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hHU : H ⊆ U := Finset.erase_subset_erase _ (ball_mono_radius (by decide))
    have hUc : U.card = 16 := by
      have he := Finset.card_erase_of_mem (self_mem_ball (D := F) (k := 3) hu)
      change U.card = _ at he
      have h20 := card_ball_four_ge_twenty (hF.mono_bound (by decide)) hm hu
      omega
    have hHc : 10 ≤ H.card := by
      have he := Finset.card_erase_of_mem (self_mem_ball (D := F) (k := 2) hu)
      change H.card = _ at he
      omega
    have hmU : ∀ v ∈ U, 2 ≤ (outN F U v).card :=
      minOut_prefix_erase hF hu (by decide : 3 + 1 ≤ 7) hm (by
        change 2 + t ≤ 5; omega)
    have hh : ∀ v ∈ H, 5 ≤ (outN F U v).card := by
      intro v hv
      exact (hm v (hUV (hHU hv))).trans (Finset.card_le_card
        (outN_prefix_erase_root hF hu (by decide : 2 + 1 ≤ 7) (Finset.mem_of_mem_erase hv)))
    have hb2 : Ball 7 2 := by
      intro G W hG hOut w hw
      exact ball_growth 7 (by decide) G W hG (fun v hv => (hOut v hv).ge) w hw 6 (by decide)
    have hd := mixed_degree_density_of_ball (by decide : 1 ≤ 7) hb2
      (hF.mono_set hUV) hmU hHU hh
    rw [hUc] at hd
    omega
  have hnot44 : ¬ (c = 4 ∧ t = 4) := by
    rintro ⟨hc, ht⟩
    let A := (ball F V u 2).erase u
    let X := outN F V u
    have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hXA : X ⊆ A := by
      change outN F V u ⊆ (ball F V u 2).erase u
      rw [← erase_ball_one_eq_outN hF (by decide) hu]
      exact Finset.erase_subset_erase _ (ball_mono_radius (by decide))
    have hAc : A.card ≤ 12 := by
      have he := Finset.card_erase_of_mem (self_mem_ball (D := F) (k := 2) hu)
      change A.card = _ at he
      omega
    have hmA : ∀ v ∈ A, 1 ≤ (outN F A v).card :=
      minOut_prefix_erase hF hu (by decide : 2 + 1 ≤ 7) hm (by
        change 1 + c ≤ 5; omega)
    have hh : ∀ v ∈ X, 5 ≤ (outN F A v).card := by
      intro v hv
      exact (hm v (outN_subset hv)).trans (Finset.card_le_card
        (outN_prefix_erase_root hF hu (by decide : 1 + 1 ≤ 7)
          ((mem_ball_one hu).mpr (Or.inr hv))))
    have hd := small_one_high_degree_count_of_le (by decide : 3 ≤ 5)
      (by decide : 5 ≤ 7) (hF.mono_set hAV) hAc hmA hXA hh
    have hXc : X.card = 5 := ho u hu
    omega
  have h555 : b = 5 ∧ c = 5 ∧ t = 4 := by
    change FiveBallProfile b c t at hp
    unfold FiveBallProfile at hp
    omega
  have hg := fourth_layer_of_two_tight_layers (by decide : 2 ≤ 5) hF ho hu h555.1 h555.2.1
  change 5 ≤ t at hg
  omega

theorem card_ge_thirty_six {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hne : V.Nonempty) :
    36 ≤ V.card := by
  have hh := card_ge_of_two_balls (i := 3) (j := 4) (a := 16) (b := 21) hf (by decide)
    (fun _ hv => card_ball_three_ge_sixteen (hf.mono_bound (by decide)) hm hv)
    (fun _ hv => card_ball_four_seven_free hf hm hv) hne
  omega

theorem card_ge_forty_one {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 8) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hne : V.Nonempty) :
    41 ≤ V.card := by
  have hh := card_ge_of_two_balls (i := 4) (j := 4) (a := 21) (b := 21) hf (by decide)
    (fun _ hv => card_ball_four_seven_free (hf.mono_bound (by decide)) hm hv)
    (fun _ hv => card_ball_four_seven_free (hf.mono_bound (by decide)) hm hv) hne
  omega

theorem ch_seven_of_le_thirty_five {D : CH.Digraph} {n : ℕ}
    (hn : 0 < n) (hsmall : n ≤ 35) (hloop : CH.Loopless D n)
    (hout : CH.MinOutdegreeAtLeast D n 5) : CH.HasDirectedCycleAtMost D n 7 := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, 5 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hout (Finset.mem_range.mp hv)
  have hs := card_ge_thirty_six hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hs
  omega

theorem ch_eight_of_le_forty {D : CH.Digraph} {n : ℕ}
    (hn : 0 < n) (hsmall : n ≤ 40) (hloop : CH.Loopless D n)
    (hout : CH.MinOutdegreeAtLeast D n 5) : CH.HasDirectedCycleAtMost D n 8 := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, 5 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hout (Finset.mem_range.mp hv)
  have hs := card_ge_forty_one hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hs
  omega

theorem boundary_second_ball_cap {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hV : V.card = 36) :
    ∀ u ∈ V, (ball D V u 2).card ≤ 11 := by
  have hthree : ∀ v ∈ V, 16 ≤ (ball D V v 3).card :=
    fun _ hv => card_ball_three_ge_sixteen (hf.mono_bound (by decide)) hm hv
  have hfour : ∀ v ∈ V, 21 ≤ (ball D V v 4).card :=
    fun _ hv => card_ball_four_seven_free hf hm hv
  have heq := two_balls_boundary_cards hf (by decide : 3 + 4 ≤ 7) hthree hfour (by omega)
  intro u hu
  exact BR65.second_ball_cap_of_third (hf.mono_bound (by decide)) hm hu (heq u hu).1.le

theorem boundary_out_regular {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hV : V.card = 36) :
    OutEq 5 D V :=
  out_regular_of_second_ball_cap (by decide) (hf.mono_bound (by decide)) hm
    (boundary_second_ball_cap hf hm hV)

theorem boundary_saturated {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hV : V.card = 36) :
    Sat 7 D V :=
  sat_of_forced_out_regular (fun _ hF hmF => boundary_out_regular hF hmF hV) hf hm

theorem boundary_in_regular {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hV : V.card = 36) :
    ∀ u ∈ V, (inN D V u).card = 5 :=
  incoming_regular_of_second_ball_cap (by decide) (by decide) hf hm
    (boundary_saturated hf hm hV) hV (boundary_second_ball_cap hf hm hV)

theorem boundary_ball_six {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 36) (hu : u ∈ V) : (ball D V u 6).card = 31 := by
  have hi := boundary_in_regular hf hm hV u hu
  have hb := card_inN_of_satQ (by decide : 1 ≤ 7) hf (boundary_saturated hf hm hV) hu
  change (inN D V u).card + (ball D V u 6).card = V.card at hb
  omega

theorem br_seven_five : BoundaryRegular 7 5 := by
  apply br_of_second_ball_cap (by decide : 2 ≤ 5) (by decide : 5 ≤ 7)
  intro D hf hm
  exact boundary_second_ball_cap hf hm (by simp)

theorem bball_seven_five : BBall 7 5 := by
  intro D hf ho u hu
  have hb := boundary_ball_six hf (fun v hv => (ho v hv).ge) (by simp) hu
  change 31 ≤ (ball D (Finset.range (7 * 5 + 1)) u 6).card
  omega

theorem ball_small_seven_five : BallSmall 7 5 := by
  intro D V hf ho hV u hu
  have hm : ∀ v ∈ V, 5 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have hlo := card_ge_thirty_six hf hm ⟨u, hu⟩
  have hb := boundary_ball_six hf hm (by omega) hu
  change 31 ≤ (ball D V u 6).card
  omega

end LeanCH.BR.BR75
