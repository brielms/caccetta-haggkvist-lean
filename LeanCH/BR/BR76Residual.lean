import LeanCH.BR.BRq6Seeds
import LeanCH.BR.BRTightPair

/-! The seven-free degree-six fourth-ball gap reduces to three non-tight profiles. -/

namespace LeanCH.BR.BRq6
open BRq2 BRq3 BRq4 BR45 BRsGen Compose.Boundary

theorem fourth_layer_of_tight_third {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 6 D V) (hu : u ∈ V)
    (hB3 : (ball D V u 3).card = 19) :
    6 ≤ (ball D V u 4 \ ball D V u 3).card := by
  have hm : ∀ v ∈ V, 6 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have htwo := card_ball_two_ge_twice (by decide : 2 ≤ 6) (hf.mono_bound (by decide)) hm hu
  have hthird := third_layer_of_cap (by decide : 7 ≤ 7) hf hm hu hB3.le
  have hB1 : (ball D V u 1).card = 7 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have hB0 : (ball D V u 0).card = 1 := by
    have hsub : ball D V u 0 ⊆ {u} := fun _ hv => Finset.mem_singleton.mpr (eq_of_mem_ball_zero hv)
    have hlo := Finset.card_pos.mpr (⟨u, self_mem_ball hu⟩ : (ball D V u 0).Nonempty)
    have hhi := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hhi
    omega
  have he1 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 0 ≤ 1))
  have he2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have he3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have htight : ∀ i, 1 ≤ i → i ≤ 3 → (ball D V u i \ ball D V u (i - 1)).card = 6 := by
    intro i hi hi3
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    all_goals simp only [Nat.reduceSub]; omega
  exact tight_layers_expand_pair (by decide : 2 ≤ 6) (by decide : 2 ≤ 3)
    (by decide : 6 + 1 ≤ 7) (by decide) hf hm hu htight

theorem seven_free_deficient_fourth_cards {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 6 D V) (hu : u ∈ V)
    (hcap : (ball D V u 4).card ≤ 24) :
    (ball D V u 3).card = 20 ∧ (ball D V u 4 \ ball D V u 3).card = 4 ∧
      (ball D V u 4).card = 24 := by
  have hm : ∀ v ∈ V, 6 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have hthree := card_ball_three_seven_free hf hm hu
  let t := (ball D V u 4 \ ball D V u 3).card
  have ht : t + (ball D V u 3).card = (ball D V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have ht4 : 4 ≤ t := by
    by_contra hn
    let U := (ball D V u 3).erase u
    have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hUc : U.card = (ball D V u 3).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
    have hmU : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
      minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 7) hm (by change 3 + t ≤ 6; omega)
    have hh := lower_order (by decide : 5 ≤ 7) (by decide : 2 ≤ 3) (by decide)
      (hf.mono_set hUV) hmU (Finset.card_pos.mp (by omega : 0 < U.card))
    -- The order bound alone leaves the t=0,1,2 cases; their stronger degree floors exclude them.
    by_cases ht3 : t = 3
    · omega
    have hmU4 : ∀ v ∈ U, 4 ≤ (outN D U v).card :=
      minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 7) hm (by change 4 + t ≤ 6; omega)
    have hh4 := lower_order (by decide : 5 ≤ 7) (by decide : 2 ≤ 4) (by decide)
      (hf.mono_set hUV) hmU4 (Finset.card_pos.mp (by omega : 0 < U.card))
    omega
  have hB3ne : (ball D V u 3).card ≠ 19 := by
    intro heq
    have hh := fourth_layer_of_tight_third hf ho hu heq
    change 6 ≤ t at hh
    omega
  exact ⟨by omega, by change t = 4; omega, by omega⟩

theorem card_ball_four_seven_free_ge_twenty_four {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    24 ≤ (ball D V u 4).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hm
  have hF := qfree_sub hsub hf
  suffices hh : 24 ≤ (ball F V u 4).card from hh.trans (Finset.card_le_card (ball_sub hsub))
  by_contra hn
  have hh := (seven_free_deficient_fourth_cards hF ho hu (by omega)).2.2
  omega

/-- Every deficient fourth ball in an exact-six host has profile (6,b,13-b,4), b=6,7,8. -/
theorem seven_free_deficient_fourth_profile {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 6 D V) (hu : u ∈ V)
    (hcap : (ball D V u 4).card ≤ 24) :
    (ball D V u 4 \ ball D V u 3).card = 4 ∧
    ((ball D V u 2 \ ball D V u 1).card = 6 ∧ (ball D V u 3 \ ball D V u 2).card = 7 ∨
     (ball D V u 2 \ ball D V u 1).card = 7 ∧ (ball D V u 3 \ ball D V u 2).card = 6 ∨
     (ball D V u 2 \ ball D V u 1).card = 8 ∧ (ball D V u 3 \ ball D V u 2).card = 5) := by
  classical
  obtain ⟨hB3, ht, hB4⟩ := seven_free_deficient_fourth_cards hf ho hu hcap
  have hm : ∀ v ∈ V, 6 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have htwo := card_ball_two_ge_twice (by decide : 2 ≤ 6) (hf.mono_bound (by decide)) hm hu
  have hB1 : (ball D V u 1).card = 7 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have he2 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have he3 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  let c := (ball D V u 3 \ ball D V u 2).card
  have hc5 : 5 ≤ c := by
    by_contra hn
    let A := (ball D V u 2).erase u
    have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hAc : A.card = (ball D V u 2).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hmA : ∀ v ∈ A, 2 ≤ (outN D A v).card :=
      minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 7) hm (by change 2 + c ≤ 6; omega)
    by_cases hc4 : c = 4
    · have hA15 : A.card = 15 := by omega
      have hb2 : Ball 7 2 := by
        intro G W hG hOut w hw
        exact ball_growth 7 (by decide) G W hG (fun v hv => (hOut v hv).ge) w hw 6 (by decide)
      have hreg := (dt_reg (by decide : 1 ≤ 7) hb2 (hf.mono_set hAV) hmA hA15).1
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have hh := hm u hu; omega : 0 < (outN D V u).card)
      have hx1 : x ∈ ball D V u 1 := (mem_ball_one hu).mpr (Or.inr hx)
      have hxA : x ∈ A := by
        refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by decide : 1 ≤ 2) hx1⟩
        intro heq
        exact loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2)
      have hhigh := (hm x (outN_subset hx)).trans (Finset.card_le_card
        (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 7) hx1))
      change 6 ≤ (outN D A x).card at hhigh
      have hh := hreg x hxA
      omega
    · have hmA3 : ∀ v ∈ A, 3 ≤ (outN D A v).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 7) hm (by change 3 + c ≤ 6; omega)
      have hh := lower_order (by decide : 5 ≤ 7) (by decide : 2 ≤ 3) (by decide)
        (hf.mono_set hAV) hmA3 hAne
      omega
  refine ⟨ht, ?_⟩
  change 5 ≤ (ball D V u 3 \ ball D V u 2).card at hc5
  omega

/-- These three actual-graph exclusions remain unproved. -/
def SevenFreeFourBallResidual : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ) (u : ℕ), QFree D V 7 → OutEq 6 D V → u ∈ V →
    (ball D V u 4 \ ball D V u 3).card = 4 →
    ((ball D V u 2 \ ball D V u 1).card = 6 ∧ (ball D V u 3 \ ball D V u 2).card = 7 ∨
     (ball D V u 2 \ ball D V u 1).card = 7 ∧ (ball D V u 3 \ ball D V u 2).card = 6 ∨
     (ball D V u 2 \ ball D V u 1).card = 8 ∧ (ball D V u 3 \ ball D V u 2).card = 5) → False

theorem four_ball_seven_of_residual (h : SevenFreeFourBallResidual)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hf : QFree D V 7)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    25 ≤ (ball D V u 4).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hm
  have hF := qfree_sub hsub hf
  suffices hh : 25 ≤ (ball F V u 4).card from hh.trans (Finset.card_le_card (ball_sub hsub))
  by_contra hn
  obtain ⟨ht, hp⟩ := seven_free_deficient_fourth_profile hF ho hu (by omega)
  exact h F V u hF ho hu ht hp

/-- The three-profile residual is equivalent to the arbitrary-host fourth-ball target. -/
theorem four_ball_seven_iff_residual :
    (∀ {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}, QFree D V 7 →
      (∀ v ∈ V, 6 ≤ (outN D V v).card) → u ∈ V → 25 ≤ (ball D V u 4).card) ↔
    SevenFreeFourBallResidual := by
  constructor
  · intro h D V u hf ho hu ht hp
    have hB1 : (ball D V u 1).card = 7 := by
      rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
    have he2 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
    have he3 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
    have he4 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
    have hh := h hf (fun v hv => (ho v hv).ge) hu
    omega
  · exact four_ball_seven_of_residual

theorem br_seven_six_of_residual (h : SevenFreeFourBallResidual) : BoundaryRegular 7 6 := by
  apply br_of_second_ball_cap (by decide : 2 ≤ 6) (by decide : 6 ≤ 7)
  intro D hf hm u hu
  have hthree : ∀ v ∈ Finset.range 43, 19 ≤ (ball D (Finset.range 43) v 3).card :=
    fun _ hv => card_ball_three_seven_free hf hm hv
  have heq := two_balls_boundary_cards hf (by decide : 3 + 4 ≤ 7) hthree
    (fun _ hv => four_ball_seven_of_residual h hf hm hv) (by simp)
  exact second_ball_cap_of_third_and_lower_orders (by decide : 4 ≤ 6) (by decide : 6 + 1 ≤ 7)
    (fun _ hd hd6 _ _ hF hmF hn => lower_order (by decide) hd hd6 hF hmF hn)
    hf hm hu (heq u hu).1.le

theorem card_ge_forty_two {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hn : V.Nonempty) :
    42 ≤ V.card := by
  have hh := card_ge_of_two_balls hf (by decide : 3 + 4 ≤ 7)
    (fun _ hv => card_ball_three_seven_free hf hm hv)
    (fun _ hv => card_ball_four_seven_free_ge_twenty_four hf hm hv) hn
  omega

theorem ch_seven_of_le_forty_one {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (hsmall : n ≤ 41)
    (hloop : CH.Loopless D n) (hdeg : CH.MinOutdegreeAtLeast D n 6) :
    CH.HasDirectedCycleAtMost D n 7 := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, 6 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hdeg (Finset.mem_range.mp hv)
  have hh := card_ge_forty_two hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hh
  omega

/-- Equality in the weaker 19+24 ball count is incompatible with a tight third ball. -/
theorem card_ge_forty_three {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hn : V.Nonempty) :
    43 ≤ V.card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hm
  have hF := qfree_sub hsub hf
  have hmF : ∀ v ∈ V, 6 ≤ (outN F V v).card := fun v hv => (ho v hv).ge
  have hlo := card_ge_forty_two hF hmF hn
  by_contra hnot
  have hN : V.card = 42 := by omega
  have hthree : ∀ v ∈ V, 19 ≤ (ball F V v 3).card :=
    fun _ hv => card_ball_three_seven_free hF hmF hv
  have hfour : ∀ v ∈ V, 24 ≤ (ball F V v 4).card :=
    fun _ hv => card_ball_four_seven_free_ge_twenty_four hF hmF hv
  have heq := two_balls_boundary_cards hF (by decide : 3 + 4 ≤ 7) hthree hfour (by omega)
  obtain ⟨u, hu⟩ := hn
  have hB3 := (heq u hu).1
  have hB4 := (heq u hu).2
  have hh := fourth_layer_of_tight_third hF ho hu hB3
  have he := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := V) (u := u) (by decide : 3 ≤ 4))
  omega

theorem ch_seven_of_le_forty_two {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (hsmall : n ≤ 42)
    (hloop : CH.Loopless D n) (hdeg : CH.MinOutdegreeAtLeast D n 6) :
    CH.HasDirectedCycleAtMost D n 7 := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, 6 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hdeg (Finset.mem_range.mp hv)
  have hh := card_ge_forty_three hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hh
  omega

end LeanCH.BR.BRq6
