import LeanCH.BR.BRDeficiencyCompletion
import LeanCH.BR.BRHighRowGrowth
import LeanCH.BR.BRsubTightSix

/-! The high-degree-three radius-four target, using the general deficiency completion. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45 BRsub

/-- A first layer at the degree-one boundary heads its entire exterior layer. -/
theorem first_pair_full_heads {D : CH.Digraph} {V : Finset ℕ} {u q d : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (h1 : (outN D V u).card = q + 1)
    (h2 : (ball D V u 2 \ ball D V u 1).card + 1 = d) :
    ∀ x ∈ outN D V u, ∀ y ∈ ball D V u 2 \ ball D V u 1, D x y = true := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  have hXE : (ball D V u 1).erase u = X := erase_ball_one_eq_outN hf (by omega) hu
  have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
    have hh := minOut_prefix_erase (d := 1) hf hu (by omega : 1 + 1 ≤ q) hmin
      (by omega : 1 + (ball D V u 2 \ ball D V u 1).card ≤ d)
    simpa only [hXE] using hh
  have hreg := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
    (hf.mono_set (show X ⊆ V from outN_subset)) hminX
    (by change (outN D V u).card = q * 1 + 1; omega)).1
  intro x hx y hy
  by_contra hn
  have hsub : outN D V x ⊆ outN D X x ∪ Y.erase y := by
    intro z hz
    have hh := outN_prefix_loss hf hu (by omega : 1 + 1 ≤ q) (hXE.symm ▸ hx) hz
    rw [hXE] at hh
    rcases Finset.mem_union.mp hh with hzX | hzY
    · exact Finset.mem_union_left _ hzX
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => hn (heq ▸ (mem_outN.mp hz).2), hzY⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hreg x hx, Finset.card_erase_of_mem hy] at hc
  change (outN D V x).card ≤ 1 + (Y.card - 1) at hc
  have hh := hmin x (outN_subset hx)
  have hYpos : 0 < Y.card := Finset.card_pos.mpr ⟨y, hy⟩
  change Y.card + 1 = d at h2
  omega

/-- The deficiency inequality leaves only two numerical profiles for a putative small ball. -/
theorem high_three_small_four_profile {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card) (hu : u ∈ V)
    (hh : 6 ≤ (outN D V u).card) (hsmall : (ball D V u 4).card ≤ 14) :
    (outN D V u).card = 6 ∧ (ball D V u 2 \ ball D V u 1).card = 2 ∧
      (((ball D V u 3 \ ball D V u 2).card = 4 ∧
         (ball D V u 4 \ ball D V u 3).card = 1) ∨
       ((ball D V u 3 \ ball D V u 2).card = 3 ∧
         (ball D V u 4 \ ball D V u 3).card = 2)) := by
  classical
  let a := (outN D V u).card
  let b := (ball D V u 2 \ ball D V u 1).card
  let c := (ball D V u 3 \ ball D V u 2).card
  let t := (ball D V u 4 \ ball D V u 3).card
  let n := (ball D V u 3).card - 1
  have h1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have h3 := high_row_ball_three_min (by decide : 2 ≤ 3) (by decide) hf hmin hu hh
  have htc : t ≤ 2 := by change (ball D V u 4 \ ball D V u 3).card ≤ 2; omega
  have hsum : a + b + c = n := by
    change (outN D V u).card + (ball D V u 2 \ ball D V u 1).card +
      (ball D V u 3 \ ball D V u 2).card = (ball D V u 3).card - 1
    omega
  have hnt : n + t ≤ 13 := by
    change (ball D V u 3).card - 1 + (ball D V u 4 \ ball D V u 3).card ≤ 13
    omega
  have hd := prefix_deficiency_of_ball (d := 3) (k := 2) (by decide : 1 ≤ 5)
    (BRq3.ball_all 5 (by decide)) hf hu (by decide) hmin (by decide)
    (by change t < 3; omega)
  change 16 ≤ n + c * (3 + t - 3) at hd
  have hdef : 16 ≤ n + c * t := by simpa using hd
  have hb : 2 ≤ b := by
    by_contra hn
    have hminX := minOut_prefix_erase (d := 2) hf hu (by decide : 1 + 1 ≤ 5) hmin
      (by change 2 + b ≤ 3; omega)
    rw [erase_ball_one_eq_outN hf (by decide) hu] at hminX
    have ha := corB (by decide : 1 ≤ 5) (hf.mono_set outN_subset) hminX
      (Finset.card_pos.mp (by omega : 0 < (outN D V u).card))
    change 11 ≤ a at ha
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with ht | ht | ht <;>
      rw [ht] at hdef hnt <;> omega
  change 6 ≤ a at hh
  change a = 6 ∧ b = 2 ∧ ((c = 4 ∧ t = 1) ∨ (c = 3 ∧ t = 2))
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with ht | ht | ht <;>
    rw [ht] at hdef hnt <;> omega

/-- The formerly open high-row radius-four estimate, with all premises discharged. -/
theorem high_three_ball_four_ge_fifteen {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card) (hu : u ∈ V)
    (hh : 6 ≤ (outN D V u).card) : 15 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  obtain ⟨h1, h2, hcases⟩ := high_three_small_four_profile hf hmin hu hh (by omega)
  have hhead := first_pair_full_heads (by decide : 2 ≤ 5) hf hu hmin h1 (by omega)
  let Y := ball D V u 2 \ ball D V u 1
  let A := ballSet D V Y 1
  let T := ballSet D V Y 2 \ A
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hAeq : A = ball D V u 3 \ ball D V u 1 :=
    second_layer_set_ball hf hu hhead (by decide : 1 ≤ 2)
  have hTeq : T = ball D V u 4 \ ball D V u 3 := by
    dsimp only [T]
    rw [second_layer_set_ball hf hu hhead (by decide : 2 ≤ 2), hAeq]
    ext v
    simp only [Finset.mem_sdiff]
    have hm : v ∈ ball D V u 1 → v ∈ ball D V u 3 :=
      fun h => ball_mono_radius (by decide : 1 ≤ 3) h
    tauto
  have hAc : A.card = 2 + (ball D V u 3 \ ball D V u 2).card := by
    rw [hAeq, Finset.card_sdiff_of_subset (ball_mono_radius (by decide : 1 ≤ 3))]
    have h12 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
    have h23 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
    omega
  have hminA (r : ℕ) (hr : r + T.card ≤ 3) :
      ∀ v ∈ A, r ≤ (outN D A v).card := by
    intro v hv
    have hsub : outN D V v ⊆ outN D A v ∪ T := by
      intro w hw
      by_cases hwA : w ∈ A
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hwA, (mem_outN.mp hw).2⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨outN_subset_ballSet_succ hv hw, hwA⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin v (ballSet_subset hv)
    omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hfA := hf.mono_set (show A ⊆ V from ballSet_subset)
  rcases hcases with ⟨hc, ht⟩ | ⟨hc, ht⟩
  · have hmin2 := hminA 2 (by rw [hTeq, ht])
    have hsize := corB (by decide : 1 ≤ 5) hfA hmin2 hne
    omega
  · have hmin1 := hminA 1 (by rw [hTeq, ht])
    have hsize := dt_size (by decide : 1 ≤ 5) (ball_q_one 5 (by decide)) hfA hmin1 hne
    omega

/-- The radius-four high-row bound extends to every cutoff at least five. -/
theorem high_three_ball_four {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card) (hu : u ∈ V)
    (hh : q + 1 ≤ (outN D V u).card) : q + 10 ≤ (ball D V u 4).card := by
  by_cases hq5 : q = 5
  · subst q
    exact high_three_ball_four_ge_fifteen hf hmin hu hh
  have hq6 : 6 ≤ q := by omega
  by_contra hn
  have hsmall : (ball D V u 4).card ≤ q + 9 := by omega
  let a := (outN D V u).card
  let b := (ball D V u 2 \ ball D V u 1).card
  let c := (ball D V u 3 \ ball D V u 2).card
  let t := (ball D V u 4 \ ball D V u 3).card
  let n := (ball D V u 3).card - 1
  have h1 := card_B1 (hf.mono_bound (by omega : 4 ≤ q)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have h3 := high_row_ball_three_min (by decide : 2 ≤ 3) (by omega) hf hmin hu hh
  have htc : t ≤ 2 := by change (ball D V u 4 \ ball D V u 3).card ≤ 2; omega
  have hsum : a + b + c = n := by
    change (outN D V u).card + (ball D V u 2 \ ball D V u 1).card +
      (ball D V u 3 \ ball D V u 2).card = (ball D V u 3).card - 1
    omega
  have hnt : n + t ≤ q + 8 := by
    change (ball D V u 3).card - 1 + (ball D V u 4 \ ball D V u 3).card ≤ q + 8
    omega
  have hd := prefix_deficiency_of_ball (d := 3) (k := 2) (by omega : 1 ≤ q)
    (BRq3.ball_all q (by omega)) hf hu (by omega) hmin (by decide)
    (by change t < 3; omega)
  change q * 3 + 1 ≤ n + c * (3 + t - 3) at hd
  have hdef : q * 3 + 1 ≤ n + c * t := by simpa using hd
  have hb : 2 ≤ b := by
    by_contra hn
    have hminX := minOut_prefix_erase (d := 2) hf hu (by omega : 1 + 1 ≤ q) hmin
      (by change 2 + b ≤ 3; omega)
    rw [erase_ball_one_eq_outN hf (by omega) hu] at hminX
    have ha := corB (by omega : 1 ≤ q) (hf.mono_set outN_subset) hminX
      (Finset.card_pos.mp (by omega : 0 < (outN D V u).card))
    change 2 * q + 1 ≤ a at ha
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with ht | ht | ht <;>
      rw [ht] at hdef hnt <;> omega
  change q + 1 ≤ a at hh
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with ht | ht | ht <;>
    rw [ht] at hdef hnt <;> omega

/-- High rows have two fewer possible incoming neighbours than generic degree-three rows. -/
theorem three_core_six_density {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card) :
    16 * V.card + 5 * H.card ≤ V.card * V.card := by
  classical
  have hcap : ∀ v ∈ V, (inN D V v).card + 13 ≤ V.card := by
    intro v hv
    have hb := ball_of_min (BRq3.ball_all 5 (by decide)) hf hmin v hv
    have hi := incoming_add_ball_le hf hv (by decide : 4 + 1 ≤ 5)
    change 13 ≤ (ball D V v 4).card at hb
    omega
  have hcapH : ∀ v ∈ H, (inN D V v).card + 15 ≤ V.card := by
    intro v hv
    have hb := high_three_ball_four_ge_fifteen hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by decide : 4 + 1 ≤ 5)
    omega
  have hloH := Finset.sum_le_sum hhigh
  have hloL := Finset.sum_le_sum
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := V \ H)
  have hupH := Finset.sum_le_sum hcapH
  have hupL := Finset.sum_le_sum
    (fun v hv => hcap v (Finset.mem_sdiff.mp hv).1) (s := V \ H)
  simp only [Finset.sum_add_distrib] at hupH hupL
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hloH hloL
  simp only [Finset.sum_const_nat (fun _ _ => rfl)] at hupH hupL
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  nlinarith

end LeanCH.BR.BRsGen
