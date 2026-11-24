import LeanCH.BR.BRWideFirstFunnel
import LeanCH.BR.BRHighRowGrowth

/-! Strict deficiency strengthens radius-four growth in a degree-two host. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem high_two_ball_four {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card) (hu : u ∈ V)
    (hhigh : q + 1 ≤ (outN D V u).card) :
    q + 7 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 4).card ≤ q + 6 := by omega
  let U := (ball D V u 3).erase u
  let H := (ball D V u 2).erase u
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let T := ball D V u 4 \ ball D V u 3
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by decide : 2 ≤ 3))
  have hXH : X ⊆ H := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      exact loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hx).2)
    · exact ball_mono_radius (by decide : 1 ≤ 2) ((mem_ball_one hu).mpr (Or.inr hx))
  have hne : U.Nonempty :=
    (Finset.card_pos.mp (by change 0 < (outN D V u).card; omega)).mono (hXH.trans hHU)
  have hUc : U.card = (ball D V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hB1 : (ball D V u 1).card = (outN D V u).card + 1 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by omega) hu] at he
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hB3 := high_row_ball_three_min (by decide : 2 ≤ 2) (by omega) hf hmin hu hhigh
  have hTc : T.card ≤ 1 := by change (ball D V u 4 \ ball D V u 3).card ≤ 1; omega
  have hUcap : U.card ≤ 2 * q := by
    have hm := Finset.card_le_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
    omega
  have hTpos : 1 ≤ T.card := by
    by_contra hzero
    have hmin2 : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
      minOut_prefix_erase hf hu (by omega : 3 + 1 ≤ q) hmin (by
        change 2 + T.card ≤ 2; omega)
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set hUV) hmin2 hne
    omega
  have hYpos : 1 ≤ Y.card := by
    by_contra hzero
    have hmin2 := minOut_prefix_erase (d := 2) hf hu (by omega : 1 + 1 ≤ q) hmin
      (by change 2 + Y.card ≤ 2; omega)
    rw [erase_ball_one_eq_outN hf (by omega) hu] at hmin2
    have hXcap := Finset.card_le_card (hXH.trans hHU)
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set outN_subset) hmin2
      (Finset.card_pos.mp (by omega : 0 < (outN D V u).card))
    change X.card ≤ U.card at hXcap
    change 2 * q + 1 ≤ X.card at hh
    omega
  have hminU : ∀ v ∈ U, 1 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : 3 + 1 ≤ q) hmin
      (by change 1 + T.card ≤ 2; omega)
  have hhighH : ∀ v ∈ H, 2 ≤ (outN D U v).card := by
    intro v hv
    exact (hmin v (hUV (hHU hv))).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by omega : 2 + 1 ≤ q)
        (Finset.mem_of_mem_erase hv)))
  have hcount := small_one_core_high_count (by omega : 1 ≤ q)
    (hf.mono_set hUV) hminU hne hUcap hHU hhighH
  change (ball D V u 4 \ ball D V u 3).card ≥ 1 at hTpos
  change 1 ≤ (ball D V u 2 \ ball D V u 1).card at hYpos
  omega

theorem two_core_high_density_four {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card) :
    (2 * q + 1) * V.card + 7 * H.card ≤ V.card * V.card := by
  classical
  have hcap : ∀ v ∈ V, (inN D V v).card + 2 * q ≤ V.card + 1 := by
    intro v hv
    have hb := ball_growth q (by omega) D V hf hmin v hv (q - 1) (by omega)
    have hi := incoming_add_ball_le hf hv (by omega : q - 1 + 1 ≤ q)
    omega
  have hcapH : ∀ v ∈ H, (inN D V v).card + q + 7 ≤ V.card := by
    intro v hv
    have hb := high_two_ball_four hq hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by omega : 4 + 1 ≤ q)
    omega
  have hloH := Finset.sum_le_sum hhigh
  have hloL := Finset.sum_le_sum
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := V \ H)
  have hupH := Finset.sum_le_sum hcapH
  have hupL := Finset.sum_le_sum
    (fun v hv => hcap v (Finset.mem_sdiff.mp hv).1) (s := V \ H)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hloH hloL hupH hupL
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  nlinarith

end LeanCH.BR.BRsGen
