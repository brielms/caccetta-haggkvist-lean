import LeanCH.BR.BRWideFirstFunnel

/-! A degree-three head start persists through every radius below the girth cutoff. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem degree_two_strict_ball {D : CH.Digraph} {V : Finset ℕ} {u q k : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hu : u ∈ V) (hhigh : 3 ≤ (outN D V u).card)
    (hk : 1 ≤ k) (hkq : k + 1 ≤ q) : 2 * k + 2 ≤ (ball D V u k).card := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
      rw [erase_ball_one_eq_outN hf (by omega) hu] at he
      omega
    have hk2 : 2 ≤ k := by omega
    by_contra hn
    have hsmall : (ball D V u k).card ≤ 2 * k + 1 := by omega
    have hprev := ih (k - 1) (by omega) (by omega) (by omega)
    let U := (ball D V u (k - 1)).erase u
    let H := (ball D V u (k - 2)).erase u
    let T := ball D V u k \ ball D V u (k - 1)
    have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hUc : U.card = (ball D V u (k - 1)).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    have hHc : H.card = (ball D V u (k - 2)).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    have hstep := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by omega : k - 1 ≤ k))
    change T.card + (ball D V u (k - 1)).card = (ball D V u k).card at hstep
    have hTc : T.card ≤ 1 := by omega
    have hUcap : U.card ≤ 2 * k := by omega
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hTpos : 1 ≤ T.card := by
      by_contra hzero
      have hmin2 : ∀ v ∈ U, 2 ≤ (outN D U v).card :=
        minOut_prefix_erase hf hu (by omega : (k - 1) + 1 ≤ q) hmin (by
          rw [show k - 1 + 1 = k by omega]
          change 2 + T.card ≤ 2
          omega)
      have hh := corB (by omega : 1 ≤ k) ((hf.mono_bound (by omega : k ≤ q)).mono_set hUV)
        hmin2 hne
      omega
    have hmin1 : ∀ v ∈ U, 1 ≤ (outN D U v).card :=
      minOut_prefix_erase hf hu (by omega : (k - 1) + 1 ≤ q) hmin (by
        rw [show k - 1 + 1 = k by omega]
        change 1 + T.card ≤ 2
        omega)
    by_cases hkEq : k = 2
    · have hsize := dt_size (by decide : 1 ≤ 3) (ball_q_one 3 (by decide))
        ((hf.mono_bound (by omega : 3 ≤ q)).mono_set hUV) hmin1 hne
      omega
    · have hk3 : 3 ≤ k := by omega
      have hprev2 := ih (k - 2) (by omega) (by omega) (by omega)
      have hHU : H ⊆ U := Finset.erase_subset_erase u (ball_mono_radius (by omega))
      have hhighH : ∀ v ∈ H, 2 ≤ (outN D U v).card := by
        intro v hv
        have hh := (hmin v (hUV (hHU hv))).trans (Finset.card_le_card
          (outN_prefix_erase_root hf hu (by omega : (k - 2) + 1 ≤ q)
            (Finset.mem_of_mem_erase hv)))
        rw [show k - 2 + 1 = k - 1 by omega] at hh
        exact hh
      have hcount := small_one_core_high_count (by omega : 1 ≤ k)
        ((hf.mono_bound (by omega : k ≤ q)).mono_set hUV) hmin1 hne hUcap hHU hhighH
      omega

theorem two_core_three_density {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 3 ≤ (outN D V v).card) :
    (2 * q + 1) * V.card + 2 * H.card ≤ V.card * V.card := by
  classical
  have hi : ∀ v ∈ V, (inN D V v).card + (ball D V v (q - 1)).card ≤ V.card := by
    intro v hv
    have hsub : inN D V v ⊆ V \ ball D V v (q - 1) := by
      intro x hx
      obtain ⟨hxV, hxv⟩ := mem_inN.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxV, fun hxB => no_back_arc hf hv hxB (by omega) hxv⟩
    have hc := Finset.card_le_card hsub
    have he := Finset.card_sdiff_add_card_eq_card
      (ball_subset (D := D) (W := V) (u := v) (k := q - 1))
    omega
  have hgapH : ∀ v ∈ H, (inN D V v).card + (2 * q + 3) ≤ V.card + (outN D V v).card := by
    intro v hv
    have hb := degree_two_strict_ball hf hmin (hHV hv) (hhigh v hv)
      (by omega : 1 ≤ q - 1) (by omega : q - 1 + 1 ≤ q)
    have hh := hi v (hHV hv)
    have ho := hhigh v hv
    omega
  have hgapL : ∀ v ∈ V \ H,
      (inN D V v).card + (2 * q + 1) ≤ V.card + (outN D V v).card := by
    intro v hv
    have hvV := (Finset.mem_sdiff.mp hv).1
    have hb := ball_growth q (by omega) D V hf hmin v hvV (q - 1) (by omega)
    have hh := hi v hvV
    have ho := hmin v hvV
    omega
  have hsH := Finset.sum_le_sum hgapH
  have hsL := Finset.sum_le_sum hgapL
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsL
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hin := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  nlinarith

end LeanCH.BR.BRsGen
