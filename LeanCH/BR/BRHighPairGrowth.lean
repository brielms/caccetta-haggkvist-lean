import LeanCH.BR.BRHighPairCore
import LeanCH.BR.BRStrictPrefixDeficiency
import LeanCH.BR.BRRootThinning

/-! A high root with a high head gains another radius-four vertex at minimum two. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem high_two_pair_ball_four_exact {D : CH.Digraph} {V : Finset ℕ} {q u v : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 2 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = q + 1)
    (hv : v ∈ outN D V u) (hhigh : q + 1 ≤ (outN D V v).card) :
    q + 8 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 4).card ≤ q + 7 := by omega
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  let A := (ball D V u 2).erase u
  let W := (ball D V u 3).erase u
  have hXV : X ⊆ V := outN_subset
  have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hWV : W ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hAW : A ⊆ W := Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXE : (ball D V u 1).erase u = X := erase_ball_one_eq_outN hf (by omega) hu
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXA : X ⊆ A := by
    rw [← hXE]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXc : X.card = q + 1 := hdegree
  have hB1 : (ball D V u 1).card = q + 2 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by omega) hu, hdegree] at he
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  change Y.card + (ball D V u 1).card = (ball D V u 2).card at h12
  change Z.card + (ball D V u 2).card = (ball D V u 3).card at h23
  change T.card + (ball D V u 3).card = (ball D V u 4).card at h34
  have hAc0 : A.card = (ball D V u 2).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hWc0 : W.card = (ball D V u 3).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hAc : A.card = q + 1 + Y.card := by omega
  have hWc : W.card = q + 1 + Y.card + Z.card := by omega
  have hhighX : ∀ x ∈ X, 2 ≤ (outN D A x).card := by
    intro x hx
    exact (hmin x (hXV hx)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hx)))
  have hvhighA : q + 1 ≤ (outN D A v).card := hhigh.trans (Finset.card_le_card
    (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hv)))
  have hvhighW : q + 1 ≤ (outN D W v).card :=
    hvhighA.trans (Finset.card_le_card (outN_mono hAW v))
  have hYlo : 2 ≤ Y.card := by
    by_contra hn
    have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
      have hh := minOut_prefix_erase (d := 1) hf hu (by omega : 1 + 1 ≤ q) hmin
        (by change 1 + Y.card ≤ 2; omega)
      simpa only [hXE] using hh
    have hr := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
      (hf.mono_set hXV) hminX (by omega : X.card = q * 1 + 1)).1 v hv
    have hc := (Finset.card_le_card (outN_prefix_loss hf hu (by omega : 1 + 1 ≤ q)
      (hXE.symm ▸ (show v ∈ X from hv)))).trans (Finset.card_union_le _ _)
    rw [hXE] at hc
    change (outN D V v).card ≤ (outN D X v).card + Y.card at hc
    omega
  have hTcap : T.card ≤ 1 := by
    by_contra hn
    have hZcap : Z.card ≤ 1 := by omega
    by_cases hz0 : Z.card = 0
    · have hminA : ∀ x ∈ A, 2 ≤ (outN D A x).card :=
        minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin
          (by change 2 + Z.card ≤ 2; omega)
      have hb := high_two_ball_four hq (hf.mono_set hAV) hminA (hXA hv) hvhighA
      have hc := Finset.card_le_card (ball_subset (D := D) (W := A) (u := v) (k := 4))
      omega
    · have hminA : ∀ x ∈ A, 1 ≤ (outN D A x).card :=
        minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin
          (by change 1 + Z.card ≤ 2; omega)
      have hh := small_one_core_high_count (by omega : 1 ≤ q) (hf.mono_set hAV)
        hminA ⟨v, hXA hv⟩ (by omega) hXA hhighX
      omega
  have hTpos : 1 ≤ T.card := by
    by_contra hn
    have hminW : ∀ x ∈ W, 2 ≤ (outN D W x).card :=
      minOut_prefix_erase hf hu (by omega : 3 + 1 ≤ q) hmin
        (by change 2 + T.card ≤ 2; omega)
    have hb := high_two_ball_four hq (hf.mono_set hWV) hminW (hAW (hXA hv)) hvhighW
    have hc := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := 4))
    omega
  have hTc : T.card = 1 := by omega
  have hb : Ball q 2 := by
    intro F U hF hout x hx
    exact ball_growth q (by omega) F U hF (fun y hy => (hout y hy).ge) x hx (q - 1) (by omega)
  have hd := prefix_deficiency_strict (d := 2) (k := 2) (by omega : 1 ≤ q) hb hf hu
    (by omega) hmin (by decide) (by change T.card < 2; omega)
    (by change (ball D V u 3).card - 1 ≤ q * 2; omega)
  change q * 2 + 2 ≤ (ball D V u 3).card - 1 + Z.card * (2 + T.card - 2) at hd
  rw [hTc] at hd
  have hq5 : q = 5 := by omega
  have hA8 : A.card = 8 := by omega
  have hW10 : W.card = 10 := by omega
  have hminW : ∀ x ∈ W, 1 ≤ (outN D W x).card :=
    minOut_prefix_erase hf hu (by omega : 3 + 1 ≤ q) hmin
      (by change 1 + T.card ≤ 2; omega)
  have hhighA : ∀ x ∈ A, 2 ≤ (outN D W x).card := by
    intro x hx
    exact (hmin x (hAV hx)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 2 + 1 ≤ q) (Finset.mem_of_mem_erase hx)))
  have hfW : QFree D W 5 := by rw [← hq5]; exact hf.mono_set hWV
  exact one_core_ten_eight_high_six_false hfW hminW hAW hhighA hW10 hA8 (hXA hv) (by omega)

theorem high_two_pair_ball_four {D : CH.Digraph} {V : Finset ℕ} {q u v : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 2 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : q + 1 ≤ (outN D V u).card)
    (hv : v ∈ outN D V u) (hhigh : q + 1 ≤ (outN D V v).card) :
    q + 8 ≤ (ball D V u 4).card := by
  classical
  obtain ⟨F, hsub, hdeg, hkeep, hrows⟩ := exists_root_thinning
    (Finset.singleton_subset_iff.mpr hv)
    (by simp only [Finset.card_singleton]; omega : ({v} : Finset ℕ).card ≤ q + 1) hdegree
  have hminF : ∀ x ∈ V, 2 ≤ (outN F V x).card := by
    intro x hx
    by_cases heq : x = u
    · subst x; omega
    · rw [hrows x heq]; exact hmin x hx
  have hvne : v ≠ u := fun heq => loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hv).2)
  have hh : q + 1 ≤ (outN F V v).card := by rw [hrows v hvne]; exact hhigh
  exact (high_two_pair_ball_four_exact hq (qfree_sub hsub hf) hminF hu hdeg
    (hkeep (Finset.mem_singleton_self v)) hh).trans (Finset.card_le_card (ball_sub hsub))

end LeanCH.BR.BRsGen
