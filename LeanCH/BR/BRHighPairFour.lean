import LeanCH.BR.BRCyclicRowCap
import LeanCH.BR.BRRootThinning
import LeanCH.BR.BRq4All

/-! A high root with a high head at minimum four forces a larger third ball. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem high_four_pair_ball_three_exact {D : CH.Digraph} {V : Finset ℕ} {q u v : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 4 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = q + 1)
    (hv : v ∈ outN D V u) (hhead : q + 1 ≤ (outN D V v).card) :
    q + 10 ≤ (ball D V u 3).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 3).card ≤ q + 9 := by omega
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let A := (ball D V u 2).erase u
  have hXV : X ⊆ V := outN_subset
  have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXE : (ball D V u 1).erase u = X := erase_ball_one_eq_outN hf (by omega) hu
  have hXA : X ⊆ A := by
    rw [← hXE]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXc : X.card = q + 1 := hdegree
  have hB1 : (ball D V u 1).card = q + 2 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [hXE, hXc] at he
    have hp : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  change Y.card + (ball D V u 1).card = (ball D V u 2).card at h12
  change Z.card + (ball D V u 2).card = (ball D V u 3).card at h23
  have hAc0 : A.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hAc : A.card = q + 1 + Y.card := by omega
  have hYlo : 4 ≤ Y.card := by
    by_contra hn
    have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
      have hh := minOut_prefix_erase (d := 1) hf hu (by omega : 1 + 1 ≤ q) hmin
        (by change 1 + Y.card ≤ 4; omega)
      simpa only [hXE] using hh
    have hr := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
      (hf.mono_set hXV) hminX (by omega : X.card = q * 1 + 1)).1 v hv
    have hc := (Finset.card_le_card (outN_prefix_loss hf hu (by omega : 1 + 1 ≤ q)
      (hXE.symm ▸ (show v ∈ X from hv)))).trans (Finset.card_union_le _ _)
    rw [hXE] at hc
    change (outN D V v).card ≤ (outN D X v).card + Y.card at hc
    omega
  have hZhi : Z.card ≤ 3 := by omega
  have hb := BRq4.ball_all4 q (by omega)
  have hd := prefix_deficiency_strict (d := 4) (k := 1) (by omega : 1 ≤ q) hb hf hu
    (by omega) hmin (by decide) (by change Z.card < 4; omega)
    (by change (ball D V u 2).card - 1 ≤ q * 4; omega)
  change q * 4 + 2 ≤ (ball D V u 2).card - 1 + Y.card * (4 + Z.card - 4) at hd
  have hz : 4 + Z.card - 4 = Z.card := by omega
  rw [hz] at hd
  have hZc : Z.card = 3 := by
    by_contra hn
    have hcases : Z.card = 0 ∨ Z.card = 1 ∨ Z.card = 2 := by omega
    rcases hcases with hc | hc | hc <;> rw [hc] at hd <;> omega
  rw [hZc] at hd
  have hq5 : q = 5 := by omega
  have hYc : Y.card = 4 := by omega
  have hA10 : A.card = 10 := by omega
  have hminA : ∀ x ∈ A, 1 ≤ (outN D A x).card :=
    minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin
      (by change 1 + Z.card ≤ 4; omega)
  have hhighX : ∀ x ∈ X, 4 ≤ (outN D A x).card := by
    intro x hx
    exact (hmin x (hXV hx)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hx)))
  have hvery : q + 1 ≤ (outN D A v).card := hhead.trans (Finset.card_le_card
    (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hv)))
  have hcount := Finset.card_sdiff_add_card_eq_card hXA
  have hcap := row_cap_of_near_deficiency (by omega : 1 ≤ q) (by decide : 1 ≤ 4)
    hb (hf.mono_set hAV) hminA hXA hhighX (by omega)
    (by omega) (hXA hv)
  omega

theorem high_four_pair_ball_three {D : CH.Digraph} {V : Finset ℕ} {q u v : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 4 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : q + 1 ≤ (outN D V u).card)
    (hv : v ∈ outN D V u) (hhead : q + 1 ≤ (outN D V v).card) :
    q + 10 ≤ (ball D V u 3).card := by
  classical
  obtain ⟨F, hsub, hdeg, hkeep, hrows⟩ := exists_root_thinning
    (Finset.singleton_subset_iff.mpr hv)
    (by simp only [Finset.card_singleton]; omega : ({v} : Finset ℕ).card ≤ q + 1) hdegree
  have hminF : ∀ x ∈ V, 4 ≤ (outN F V x).card := by
    intro x hx
    by_cases heq : x = u
    · subst x; omega
    · rw [hrows x heq]; exact hmin x hx
  have hvne : v ≠ u := fun heq => loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hv).2)
  have hh : q + 1 ≤ (outN F V v).card := by rw [hrows v hvne]; exact hhead
  exact (high_four_pair_ball_three_exact hq (qfree_sub hsub hf) hminF hu hdeg
    (hkeep (Finset.mem_singleton_self v)) hh).trans (Finset.card_le_card (ball_sub hsub))

end LeanCH.BR.BRsGen
