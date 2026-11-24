import LeanCH.BR.BRStrictPrefixDeficiency
import LeanCH.BR.BRRootThinning

/-! A degree-(q+1) head supplies the sharp q+7 radius-four bound at minimum two. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem full_head_boundary_other_rows {D : CH.Digraph} {V : Finset ℕ} {q v : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hV : V.card ≤ q + 2)
    (hmin : ∀ x ∈ V, 1 ≤ (outN D V x).card) (hv : v ∈ V)
    (hhigh : q + 1 ≤ (outN D V v).card) :
    ∀ x ∈ V, x ≠ v → (outN D V x).card = 1 := by
  classical
  let C := V.erase v
  have hCV : C ⊆ V := Finset.erase_subset _ _
  have hCc : C.card = V.card - 1 := Finset.card_erase_of_mem hv
  have hsub : outN D V v ⊆ C := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by omega) hv (heq ▸ (mem_outN.mp hx).2), (mem_outN.mp hx).1⟩
  have hcount := Finset.card_le_card hsub
  have hCeq : C.card = q + 1 := by omega
  have hfull : outN D V v = C := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hretain : ∀ x ∈ C, outN D V x = outN D C x := by
    intro x hx
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨hyV, hxy⟩ := mem_outN.mp hy
      have hvx : D v x = true := (mem_outN.mp (hfull.symm ▸ hx)).2
      exact mem_outN.mpr ⟨Finset.mem_erase.mpr
        ⟨fun heq => digonfree hf hq hv (hCV hx) hvx (heq ▸ hxy), hyV⟩, hxy⟩
    · exact outN_mono hCV x
  have hminC : ∀ x ∈ C, 1 ≤ (outN D C x).card := by
    intro x hx
    rw [← hretain x hx]
    exact hmin x (hCV hx)
  have hreg := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
    (hf.mono_set hCV) hminC (by omega : C.card = q * 1 + 1)).1
  intro x hx hxv
  have hxC : x ∈ C := Finset.mem_erase.mpr ⟨hxv, hx⟩
  rw [hretain x hxC]
  exact hreg x hxC

theorem high_two_predecessor_ball_four_exact {D : CH.Digraph} {V : Finset ℕ} {q u v : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 2 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = 2)
    (hv : v ∈ outN D V u) (hhigh : q + 1 ≤ (outN D V v).card) :
    q + 7 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 4).card ≤ q + 6 := by omega
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  let U := (ball D V u 2).erase u
  have hXc : X.card = 2 := hdegree
  have hXV : X ⊆ V := outN_subset
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXU : X ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) (hX1 hx)⟩
  have hhighX : ∀ x ∈ X, 2 ≤ (outN D U x).card := by
    intro x hx
    exact (hmin x (hXV hx)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hx)))
  have hhighV : q + 1 ≤ (outN D U v).card := hhigh.trans (Finset.card_le_card
    (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hv)))
  have hUeq : U = X ∪ Y := by
    dsimp only [U]
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by omega) hu]
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hUc : U.card = 2 + Y.card := by rw [hUeq, Finset.card_union_of_disjoint hXY, hXc]
  have hYlo : q ≤ Y.card := by
    have hsub : outN D U v ⊆ X.erase v ∪ Y := by
      intro x hx
      obtain ⟨hxU, hvx⟩ := mem_outN.mp hx
      rw [hUeq] at hxU
      rcases Finset.mem_union.mp hxU with hxX | hxY
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨fun heq => loopfree hf (by omega) (hXV hv) (heq ▸ hvx), hxX⟩)
      · exact Finset.mem_union_right _ hxY
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem hv, hXc] at hc
    omega
  have hB1 : (ball D V u 1).card = 3 := by
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
  have hb : Ball q 2 := by
    intro F W hF hout w hw
    exact ball_growth q (by omega) F W hF (fun x hx => (hout x hx).ge) w hw (q - 1) (by omega)
  have hdef : T.card ≤ 1 → 2 * q + 2 ≤ 2 + Y.card + Z.card + Z.card * T.card := by
    intro ht
    have hd := prefix_deficiency_strict (d := 2) (k := 2) (by omega : 1 ≤ q) hb hf hu
      (by omega) hmin (by decide) (by change T.card < 2; omega)
      (by change (ball D V u 3).card - 1 ≤ q * 2; omega)
    change q * 2 + 2 ≤ (ball D V u 3).card - 1 + Z.card * (2 + T.card - 2) at hd
    simpa using (show 2 * q + 2 ≤ 2 + Y.card + Z.card + Z.card * (2 + T.card - 2) by omega)
  have hTlo : 2 ≤ T.card := by
    by_contra hn
    have hd := hdef (by omega)
    rcases (by omega : T.card = 0 ∨ T.card = 1) with ht0 | ht1
    · rw [ht0] at hd; omega
    · rw [ht1] at hd; omega
  have hZlo : 1 ≤ Z.card := by
    by_contra hn
    have hmin2 : ∀ x ∈ U, 2 ≤ (outN D U x).card :=
      minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin
        (by change 2 + Z.card ≤ 2; omega)
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set hUV) hmin2 ⟨v, hXU hv⟩
    omega
  have hZc : Z.card = 1 := by omega
  have hYc : Y.card = q := by omega
  have hmin1 : ∀ x ∈ U, 1 ≤ (outN D U x).card :=
    minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin
      (by change 1 + Z.card ≤ 2; omega)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hv, hXc]
    decide : 0 < (X.erase v).card)
  have hxX := (Finset.mem_erase.mp hx).2
  have hh := full_head_boundary_other_rows (by omega : 2 ≤ q) (hf.mono_set hUV)
    (by omega) hmin1 (hXU hv) hhighV x (hXU hxX) (Finset.mem_erase.mp hx).1
  have hd := hhighX x hxX
  omega

theorem high_two_predecessor_ball_four {D : CH.Digraph} {V : Finset ℕ} {q u v : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ x ∈ V, 2 ≤ (outN D V x).card)
    (hu : u ∈ V) (hv : v ∈ outN D V u) (hhigh : q + 1 ≤ (outN D V v).card) :
    q + 7 ≤ (ball D V u 4).card := by
  classical
  obtain ⟨F, hsub, hdegree, hkeep, hrows⟩ := exists_root_thinning
    (Finset.singleton_subset_iff.mpr hv) (by simp : ({v} : Finset ℕ).card ≤ 2) (hmin u hu)
  have hminF : ∀ x ∈ V, 2 ≤ (outN F V x).card := by
    intro x hx
    by_cases heq : x = u
    · subst x; omega
    · rw [hrows x heq]; exact hmin x hx
  have hvne : v ≠ u := fun heq => loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hv).2)
  have hhighF : q + 1 ≤ (outN F V v).card := by rw [hrows v hvne]; exact hhigh
  exact (high_two_predecessor_ball_four_exact hq (qfree_sub hsub hf) hminF hu hdegree
    (hkeep (Finset.mem_singleton_self v)) hhighF).trans (Finset.card_le_card (ball_sub hsub))

end LeanCH.BR.BRsGen
