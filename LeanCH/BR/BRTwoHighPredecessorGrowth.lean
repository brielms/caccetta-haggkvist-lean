import LeanCH.BR.BRHighPredecessorGrowth
import LeanCH.BR.BRMarkedSmallCore
import LeanCH.BR.BRLocalDegreeDrop
import LeanCH.BR.BRRootThinning

/-! Two high heads give two extra radius-four vertices at a degree-three root. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem two_high_predecessor_ball_four {D : CH.Digraph} {V H : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ x ∈ V, 3 ≤ (outN D V x).card)
    (hu : u ∈ V) (hdegree : (outN D V u).card = 3)
    (hHX : H ⊆ outN D V u) (hH : H.card = 2)
    (hhigh : ∀ x ∈ H, 6 ≤ (outN D V x).card) :
    15 ≤ (ball D V u 4).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 4).card ≤ 14 := by omega
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  let U := (ball D V u 2).erase u
  have hXc : X.card = 3 := hdegree
  have hXV : X ⊆ V := outN_subset
  have hHV : H ⊆ V := hHX.trans hXV
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXU : X ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) (hX1 hx)⟩
  have hHU : H ⊆ U := hHX.trans hXU
  have hhighX : ∀ x ∈ X, 3 ≤ (outN D U x).card := by
    intro x hx
    exact (hmin x (hXV hx)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hx)))
  have hhighH : ∀ x ∈ H, 6 ≤ (outN D U x).card := by
    intro x hx
    exact (hhigh x hx).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 (hHX hx))))
  have hUeq : U = X ∪ Y := by
    dsimp only [U]
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by decide) hu]
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hUc : U.card = 3 + Y.card := by rw [hUeq, Finset.card_union_of_disjoint hXY, hXc]
  have hYlo : 5 ≤ Y.card := by
    obtain ⟨z, hz, hsink⟩ := exists_sink (hf.mono_set hHV)
      (Finset.card_pos.mp (by omega)) (by omega)
    have hsub : outN D U z ⊆ (X \ H) ∪ Y := by
      intro v hv
      obtain ⟨hvU, hzv⟩ := mem_outN.mp hv
      rw [hUeq] at hvU
      rcases Finset.mem_union.mp hvU with hvX | hvY
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
          ⟨hvX, fun hvH => hsink v hvH hzv⟩)
      · exact Finset.mem_union_right _ hvY
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hsplit := Finset.card_sdiff_add_card_eq_card hHX
    have hh := hhighH z hz
    change (X \ H).card + H.card = X.card at hsplit
    omega
  have hB1 : (ball D V u 1).card = 4 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by decide) hu, hdegree] at he
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
  have hZlo : 2 ≤ Z.card := by
    by_contra hZsmall
    by_cases hzero : Z.card = 0
    · have hmin3 : ∀ x ∈ U, 3 ≤ (outN D U x).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
          (by change 3 + Z.card ≤ 3; omega)
      have hh := dt_size (by decide : 1 ≤ 5) (BRq3.ball_all 5 (by decide))
        (hf.mono_set hUV) hmin3 (Finset.card_pos.mp (by omega))
      omega
    · have hmin2 : ∀ x ∈ U, 2 ≤ (outN D U x).card :=
        minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
          (by change 2 + Z.card ≤ 3; omega)
      have hd := two_core_high_density_four (by decide : 5 ≤ 5)
        (hf.mono_set hUV) hmin2 hHU hhighH
      have hlo := corB (by decide : 1 ≤ 5) (hf.mono_set hUV) hmin2
        (Finset.card_pos.mp (by omega))
      have hcap : U.card ≤ 12 := by omega
      rw [hH] at hd
      nlinarith
  have hdef : T.card ≤ 2 → 17 ≤ 3 + Y.card + Z.card + Z.card * T.card := by
    intro ht
    have hd := prefix_deficiency_strict (d := 3) (k := 2) (by decide : 1 ≤ 5)
      (BRq3.ball_all 5 (by decide)) hf hu (by decide) hmin (by decide)
      (by change T.card < 3; omega)
      (by change (ball D V u 3).card - 1 ≤ 5 * 3; omega)
    change 17 ≤ (ball D V u 3).card - 1 + Z.card * (3 + T.card - 3) at hd
    simpa using (show 17 ≤ 3 + Y.card + Z.card + Z.card * (3 + T.card - 3) by omega)
  have hcases : (Y.card = 5 ∧ Z.card = 3 ∧ T.card = 2) ∨
      (Y.card = 5 ∧ Z.card = 2 ∧ T.card = 3) := by
    have ht : T.card ≤ 3 := by omega
    rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3) with
      ht0 | ht1 | ht2 | ht3
    · have hh := hdef (by omega); rw [ht0] at hh; omega
    · have hh := hdef (by omega); rw [ht1] at hh; omega
    · have hh := hdef (by omega); rw [ht2] at hh
      exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hYc : Y.card = 5 := hcases.elim (fun h => h.1) (fun h => h.1)
  let C := U \ H
  have hCU : C ⊆ U := Finset.sdiff_subset
  have hCV : C ⊆ V := hCU.trans hUV
  have hCc : C.card = 6 := by
    have hh := Finset.card_sdiff_add_card_eq_card hHU
    change C.card + H.card = U.card at hh
    omega
  have hHC : H ∪ C = U := Finset.union_sdiff_of_subset hHU
  have hreach : ∀ h ∈ H, ∀ c ∈ C, ∃ m, 1 ≤ m ∧ m ≤ 2 ∧ Walk D V h c m := by
    apply small_first_funnel_of_ball (q := 3) (d := 1) (s := 6)
      (by decide) (ball_q_one 3 (by decide)) (hf.mono_bound (by decide))
      (fun v hv => by have := hmin v hv; omega) hHV hCV Finset.disjoint_sdiff
      (by omega) (by omega)
    intro h hh
    rw [hHC]
    exact hhighH h hh
  have hback : ∀ c ∈ C, ∀ h ∈ H, ¬ D c h = true := by
    intro c hc h hh hch
    obtain ⟨m, hm, hm2, w⟩ := hreach h hh c hc
    exact hf h (m + 1) (by omega) (by omega) (w.snoc (hHV hh) hch)
  rcases hcases with ⟨_, hZc, hTc⟩ | ⟨_, hZc, _⟩
  · let M := (ball D V u 3).erase u
    let A := M \ H
    have hUM : U ⊆ M := Finset.erase_subset_erase u (ball_mono_radius (by decide))
    have hHM : H ⊆ M := hHU.trans hUM
    have hMV : M ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hAV : A ⊆ V := Finset.sdiff_subset.trans hMV
    have hCA : C ⊆ A := fun _ hc => Finset.mem_sdiff.mpr
      ⟨hUM (Finset.mem_sdiff.mp hc).1, (Finset.mem_sdiff.mp hc).2⟩
    have hMc : M.card = 11 := by
      have hh := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 3) hu)
      change M.card = _ at hh
      omega
    have hAc : A.card = 9 := by
      have hh := Finset.card_sdiff_add_card_eq_card hHM
      change A.card + H.card = M.card at hh
      omega
    have hZback : ∀ z ∈ Z, ∀ h ∈ H, ¬ D z h = true := by
      intro z hz h hh hzh
      obtain ⟨y, hy2, hyz⟩ := ball_succ_pred hu
        (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
      have hy1 : y ∉ ball D V u 1 := fun h =>
        (Finset.mem_sdiff.mp hz).2 (ball_step h (ball_subset (Finset.mem_sdiff.mp hz).1) hyz)
      have hyC : y ∈ C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨fun heq => hy1 (by rw [heq]; exact self_mem_ball hu), hy2⟩,
          fun hyH => hy1 (hX1 (hHX hyH))⟩
      obtain ⟨m, hm, hm2, w⟩ := hreach h hh y hyC
      exact hf h (m + 1 + 1) (by omega) (by omega)
        ((w.snoc (ball_subset (Finset.mem_sdiff.mp hz).1) hyz).snoc (hHV hh) hzh)
    have hAno : ∀ a ∈ A, ∀ h ∈ H, ¬ D a h = true := by
      intro a ha h hh
      have haM := (Finset.mem_sdiff.mp ha).1
      have heq : M = U ∪ Z := erase_ball_succ_eq_union hu
      rw [heq] at haM
      rcases Finset.mem_union.mp haM with haU | haZ
      · exact hback a (Finset.mem_sdiff.mpr ⟨haU, (Finset.mem_sdiff.mp ha).2⟩) h hh
      · exact hZback a haZ h hh
    have hretain : ∀ a ∈ A, outN D M a ⊆ outN D A a := by
      intro a ha v hv
      obtain ⟨hvM, hav⟩ := mem_outN.mp hv
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨hvM, fun hvH => hAno a ha v hvH hav⟩, hav⟩
    have hminM : ∀ a ∈ M, 1 ≤ (outN D M a).card :=
      minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin
        (by change 1 + T.card ≤ 3; omega)
    have hminA : ∀ a ∈ A, 1 ≤ (outN D A a).card := fun a ha =>
      (hminM a (Finset.mem_sdiff.mp ha).1).trans (Finset.card_le_card (hretain a ha))
    have hhighC : ∀ c ∈ C, 3 ≤ (outN D A c).card := by
      intro c hc
      exact (hmin c (hCV hc)).trans ((Finset.card_le_card
        (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5)
          (Finset.mem_of_mem_erase (hCU hc)))).trans (Finset.card_le_card (hretain c (hCA hc))))
    have hdiff := Finset.card_sdiff_add_card_eq_card hCA
    exact marked_small_one_core_false (by decide : 2 ≤ 5) (hf.mono_set hAV)
      hminA hCA (by omega) hhighC (by omega) (by omega)
  · have hminU : ∀ c ∈ U, 1 ≤ (outN D U c).card :=
      minOut_prefix_erase hf hu (by decide : 2 + 1 ≤ 5) hmin
        (by change 1 + Z.card ≤ 3; omega)
    have hretain : ∀ c ∈ C, outN D U c ⊆ outN D C c := by
      intro c hc v hv
      obtain ⟨hvU, hcv⟩ := mem_outN.mp hv
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨hvU, fun hvH => hback c hc v hvH hcv⟩, hcv⟩
    have hminC : ∀ c ∈ C, 1 ≤ (outN D C c).card := fun c hc =>
      (hminU c (hCU hc)).trans (Finset.card_le_card (hretain c hc))
    have hreg := (dt_reg (by decide : 1 ≤ 5) (ball_q_one 5 (by decide))
      (hf.mono_set hCV) hminC (by omega : C.card = 5 * 1 + 1)).1
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      have hh := Finset.card_sdiff_add_card_eq_card hHX
      change (X \ H).card + H.card = X.card at hh
      omega : 0 < (X \ H).card)
    have hxC : x ∈ C := Finset.mem_sdiff.mpr
      ⟨hXU (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    have hh := (hhighX x (Finset.mem_sdiff.mp hx).1).trans
      (Finset.card_le_card (hretain x hxC))
    have hr := hreg x hxC
    omega

theorem high_predecessor_ball_four_min {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 5) (hmin : ∀ x ∈ V, 3 ≤ (outN D V x).card)
    (hu : u ∈ V) (hv : v ∈ outN D V u) (hhigh : 6 ≤ (outN D V v).card) :
    14 ≤ (ball D V u 4).card := by
  classical
  obtain ⟨F, hsub, hdegree, hkeep, hrows⟩ := exists_root_thinning
    (Finset.singleton_subset_iff.mpr hv) (by simp : ({v} : Finset ℕ).card ≤ 3) (hmin u hu)
  have hminF : ∀ x ∈ V, 3 ≤ (outN F V x).card := by
    intro x hx
    by_cases heq : x = u
    · subst x; omega
    · rw [hrows x heq]; exact hmin x hx
  have hvne : v ≠ u := fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hv).2)
  have hhighF : 6 ≤ (outN F V v).card := by rw [hrows v hvne]; exact hhigh
  exact (high_predecessor_ball_four (qfree_sub hsub hf) hminF hu
    (hkeep (Finset.mem_singleton_self v)) hdegree hhighF).trans
      (Finset.card_le_card (ball_sub hsub))

theorem two_high_predecessor_ball_four_min {D : CH.Digraph} {V H : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ x ∈ V, 3 ≤ (outN D V x).card)
    (hu : u ∈ V) (hHX : H ⊆ outN D V u) (hH : 2 ≤ H.card)
    (hhigh : ∀ x ∈ H, 6 ≤ (outN D V x).card) :
    15 ≤ (ball D V u 4).card := by
  classical
  obtain ⟨J, hJH, hJc⟩ := Finset.exists_subset_card_eq hH
  obtain ⟨F, hsub, hdegree, hkeep, hrows⟩ := exists_root_thinning
    (hJH.trans hHX) (by omega : J.card ≤ 3) (hmin u hu)
  have hminF : ∀ x ∈ V, 3 ≤ (outN F V x).card := by
    intro x hx
    by_cases heq : x = u
    · subst x; omega
    · rw [hrows x heq]; exact hmin x hx
  have hhighF : ∀ x ∈ J, 6 ≤ (outN F V x).card := by
    intro x hx
    have hxne : x ≠ u := fun heq => loopfree hf (by decide) hu
      (heq ▸ (mem_outN.mp (hHX (hJH hx))).2)
    rw [hrows x hxne]
    exact hhigh x (hJH hx)
  exact (two_high_predecessor_ball_four (qfree_sub hsub hf) hminF hu hdegree
    hkeep hJc hhighF).trans (Finset.card_le_card (ball_sub hsub))

end LeanCH.BR.BRsGen
