import LeanCH.BR.BRPartialFunnel
import LeanCH.BR.BRsubWideFirstLayers

/-! Parent multiplicity closes the first-pair (9,5) branch. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

theorem no_nine_five_deficient (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 9)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5)
    (hb4 : (ball E V u 4).card ≤ 24) : False := by
  classical
  obtain ⟨h3, h4, _⟩ := nine_five_deficient_profile hf hu hmin h1 h2 hb4
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  let Z := ball E V u 3 \ ball E V u 2
  let T := ball E V u 4 \ ball E V u 3
  have hXc : X.card = 9 := h1
  have hYc : Y.card = 5 := h2
  have hZc : Z.card = 6 := h3
  have hTc : T.card = 3 := h4
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hZV : Z ⊆ V := fun _ hz => ball_subset (Finset.mem_sdiff.mp hz).1
  have hX1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hY2 : Y ⊆ ball E V u 2 := fun _ hy => (Finset.mem_sdiff.mp hy).1
  have hZ3 : Z ⊆ ball E V u 3 := fun _ hz => (Finset.mem_sdiff.mp hz).1
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hYZ : Disjoint Y Z := Finset.disjoint_left.mpr
    (fun _ hy hz => (Finset.mem_sdiff.mp hz).2 (hY2 hy))
  have hU2 : (ball E V u 2).erase u = X ∪ Y := by
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by decide) hu]
  have hhighX : ∀ x ∈ X, 6 ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hh := outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hx)
    rw [hU2] at hh
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hh)
  have hfun := first_layers_funnel (L := 4) (by decide) (by decide) hf hu hmin h1.le h2
  have hnoYX : ∀ y ∈ Y, ∀ x ∈ X, ¬ E y x = true := by
    intro y hy x hx hyx
    obtain ⟨m, hm, hm4, w⟩ := hfun x hx y hy
    exact hf x (m + 1) (by omega) (by omega) (w.snoc (hXV hx) hyx)
  have hheadsY : ∀ y ∈ Y, outN E V y ⊆ outN E (Y ∪ Z) y := by
    intro y hy v hv
    obtain ⟨hvV, hyv⟩ := mem_outN.mp hv
    have hv3 := ball_step (hY2 hy) hvV hyv
    have hv1 : v ∉ ball E V u 1 := by
      intro hv1
      rcases (mem_ball_one hu).mp hv1 with hvu | hvX
      · exact no_back_arc hf hu (hY2 hy) (by decide) (hvu ▸ hyv)
      · exact hnoYX y hy v hvX hyv
    refine mem_outN.mpr ⟨?_, hyv⟩
    by_cases hv2 : v ∈ ball E V u 2
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv2, hv1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv3, hv2⟩)
  have hhighY : ∀ y ∈ Y, 6 ≤ (outN E (Y ∪ Z) y).card := by
    intro y hy
    exact (hmin y (hYV hy)).trans (Finset.card_le_card (hheadsY y hy))
  obtain ⟨a, ha, hsink⟩ := exists_sink (hf.mono_set hYV)
    (Finset.card_pos.mp (by omega : 0 < Y.card)) (by omega : Y.card ≤ 5)
  have haZ : ∀ z ∈ Z, E a z = true := by
    have hzero : outN E Y a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hsink v (mem_outN.mp hv).1 (mem_outN.mp hv).2
    have hh := hhighY a ha
    rw [card_outN_union hYZ, hzero, Finset.card_empty, zero_add] at hh
    have heq : outN E Z a = Z := Finset.eq_of_subset_of_card_le outN_subset (by omega)
    intro z hz
    exact (mem_outN.mp (heq.symm ▸ hz)).2
  have hYerase : (Y.erase a).card = 4 := by rw [Finset.card_erase_of_mem ha, hYc]
  obtain ⟨b, hb, hsinkB⟩ := exists_sink
    (hf.mono_set (Finset.erase_subset a Y |>.trans hYV))
    (Finset.card_pos.mp (by omega : 0 < (Y.erase a).card))
    (by omega : (Y.erase a).card ≤ 5)
  have hbY : b ∈ Y := (Finset.mem_erase.mp hb).2
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  let G := outN E Z b
  have hGZ : G ⊆ Z := outN_subset
  have hGc : 5 ≤ G.card := by
    have hsub : outN E Y b ⊆ {a} := by
      intro v hv
      apply Finset.mem_singleton.mpr
      by_contra hne
      exact hsinkB v (Finset.mem_erase.mpr ⟨hne, (mem_outN.mp hv).1⟩)
        (mem_outN.mp hv).2
    have hc := Finset.card_le_card hsub
    have hh := hhighY b hbY
    rw [card_outN_union hYZ] at hh
    have hc' : (outN E Y b).card ≤ 1 := by simpa using hc
    change 5 ≤ (outN E Z b).card
    omega
  have hbad : (Z \ G).card ≤ 1 := by
    have hh := Finset.card_sdiff_add_card_eq_card hGZ
    omega
  have hnoGX : ∀ z ∈ G, ∀ x ∈ X, ¬ E z x = true := by
    intro z hz
    have hpairY : ({a, b} : Finset ℕ) ⊆ Y := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hbY
    have hpaircard : ({a, b} : Finset ℕ).card = 2 := by simp [Ne.symm hba]
    apply no_return_of_many_parents (k := 4) (d := 3) (s := 6)
      (by decide) (by decide) (BRq3.ball_all 4 (by decide)) hf
      (fun v hv => (by decide : 3 ≤ 6).trans (hmin v hv)) hXV hYV hXY
      (by omega) hhighX hpairY (hZV (hGZ hz))
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact haZ z (hGZ hz)
      · exact (mem_outN.mp hz).2
    · omega
  let A := Y ∪ G
  have hAV : A ⊆ V := Finset.union_subset hYV (hGZ.trans hZV)
  have hYA : Y ⊆ A := Finset.subset_union_left
  have hAc : A.card ≤ 11 := by
    have hh := Finset.card_union_le Y G
    have hg := Finset.card_le_card hGZ
    change (Y ∪ G).card ≤ 11
    omega
  have hA3 : A ⊆ ball E V u 3 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hy | hg
    · exact ball_mono_radius (by decide : 2 ≤ 3) (hY2 hy)
    · exact hZ3 (hGZ hg)
  have hnoA1 : ∀ v ∈ A, ∀ w ∈ ball E V u 1, ¬ E v w = true := by
    intro v hv w hw hvw
    rcases (mem_ball_one hu).mp hw with hwu | hwX
    · exact no_back_arc hf hu (hA3 hv) (by decide) (hwu ▸ hvw)
    · rcases Finset.mem_union.mp hv with hy | hg
      · exact hnoYX v hy w hwX hvw
      · exact hnoGX v hg w hwX hvw
  have hminA : ∀ v ∈ A, 2 ≤ (outN E A v).card := by
    intro v hv
    have hsub : outN E V v ⊆ (outN E A v ∪ (Z \ G)) ∪ T := by
      intro w hw
      obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
      by_cases hw3 : w ∈ ball E V u 3
      · apply Finset.mem_union_left
        by_cases hwA : w ∈ A
        · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hwA, hvw⟩)
        · apply Finset.mem_union_right
          have hw2 : w ∉ ball E V u 2 := by
            intro hw2
            by_cases hw1 : w ∈ ball E V u 1
            · exact hnoA1 v hv w hw1 hvw
            · exact hwA (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw2, hw1⟩))
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hw3, hw2⟩,
            fun hg => hwA (Finset.mem_union_right _ hg)⟩
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨ball_step (hA3 hv) hwV hvw, hw3⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc' := Finset.card_union_le (outN E A v) (Z \ G)
    have hh := hmin v (hAV hv)
    omega
  have hhighA : ∀ y ∈ Y, 5 ≤ (outN E A y).card := by
    intro y hy
    have hsub : outN E V y ⊆ outN E A y ∪ (Z \ G) := by
      intro w hw
      obtain ⟨hwYZ, hyw⟩ := mem_outN.mp (hheadsY y hy hw)
      by_cases hwA : w ∈ A
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hwA, hyw⟩)
      · apply Finset.mem_union_right
        rcases Finset.mem_union.mp hwYZ with hwY | hwZ
        · exact False.elim (hwA (Finset.mem_union_left _ hwY))
        · exact Finset.mem_sdiff.mpr ⟨hwZ, fun hg => hwA (Finset.mem_union_right _ hg)⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin y (hYV hy)
    omega
  exact two_core_many_high_false (q := 5) (by decide) (hf.mono_set hAV)
    (by omega) hminA hYA (by omega) hhighA

theorem nine_five_ball_four_ge_twenty_five (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 9)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5) :
    25 ≤ (ball E V u 4).card := by
  by_contra hn
  exact no_nine_five_deficient hf hu hmin h1 h2 (by omega)

end LeanCH.BR.BRsub
