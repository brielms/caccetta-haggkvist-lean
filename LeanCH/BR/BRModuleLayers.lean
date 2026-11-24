import LeanCH.BR.BRsubLocalSix

/-! Uniform incoming modules occupy a single distance layer from an outside root. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

theorem module_parent_uniform {D : CH.Digraph} {V M Y : Finset ℕ} {q s : ℕ}
    (hqs : q + 1 = s) (hq : 2 ≤ q) (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hYV : Y ⊆ V) (hY : Y.card = s - 1)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = s) (hcyc : OutEq 1 D M) :
    ∀ p ∈ V, p ∉ M → ∀ x ∈ M, ∀ y ∈ M, D p x = true → D p y = true := by
  intro p hp hpM x hx y hy hpx
  have hpin : p ∈ inN D V x := mem_inN.mpr ⟨hp, hpx⟩
  rw [lemmaM hqs hq hf hsat hMV hYV hY hhead hout hcyc hx] at hpin
  have hpW : p ∈ WM D V M Y q := by
    rcases Finset.mem_union.mp hpin with h | h
    · exact (hpM (mem_inN.mp h).1).elim
    · exact h
  have hpy : p ∈ inN D V y := by
    rw [lemmaM hqs hq hf hsat hMV hYV hY hhead hout hcyc hy]
    exact Finset.mem_union_right _ hpW
  exact (mem_inN.mp hpy).2

/-- An outside root reaches either all or none of a full module by each radius. -/
theorem uniform_incoming_ball_flat {D : CH.Digraph} {V M : Finset ℕ} {u : ℕ}
    (hu : u ∈ V) (huM : u ∉ M) (hMV : M ⊆ V)
    (hp : ∀ p ∈ V, p ∉ M → ∀ x ∈ M, ∀ y ∈ M, D p x = true → D p y = true) :
    ∀ k, ∀ x ∈ M, x ∈ ball D V u k → M ⊆ ball D V u k := by
  intro k
  induction k with
  | zero =>
    intro x hx hxb
    have he := eq_of_mem_ball_zero hxb
    subst x
    exact (huM hx).elim
  | succ k ih =>
    intro x hx hxb y hy
    by_cases hprev : x ∈ ball D V u k
    · exact ball_mono_radius (by omega) (ih x hx hprev hy)
    · obtain ⟨p, hpb, hpx⟩ := ball_succ_pred hu hxb hprev
      by_cases hpM : p ∈ M
      · exact ball_mono_radius (by omega) (ih p hpM hpb hy)
      · exact ball_step hpb (hMV hy) (hp p (ball_subset hpb) hpM x hx y hy hpx)

/-- A nonempty module inside a ball lies in one entire distance layer. -/
theorem uniform_incoming_one_layer {D : CH.Digraph} {V M : Finset ℕ} {u k : ℕ}
    (hu : u ∈ V) (huM : u ∉ M) (hMV : M ⊆ V) (hn : M.Nonempty)
    (hp : ∀ p ∈ V, p ∉ M → ∀ x ∈ M, ∀ y ∈ M, D p x = true → D p y = true)
    (hMk : M ⊆ ball D V u k) :
    ∃ j, j + 1 ≤ k ∧ M ⊆ ball D V u (j + 1) \ ball D V u j := by
  induction k with
  | zero =>
    obtain ⟨x, hx⟩ := hn
    have he := eq_of_mem_ball_zero (hMk hx)
    subst x
    exact (huM hx).elim
  | succ k ih =>
    by_cases hprev : M ⊆ ball D V u k
    · obtain ⟨j, hj, hlayer⟩ := ih hprev
      exact ⟨j, by omega, hlayer⟩
    · refine ⟨k, by omega, ?_⟩
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨hMk hx, ?_⟩
      intro hxb
      exact hprev (uniform_incoming_ball_flat hu huM hMV hp k x hx hxb)

theorem tight_six_local_one_layer {D : CH.Digraph} {V M Y : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V)
    (hMsub : M ⊆ (ball D V u 3).erase u) (hM : M.card = 6)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) (hcyc : OutEq 1 D M) :
    M ⊆ ball D V u 1 \ ball D V u 0 ∨
      M ⊆ ball D V u 2 \ ball D V u 1 ∨ M ⊆ ball D V u 3 \ ball D V u 2 := by
  have hMV : M ⊆ V := hMsub.trans ((Finset.erase_subset _ _).trans ball_subset)
  have huM : u ∉ M := fun h => (Finset.mem_erase.mp (hMsub h)).1 rfl
  have hp := module_parent_uniform (by decide : 5 + 1 = 6) (by decide) hf hsat
    hMV hYV hY hhead hout hcyc
  obtain ⟨j, hj, hlayer⟩ := uniform_incoming_one_layer hu huM hMV
    (Finset.card_pos.mp (by omega)) hp (hMsub.trans (Finset.erase_subset _ _))
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact Or.inl hlayer
  · exact Or.inr (Or.inl hlayer)
  · exact Or.inr (Or.inr hlayer)

/-- Two distinct rows cannot both head every other vertex in a digon-free set. -/
theorem almost_order_rows_at_most_one {D : CH.Digraph} {V H : Finset ℕ} {s : ℕ}
    (hf : QFree D V 2) (hHV : H ⊆ V) (hV : V.card ≤ s + 1)
    (hh : ∀ x ∈ H, s ≤ (outN D V x).card) : H.card ≤ 1 := by
  classical
  have hfull : ∀ x ∈ H, outN D V x = V.erase x := by
    intro x hx
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      exact Finset.mem_erase.mpr ⟨fun heq => loopfree hf (by decide) (hHV hx)
        (heq ▸ (mem_outN.mp hy).2), outN_subset hy⟩
    · rw [Finset.card_erase_of_mem (hHV hx)]
      have := hh x hx
      omega
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hne
  have hxy : D x y = true := (mem_outN.mp (by
    rw [hfull x hx]; exact Finset.mem_erase.mpr ⟨Ne.symm hne, hHV hy⟩)).2
  have hyx : D y x = true := (mem_outN.mp (by
    rw [hfull y hy]; exact Finset.mem_erase.mpr ⟨hne, hHV hx⟩)).2
  exact digonfree hf (by decide) (hHV hx) (hHV hy) hxy hyx

/-- At a first-two-ball size of at most14, a tight six-module cannot occupy layer two. -/
theorem no_tight_six_in_small_second_layer {D : CH.Digraph} {V M Y : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hB2 : (ball D V u 2).card ≤ 14)
    (hMsub : M ⊆ ball D V u 2 \ ball D V u 1) (hM : M.card = 6)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) (hcyc : OutEq 1 D M) : False := by
  classical
  let X := outN D V u
  let A := (ball D V u 2).erase u
  let S := A \ M
  let W := WM D V M Y 5
  let P := X \ W
  have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hMA : M ⊆ A := by
    intro x hx
    obtain ⟨hx2, hx1⟩ := Finset.mem_sdiff.mp (hMsub hx)
    exact Finset.mem_erase.mpr ⟨fun heq => hx1 (heq.symm ▸ self_mem_ball hu), hx2⟩
  have hMV := hMA.trans hAV
  have hXA : X ⊆ A := by
    rw [show X = (ball D V u 1).erase u from (erase_ball_one_eq_outN hf (by decide) hu).symm]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXM : ∀ x ∈ X, x ∉ M := by
    intro x hx hxM
    exact (Finset.mem_sdiff.mp (hMsub hxM)).2 ((mem_ball_one hu).mpr (Or.inr hx))
  have hSV : S ⊆ V := Finset.sdiff_subset.trans hAV
  have hPS : P ⊆ S := by
    intro x hx
    have hxX := (Finset.mem_sdiff.mp hx).1
    exact Finset.mem_sdiff.mpr ⟨hXA hxX, hXM x hxX⟩
  have hSc : S.card ≤ 7 := by
    have hAc : A.card = (ball D V u 2).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
    have hpart : S.card + M.card = A.card := Finset.card_sdiff_add_card_eq_card hMA
    omega
  have hretain : ∀ x ∈ P, outN D V x ⊆ outN D S x := by
    intro x hx z hz
    obtain ⟨hxX, hxW⟩ := Finset.mem_sdiff.mp hx
    have hzA := (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
      ((mem_ball_one hu).mpr (Or.inr hxX)) hz)).1
    refine mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨hzA, ?_⟩, (mem_outN.mp hz).2⟩
    intro hzM
    have hxin : x ∈ inN D V z := mem_inN.mpr ⟨outN_subset hxX, (mem_outN.mp hz).2⟩
    rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hf hsat hMV hYV hY hhead hout hcyc hzM] at hxin
    rcases Finset.mem_union.mp hxin with h | h
    · exact hXM x hxX (mem_inN.mp h).1
    · exact hxW h
  have hPc := almost_order_rows_at_most_one ((hf.mono_set hSV).mono_bound (by decide)) hPS hSc
    (fun x hx => (hm x (hSV (hPS hx))).trans (Finset.card_le_card (hretain x hx)))
  have hWc : W.card ≤ 4 := tightModule_WM_le_four hf hV hm hMV hYV hM hY hhead
  have hsub : X ⊆ P ∪ W := by
    intro x hx
    by_cases hw : x ∈ W
    · exact Finset.mem_union_right _ hw
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hw⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hr : 6 ≤ X.card := hm u hu
  omega

theorem tight_six_first_ball_two_cap {D : CH.Digraph} {V M Y : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hMX : M = outN D V u) (hM : M.card = 6)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) (hcyc : OutEq 1 D M) :
    (ball D V u 2).card ≤ 12 := by
  have hMV : M ⊆ V := hMX ▸ outN_subset
  have hB1 : ball D V u 1 ⊆ insert u (M ∪ Y) := by
    intro x hx
    rcases (mem_ball_one hu).mp hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hMX.symm ▸ hx))
  have hB2 : ball D V u 2 ⊆ insert u (M ∪ Y) := by
    intro x hx
    by_cases hx1 : x ∈ ball D V u 1
    · exact hB1 hx1
    · obtain ⟨p, hp, hpx⟩ := ball_succ_pred hu hx hx1
      rcases (mem_ball_one hu).mp hp with rfl | hp
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (hMX.symm ▸ mem_outN.mpr ⟨ball_subset hx, hpx⟩))
      · have hpM : p ∈ M := hMX.symm ▸ hp
        have hh := out_sub (by decide : 5 + 1 = 6) (by decide) hf hMV hYV hY
          hhead hout hcyc hpM (ball_subset hx) hpx
        exact Finset.mem_insert_of_mem (Finset.mem_union.mpr hh)
  have hc := (Finset.card_le_card hB2).trans (Finset.card_insert_le _ _)
  have hcU := Finset.card_union_le M Y
  omega

theorem remaining_six_small_ball_cards {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23) :
    (ball D V u 2).card = 14 ∧ (ball D V u 3 \ ball D V u 2).card = 5 ∧
      (ball D V u 4 \ ball D V u 3).card = 4 ∧ (ball D V u 4).card = 23 ∧
      (outN D V u).card ≤ 7 := by
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hpair := hp.first_pair_bounds
  have h2 := hp.second_ge_six
  have h3 := hp.third_ge_four
  have h4 := hp.fourth_ge_three
  have ht4 : 4 ≤ (ball D V u 4 \ ball D V u 3).card := by
    by_contra hn
    have := hp.fourth_three_exact (by omega)
    omega
  have ht5 : 5 ≤ (ball D V u 3 \ ball D V u 2).card := by
    by_contra hn
    have := hp.third_four_pair_fifteen (by omega)
    omega
  omega

/-- A local tight module in a small surviving profile must sit inside the seven-vertex first layer. -/
theorem tight_six_small_profile_position {D : CH.Digraph} {V M Y : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hMsub : M ⊆ (ball D V u 3).erase u) (hM : M.card = 6)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) (hcyc : OutEq 1 D M) :
    M ⊆ outN D V u ∧ (outN D V u).card = 7 ∧
      (ball D V u 2 \ ball D V u 1).card = 6 := by
  obtain ⟨hB2, h3, h4, hB4, ha⟩ := remaining_six_small_ball_cards hf hu hp hsmall
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  rcases tight_six_local_one_layer hf hsat hu hMsub hM hYV hY hhead hout hcyc with h1 | h2 | h3M
  · have hMX : M ⊆ outN D V u := by
      intro x hx
      rcases (mem_ball_one hu).mp (Finset.mem_sdiff.mp (h1 hx)).1 with rfl | h
      · exact ((Finset.mem_sdiff.mp (h1 hx)).2 (self_mem_ball hu)).elim
      · exact h
    have hc := Finset.card_le_card hMX
    have hnot : (outN D V u).card ≠ 6 := by
      intro heq
      have hMeq := Finset.eq_of_subset_of_card_le hMX (by omega)
      have hh := tight_six_first_ball_two_cap hf hu hMeq hM hYV hY hhead hout hcyc
      omega
    exact ⟨hMX, by omega, by omega⟩
  · exact (no_tight_six_in_small_second_layer hf hsat hu hV hm (by omega)
      h2 hM hYV hY hhead hout hcyc).elim
  · have hc := Finset.card_le_card h3M
    omega

/-- The current profile exclusions already give a uniform two-unit ball deficit cap. -/
theorem six_boundary_ball_four_ge_twenty_three {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) : 23 ≤ (ball D V u 4).card := by
  by_cases ht : TightRoot D V 6 u
  · have := tight_six_ball_four_ge_twenty_four hf hsat hV hm hu ht
    omega
  · by_contra hn
    have hp := remaining_six_profile hf hsat hV hm hu ht (by omega)
    have hh := remaining_six_small_ball_cards hf hu hp (by omega)
    omega

theorem six_boundary_in_le_eight {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) : (inN D V u).card ≤ 8 := by
  have hb := six_boundary_ball_four_ge_twenty_three hf hsat hu hV hm
  have hc := card_inN_of_satQ (by decide : 1 ≤ 5) hf hsat hu
  change (inN D V u).card + (ball D V u 4).card = V.card at hc
  omega

/-- Any outside parent of a tight six-module has deficit at most one. -/
theorem tight_six_parent_deficit_le_one {D : CH.Digraph} {V M Y : Finset ℕ} {p : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hMV : M ⊆ V) (hM : M.card = 6)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) (hcyc : OutEq 1 D M)
    (hp : p ∈ WM D V M Y 5) :
    (inN D V p).card ≤ (outN D V p).card + 1 := by
  have hpV := (mem_WM.mp hp).1
  have hi := six_boundary_in_le_eight hf hsat hpV hV hm
  have ho := hm p hpV
  by_cases hhigh : 7 ≤ (outN D V p).card
  · omega
  have heq : (outN D V p).card = 6 := by omega
  have hMX : M = outN D V p := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have hpin : p ∈ inN D V x := by
        rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hf hsat hMV hYV hY hhead hout hcyc hx]
        exact Finset.mem_union_right _ hp
      exact mem_outN.mpr ⟨hMV hx, (mem_inN.mp hpin).2⟩
    · omega
  have hb2 := tight_six_first_ball_two_cap hf hpV hMX hM hYV hY hhead hout hcyc
  have hb4 : 24 ≤ (ball D V p 4).card := by
    by_cases ht : TightRoot D V 6 p
    · exact tight_six_ball_four_ge_twenty_four hf hsat hV hm hpV ht
    · by_contra hn
      have hh := remaining_six_small_ball_cards hf hpV
        (remaining_six_profile hf hsat hV hm hpV ht (by omega)) (by omega)
      omega
  have hc := card_inN_of_satQ (by decide : 1 ≤ 5) hf hsat hpV
  change (inN D V p).card + (ball D V p 4).card = V.card at hc
  omega

/-- A module's six units of surplus cover all outside-parent deficits with two to spare. -/
theorem tight_six_module_discharge {D : CH.Digraph} {V M Y : Finset ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hMV : M ⊆ V) (hM : M.card = 6)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, D x y = true)
    (hout : ∀ x ∈ M, (outN D V x).card = 6) (hcyc : OutEq 1 D M) :
    (∑ p ∈ WM D V M Y 5, ((inN D V p).card - (outN D V p).card)) + 2 ≤
      ∑ x ∈ M, ((outN D V x).card - (inN D V x).card) := by
  have hparent : ∀ p ∈ WM D V M Y 5,
      (inN D V p).card - (outN D V p).card ≤ 1 := by
    intro p hp
    have := tight_six_parent_deficit_le_one hf hsat hV hm hMV hM hYV hY hhead hout hcyc hp
    omega
  have hinternal := (dt_reg (by decide : 1 ≤ 5) (ball_q_one 5 (by decide))
    (hf.mono_set hMV) (fun x hx => (hcyc x hx).ge) (by omega)).2
  have hgain : ∀ x ∈ M, 1 ≤ (outN D V x).card - (inN D V x).card := by
    intro x hx
    have hi := tightModule_in_le_five hf hsat hV hm hMV hYV hM hY hhead hout
      (fun v hv => ⟨hcyc v hv, hinternal v hv⟩) hx
    have ho := hout x hx
    omega
  have hsP := Finset.sum_le_sum hparent
  have hsM := Finset.sum_le_sum hgain
  simp only [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_one] at hsP hsM
  have hw := tightModule_WM_le_four hf hV hm hMV hYV hM hY hhead
  omega

end LeanCH.BR.BRsub
