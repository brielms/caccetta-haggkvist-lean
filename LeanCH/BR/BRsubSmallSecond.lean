import LeanCH.BR.BRsubFourthLayer
import LeanCH.BR.BRHighThreeCore
import LeanCH.BR.BRPrefixRetention
import LeanCH.BR.BRLocalDegreeDrop

/-! Reduction of deficient degree-six balls with a small second layer. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- A deficient degree-six ball has at least four third-layer vertices. -/
theorem third_layer_ge_four (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hb4 : (ball E V u 4).card ≤ 24) :
    4 ≤ (ball E V u 3 \ ball E V u 2).card := by
  classical
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  let U := (ball E V u 2).erase u
  let X := outN E V u
  have hXc : 6 ≤ X.card := hmin u hu
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXU : X ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have hUc : U.card + (ball E V u 3 \ ball E V u 2).card ≤ 20 := by
    have he : U.card = (ball E V u 2).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
    have h23 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
    have h34 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
    have hpos : 0 < (ball E V u 2).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  have hne : U.Nonempty := ⟨x, hXU hx⟩
  by_contra hn
  by_cases hsmall : (ball E V u 3 \ ball E V u 2).card ≤ 2
  · have hminU := minOut_prefix_erase (d := 4) hf hu (by decide : 2 + 1 ≤ 5) hmin
      (by change 4 + (ball E V u 3 \ ball E V u 2).card ≤ 6; omega)
    have hsize := dt_size (by decide : 1 ≤ 5) (BRq4.ball_all4 5 (by decide))
      (hf.mono_set hUV) hminU hne
    change 5 * 4 + 1 ≤ U.card at hsize
    omega
  · have hminU := minOut_prefix_erase (d := 3) hf hu (by decide : 2 + 1 ≤ 5) hmin
      (by change 3 + (ball E V u 3 \ ball E V u 2).card ≤ 6; omega)
    obtain ⟨H, hHX, hH⟩ := Finset.exists_subset_card_eq hXc
    apply three_core_high_rows_false (s := 6) (by decide) (hf.mono_set hUV)
      (by omega) hminU (hHX.trans hXU) hH
    intro v hv
    have hv1 : v ∈ ball E V u 1 := (mem_ball_one hu).mpr (Or.inr (hHX hv))
    exact (hmin v (outN_subset (hHX hv))).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) hv1))

/-- Four starting vertices reach at least fifteen vertices within two steps. -/
theorem card_ballSet_two_ge_fifteen_of_four {Y : Finset ℕ}
    (hf : QFree E V 5) (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hYV : Y ⊆ V) (hY : Y.card = 4) : 15 ≤ (ballSet E V Y 2).card := by
  classical
  have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have h1 : 10 ≤ (ballSet E V Y 1).card := by
    obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV) hne (by omega)
    have hsub : outN E V y ⊆ ballSet E V Y 1 \ Y := by
      intro v hv
      exact Finset.mem_sdiff.mpr
        ⟨outN_subset_ballSet_succ (subset_ballSet (k := 0) hYV hy) hv,
          fun hvY => hsink v hvY (mem_outN.mp hv).2⟩
    have hc := Finset.card_sdiff_add_card_eq_card (subset_ballSet (k := 1) (E := E) hYV)
    have hh := (hmin y (hYV hy)).trans (Finset.card_le_card hsub)
    omega
  by_contra hn
  let l := (ballSet E V Y 2 \ ballSet E V Y 1).card
  have hsum : l + (ballSet E V Y 1).card = (ballSet E V Y 2).card :=
    Finset.card_sdiff_add_card_eq_card (ballSet_mono (by decide))
  have htest (c : ℕ) (hc : 1 ≤ c) (hc4 : c ≤ 4) (h : c + l ≤ 6) :
      5 * c + 2 ≤ (ballSet E V Y 1).card :=
    ballSet_deletion (k := 0) hc hc4 hf hYV hne (fun v hv => hmin v (ballSet_subset hv)) h
  by_cases hl : l ≤ 3
  · have := htest 3 (by decide) (by decide) (by omega)
    omega
  · have := htest 2 (by decide) (by decide) (by omega)
    omega

/-- A deficient ball with second layer at most four has exactly profile (12,4,4,3). -/
theorem small_second_deficient_profile (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hb4 : (ball E V u 4).card ≤ 24)
    (hsmall : (ball E V u 2 \ ball E V u 1).card ≤ 4) :
    (outN E V u).card = 12 ∧
    (ball E V u 2 \ ball E V u 1).card = 4 ∧
    (ball E V u 3 \ ball E V u 2).card = 4 ∧
    (ball E V u 4 \ ball E V u 3).card = 3 ∧ (ball E V u 4).card = 24 := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hX1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have h3 := third_layer_ge_four hf hu hmin hb4
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hbudget : X.card + Y.card ≤ 16 := by
    change (ball E V u 1).card = X.card + 1 at hB1
    change Y.card + (ball E V u 1).card = (ball E V u 2).card at h12
    omega
  have hminX (d : ℕ) (hd : d + Y.card ≤ 6) : ∀ x ∈ X, d ≤ (outN E X x).card := by
    have h := minOut_prefix_erase (d := d) hf hu (by decide : 1 + 1 ≤ 5) hmin hd
    rw [erase_ball_one_eq_outN hf (by decide) hu] at h
    exact h
  have hXne : X.Nonempty := Finset.card_pos.mp ((by decide : 0 < 6).trans_le (hmin u hu))
  have hsize (d : ℕ) (hd : 1 ≤ d) (hd4 : d ≤ 4) (hloss : d + Y.card ≤ 6) :
      5 * d + 1 ≤ X.card :=
    dt_size (by decide) (ball_five_small hd hd4) (hf.mono_set hXV) (hminX d hloss) hXne
  have hY4 : Y.card = 4 := by
    change Y.card ≤ 4 at hsmall
    by_contra hn
    by_cases h2 : Y.card ≤ 2
    · have := hsize 4 (by decide) (by decide) (by omega)
      omega
    · have := hsize 3 (by decide) (by decide) (by omega)
      omega
  have hXlo := hsize 2 (by decide) (by decide) (by omega)
  have hX12 : X.card = 12 := by
    by_contra hn
    have hX11 : X.card = 11 := by omega
    have hreg := (dt_reg (by decide : 1 ≤ 5) (ball_five_small (c := 2) (by decide) (by decide))
      (hf.mono_set hXV) (hminX 2 (by omega)) hX11).1
    have hhead : ∀ x ∈ X, ∀ y ∈ Y, E x y = true := by
      intro x hx
      have hsub : outN E V x ⊆ outN E (X ∪ Y) x := by
        intro v hv
        have hxE : x ∈ (ball E V u 1).erase u := by
          rw [erase_ball_one_eq_outN hf (by decide) hu]; exact hx
        have hh := outN_prefix_loss hf hu (by decide : 1 + 1 ≤ 5) hxE hv
        rw [erase_ball_one_eq_outN hf (by decide) hu] at hh
        refine mem_outN.mpr ⟨?_, (mem_outN.mp hv).2⟩
        rcases Finset.mem_union.mp hh with hvX | hvY
        · exact Finset.mem_union_left _ (mem_outN.mp hvX).1
        · exact Finset.mem_union_right _ hvY
      have hh := (hmin x (hXV hx)).trans (Finset.card_le_card hsub)
      rw [card_outN_union hXY, hreg x hx] at hh
      have heq : outN E Y x = Y := Finset.eq_of_subset_of_card_le outN_subset (by omega)
      intro y hy
      exact (mem_outN.mp (heq.symm ▸ hy)).2
    have h15 := card_ballSet_two_ge_fifteen_of_four hf hmin hYV hY4
    have heq := second_layer_set_ball hf hu hhead (by decide : 2 ≤ 2)
    change ballSet E V Y 2 = ball E V u 4 \ ball E V u 1 at heq
    rw [heq] at h15
    have h14 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 4))
    change X.card = 11 at hX11
    change (ball E V u 1).card = X.card + 1 at hB1
    omega
  change (ball E V u 1).card = X.card + 1 at hB1
  change Y.card + (ball E V u 1).card = (ball E V u 2).card at h12
  exact ⟨hX12, hY4, by omega, by omega, by omega⟩

/-- Every deficient degree-six radius-four ball has second layer at least five. -/
theorem second_layer_ge_five (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hb4 : (ball E V u 4).card ≤ 24) :
    5 ≤ (ball E V u 2 \ ball E V u 1).card := by
  classical
  by_contra hn
  obtain ⟨h1, h2, h3, _, _⟩ := small_second_deficient_profile hf hu hmin hb4 (by omega)
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  let Z := ball E V u 3 \ ball E V u 2
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hX1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hsplit2 : ∀ v ∈ ball E V u 2, v ≠ u → v ∈ X ∪ Y := by
    intro v hv hvu
    by_cases hv1 : v ∈ ball E V u 1
    · rcases (mem_ball_one hu).mp hv1 with h | h
      · exact (hvu h).elim
      · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hv1⟩)
  have hsplit3 : ∀ v ∈ ball E V u 3, v ≠ u → v ∈ X ∪ Y ∪ Z := by
    intro v hv hvu
    by_cases hv2 : v ∈ ball E V u 2
    · exact Finset.mem_union_left _ (hsplit2 v hv2 hvu)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hv2⟩)
  have hhighX : ∀ x ∈ X, 6 ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    apply (hmin x (hXV hx)).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvE, hxv⟩ := mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hx) hv)
    exact mem_outN.mpr ⟨hsplit2 v (Finset.mem_of_mem_erase hvE) (Finset.mem_erase.mp hvE).1, hxv⟩
  have hhighY : ∀ y ∈ Y, 6 ≤ (outN E (X ∪ Y ∪ Z) y).card := by
    intro y hy
    apply (hmin y (hYV hy)).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvE, hyv⟩ := mem_outN.mp
      (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5) (Finset.mem_sdiff.mp hy).1 hv)
    exact mem_outN.mpr ⟨hsplit3 v (Finset.mem_of_mem_erase hvE) (Finset.mem_erase.mp hvE).1, hyv⟩
  have hlarge := small_first_next_layer_card (s := 6) (d := 3) (by decide : 2 ≤ 5)
    (BRq3.ball_all 5 (by decide)) hf (fun v hv => (by decide : 3 ≤ 6).trans (hmin v hv))
    hXV hYV hXY (by change (outN E V u).card ≤ 3 * (5 - 1); omega)
    (by change 3 + (ball E V u 2 \ ball E V u 1).card ≤ 6 + 1; omega)
    (Finset.card_pos.mp (by change 0 < (ball E V u 2 \ ball E V u 1).card; omega))
    (by change (ball E V u 2 \ ball E V u 1).card ≤ 5; omega) hhighX hhighY
  change 6 ≤ (ball E V u 3 \ ball E V u 2).card at hlarge
  omega

/-- The first pair (s,s-1) is already a tight root, uniformly in the subdiagonal parameter. -/
theorem tight_of_first_pair {s : ℕ} (hs : 3 ≤ s) (hf : QFree E V (s - 1)) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, s ≤ (outN E V v).card)
    (h1 : (outN E V u).card = s)
    (h2 : (ball E V u 2 \ ball E V u 1).card = s - 1) : TightRoot E V s u := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  have hXV : X ⊆ V := outN_subset
  have hX1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hU2 : (ball E V u 2).erase u = X ∪ Y := by
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by omega) hu]
  have hretain : ∀ x ∈ X, outN E V x ⊆ outN E (X ∪ Y) x := by
    intro x hx
    have hh := outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ s - 1) (hX1 hx)
    rwa [hU2] at hh
  have hhigh : ∀ x ∈ X, s ≤ (outN E (X ∪ Y) x).card := fun x hx =>
    (hmin x (hXV hx)).trans (Finset.card_le_card (hretain x hx))
  have hminX : ∀ x ∈ X, 1 ≤ (outN E X x).card := by
    intro x hx
    have hh := hhigh x hx
    rw [card_outN_union hXY] at hh
    have hc := Finset.card_le_card (outN_subset (D := E) (W := Y) (y := x))
    change Y.card = s - 1 at h2
    omega
  have hreg := dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega))
    (hf.mono_set hXV) hminX (by change (outN E V u).card = (s - 1) * 1 + 1; omega)
  refine ⟨h1, h2, ?_⟩
  intro x hx
  have hhi := hhigh x hx
  rw [card_outN_union hXY, hreg.1 x hx] at hhi
  have hYc : Y.card = s - 1 := h2
  have heq : outN E Y x = Y := Finset.eq_of_subset_of_card_le outN_subset (by omega)
  have hout : (outN E V x).card = s := by
    have hc := Finset.card_le_card (hretain x hx)
    rw [card_outN_union hXY, hreg.1 x hx, heq, hYc] at hc
    have hh := hmin x (hXV hx)
    omega
  refine ⟨hout, hreg.1 x hx, hreg.2 x hx, ?_⟩
  intro y hy hy1
  have hyY : y ∈ Y := Finset.mem_sdiff.mpr ⟨hy, hy1⟩
  exact (mem_outN.mp (heq.symm ▸ hyY)).2

end LeanCH.BR.BRsub
