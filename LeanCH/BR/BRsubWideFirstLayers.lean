import LeanCH.BR.BRWideFirstFunnel
import LeanCH.BR.BRsubSmallSecond

/-! Wider first layers: the improved funnel closes the degree-six (8,5) branch. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- The uniform first-set funnel applied to actual BFS layers. -/
theorem first_layers_funnel {q L : ℕ} (hL : 2 ≤ L) (hLq : L + 1 ≤ q)
    (hf : QFree E V q) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, q + 1 ≤ (outN E V v).card)
    (h1 : (outN E V u).card ≤ q + L)
    (h2 : (ball E V u 2 \ ball E V u 1).card = q) :
    ∀ x ∈ outN E V u, ∀ y ∈ ball E V u 2 \ ball E V u 1,
      ∃ m, 1 ≤ m ∧ m ≤ L ∧ Walk E V x y m := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hX1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hU2 : (ball E V u 2).erase u = X ∪ Y := by
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by omega) hu]
  have hhigh : ∀ x ∈ X, q + 1 ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hh := outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q) (hX1 hx)
    rw [hU2] at hh
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hh)
  exact wide_first_funnel hL hLq hf
    (fun v hv => (by omega : 2 ≤ q + 1).trans (hmin v hv))
    hXV hYV hXY h1 h2 hhigh

/-- A first layer of size at most q+L followed by a q-set forces a full third layer. -/
theorem third_layer_ge_of_first_layers {q L : ℕ} (hL : 2 ≤ L) (hLq : L + 1 ≤ q)
    (hf : QFree E V q) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, q + 1 ≤ (outN E V v).card)
    (h1 : (outN E V u).card ≤ q + L)
    (h2 : (ball E V u 2 \ ball E V u 1).card = q) :
    q + 1 ≤ (ball E V u 3 \ ball E V u 2).card := by
  classical
  let Y := ball E V u 2 \ ball E V u 1
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hfunnel := first_layers_funnel hL hLq hf hu hmin h1 h2
  obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV)
    (Finset.card_pos.mp (by change 0 < (ball E V u 2 \ ball E V u 1).card; omega)) h2.le
  have hsub : outN E V y ⊆ ball E V u 3 \ ball E V u 2 := by
    intro v hv
    obtain ⟨hvV, hyv⟩ := mem_outN.mp hv
    refine Finset.mem_sdiff.mpr ⟨ball_step (Finset.mem_sdiff.mp hy).1 hvV hyv, ?_⟩
    intro hv2
    by_cases hv1 : v ∈ ball E V u 1
    · rcases (mem_ball_one hu).mp hv1 with hvu | hvX
      · exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) (hvu ▸ hyv)
      · obtain ⟨m, hm, hmL, w⟩ := hfunnel v hvX y hy
        exact hf v (m + 1) (by omega) (by omega) (w.snoc hvV hyv)
    · exact hsink v (Finset.mem_sdiff.mpr ⟨hv2, hv1⟩) hyv
  exact (hmin y (hYV hy)).trans (Finset.card_le_card hsub)

/-- The whole (8,5) first-pair branch is impossible under the deficient-ball hypothesis.
No saturation or ambient order assumption is used. -/
theorem no_eight_five_deficient (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 8)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5)
    (hb4 : (ball E V u 4).card ≤ 24) : False := by
  classical
  have hfun := first_layers_funnel (L := 3) (by decide) (by decide) hf hu hmin h1.le h2
  have h3 := third_layer_ge_of_first_layers (L := 3) (by decide) (by decide) hf hu hmin h1.le h2
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  let Y := ball E V u 2 \ ball E V u 1
  let A := ball E V u 3 \ ball E V u 1
  let T := ball E V u 4 \ ball E V u 3
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hAV : A ⊆ V := fun _ hv => ball_subset (Finset.mem_sdiff.mp hv).1
  have hYA : Y ⊆ A := by
    intro y hy
    exact Finset.mem_sdiff.mpr
      ⟨ball_mono_radius (by decide : 2 ≤ 3) (Finset.mem_sdiff.mp hy).1,
        (Finset.mem_sdiff.mp hy).2⟩
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hTc : T.card ≤ 4 := by change (ball E V u 4 \ ball E V u 3).card ≤ 4; omega
  have hAc : A.card ≤ 12 := by
    dsimp only [A]
    rw [Finset.card_sdiff_of_subset (ball_mono_radius (by decide : 1 ≤ 3))]
    omega
  have hreach : ∀ x ∈ outN E V u, ∀ v ∈ A,
      ∃ m, 1 ≤ m ∧ m ≤ 4 ∧ Walk E V x v m := by
    intro x hx v hv
    by_cases hv2 : v ∈ ball E V u 2
    · obtain ⟨m, hm, hm3, w⟩ := hfun x hx v
        (Finset.mem_sdiff.mpr ⟨hv2, (Finset.mem_sdiff.mp hv).2⟩)
      exact ⟨m, hm, by omega, w⟩
    · obtain ⟨y, hy, hyv⟩ := ball_succ_pred hu (Finset.mem_sdiff.mp hv).1 hv2
      have hy1 : y ∉ ball E V u 1 := by
        intro hy1
        exact hv2 (ball_step hy1 (hAV hv) hyv)
      obtain ⟨m, hm, hm3, w⟩ := hfun x hx y (Finset.mem_sdiff.mpr ⟨hy, hy1⟩)
      exact ⟨m + 1, by omega, by omega, w.snoc (hAV hv) hyv⟩
  have hnoB1 : ∀ v ∈ A, ∀ w ∈ ball E V u 1, ¬ E v w = true := by
    intro v hv w hw hvw
    rcases (mem_ball_one hu).mp hw with hwu | hwX
    · exact no_back_arc hf hu (Finset.mem_sdiff.mp hv).1 (by decide) (hwu ▸ hvw)
    · obtain ⟨m, hm, hm4, path⟩ := hreach w hwX v hv
      exact hf w (m + 1) (by omega) (by omega) (path.snoc (outN_subset hwX) hvw)
  have hminA : ∀ v ∈ A, 2 ≤ (outN E A v).card := by
    intro v hv
    have hsub : outN E V v ⊆ outN E A v ∪ T := by
      intro w hw
      obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
      by_cases hw3 : w ∈ ball E V u 3
      · exact Finset.mem_union_left _ (mem_outN.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hw3, fun hw1 => hnoB1 v hv w hw1 hvw⟩, hvw⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨ball_step (Finset.mem_sdiff.mp hv).1 hwV hvw, hw3⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin v (hAV hv)
    omega
  have hhighY : ∀ y ∈ Y, 5 ≤ (outN E A y).card := by
    intro y hy
    have hsub : outN E V y ⊆ outN E A y := by
      intro w hw
      obtain ⟨hwV, hyw⟩ := mem_outN.mp hw
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr
        ⟨ball_step (Finset.mem_sdiff.mp hy).1 hwV hyw,
          fun hw1 => hnoB1 y (hYA hy) w hw1 hyw⟩, hyw⟩
    have hh := (hmin y (hYV hy)).trans (Finset.card_le_card hsub)
    omega
  apply two_core_many_high_false (q := 5) (by decide) (hf.mono_set hAV) hAc hminA hYA
    (by change A.card < 3 * (ball E V u 2 \ ball E V u 1).card; omega) hhighY

theorem eight_five_ball_four_ge_twenty_five (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 8)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5) :
    25 ≤ (ball E V u 4).card := by
  by_contra hn
  exact no_eight_five_deficient hf hu hmin h1 h2 (by omega)

/-- The next first pair has only one deficient numerical profile left. -/
theorem nine_five_deficient_profile (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 9)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5)
    (hb4 : (ball E V u 4).card ≤ 24) :
    (ball E V u 3 \ ball E V u 2).card = 6 ∧
    (ball E V u 4 \ ball E V u 3).card = 3 ∧ (ball E V u 4).card = 24 := by
  have h3 := third_layer_ge_of_first_layers (L := 4) (by decide) (by decide) hf hu hmin h1.le h2
  have h4 := fourth_layer_ge_three hf hu hmin hb4
  have hB1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  omega

end LeanCH.BR.BRsub
