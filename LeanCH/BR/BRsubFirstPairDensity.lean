import LeanCH.BR.BRsubSmallSecond
import LeanCH.BR.BRHighTwoGrowth
import LeanCH.BR.BRStrictThreeCore

/-! Necessary first-pair inequalities for the remaining degree-six profiles. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- A third layer of size four leaves a degree-two core with every first row high. -/
theorem third_four_first_pair_density (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 4) :
    let a := (outN E V u).card
    let b := (ball E V u 2 \ ball E V u 1).card
    11 * (a + b) + 5 * a ≤ (a + b) * (a + b) := by
  classical
  let U := (ball E V u 2).erase u
  let X := outN E V u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXU : X ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have hminU := minOut_prefix_erase (d := 2) hf hu (by decide : 2 + 1 ≤ 5) hmin
    (by rw [h3])
  have hhigh : ∀ x ∈ X, 6 ≤ (outN E U x).card := by
    intro x hx
    exact (hmin x (outN_subset hx)).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
        ((mem_ball_one hu).mpr (Or.inr hx))))
  have hbound := two_core_high_density (by decide : 4 ≤ 5)
    (hf.mono_set hUV) hminU hXU hhigh
  have hUc : U.card = X.card + (ball E V u 2 \ ball E V u 1).card := by
    have he : U.card = (ball E V u 2).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    have h1 := card_B1 (hf.mono_bound (by decide)) hu
    have h12 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
    change (ball E V u 1).card = X.card + 1 at h1
    omega
  rw [hUc] at hbound
  exact hbound

/-- The radius-four high-row theorem strengthens the first-pair coefficient to seven. -/
theorem third_four_first_pair_density_strong (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 4) :
    let a := (outN E V u).card
    let b := (ball E V u 2 \ ball E V u 1).card
    11 * (a + b) + 7 * a ≤ (a + b) * (a + b) := by
  classical
  let U := (ball E V u 2).erase u
  let X := outN E V u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXU : X ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
        ball_mono_radius (by decide : 1 ≤ 2) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have hminU := minOut_prefix_erase (d := 2) hf hu (by decide : 2 + 1 ≤ 5) hmin
    (by rw [h3])
  have hhigh : ∀ x ∈ X, 6 ≤ (outN E U x).card := by
    intro x hx
    exact (hmin x (outN_subset hx)).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
        ((mem_ball_one hu).mpr (Or.inr hx))))
  have hbound := two_core_high_density_four (by decide : 5 ≤ 5)
    (hf.mono_set hUV) hminU hXU hhigh
  have hUc : U.card = X.card + (ball E V u 2 \ ball E V u 1).card := by
    have he : U.card = (ball E V u 2).card - 1 :=
      Finset.card_erase_of_mem (self_mem_ball hu)
    have h1 := card_B1 (hf.mono_bound (by decide)) hu
    have h12 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
    change (ball E V u 1).card = X.card + 1 at h1
    omega
  rw [hUc] at hbound
  exact hbound

/-- Third layer four requires at least fourteen vertices in the first pair. -/
theorem third_four_first_pair_ge_fourteen (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 4) :
    14 ≤ (outN E V u).card + (ball E V u 2 \ ball E V u 1).card := by
  have hh := third_four_first_pair_density hf hu hmin h3
  dsimp only at hh
  have ha := hmin u hu
  by_contra hn
  let n := (outN E V u).card + (ball E V u 2 \ ball E V u 1).card
  have hn13 : n ≤ 13 := by omega
  have hprod := Nat.mul_le_mul_right n hn13
  change 11 * n + 5 * (outN E V u).card ≤ n * n at hh
  nlinarith

/-- The first three layers (9,5,4) violate the uniform core density inequality. -/
theorem no_nine_five_four (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 9)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 4) : False := by
  have hh := third_four_first_pair_density hf hu hmin h3
  dsimp only at hh
  rw [h1, h2] at hh
  omega

/-- First layer at most eight and second layer five force third layer at least six.
No saturation, ambient order, or deficient-ball hypothesis is required. -/
theorem five_second_small_first_third_ge_six (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card ≤ 8)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5) :
    6 ≤ (ball E V u 3 \ ball E V u 2).card := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  let Z := ball E V u 3 \ ball E V u 2
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hX1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hU2 : (ball E V u 2).erase u = X ∪ Y := by
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by decide) hu]
  have hU3 : (ball E V u 3).erase u = X ∪ Y ∪ Z := by
    rw [show 3 = 2 + 1 by decide, erase_ball_succ_eq_union hu, hU2]
  have hhighX : ∀ x ∈ X, 6 ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hh := outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5) (hX1 hx)
    rw [hU2] at hh
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hh)
  have hhighY : ∀ y ∈ Y, 6 ≤ (outN E (X ∪ Y ∪ Z) y).card := by
    intro y hy
    have hh := outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5)
      (Finset.mem_sdiff.mp hy).1
    rw [hU3] at hh
    exact (hmin y (hYV hy)).trans (Finset.card_le_card hh)
  have hb : Ball 5 2 := by
    intro D W hf hout v hv
    exact ball_growth 5 (by decide) D W hf
      (fun x hx => (hout x hx).ge) v hv 4 (by decide)
  exact small_first_next_layer_card (s := 6) (d := 2) (by decide : 2 ≤ 5) hb hf
    (fun v hv => (by decide : 2 ≤ 6).trans (hmin v hv)) hXV hYV hXY h1
    (by change 2 + (ball E V u 2 \ ball E V u 1).card ≤ 6 + 1; omega)
    (Finset.card_pos.mp (by change 0 < (ball E V u 2 \ ball E V u 1).card; omega))
    (by change (ball E V u 2 \ ball E V u 1).card ≤ 5; omega) hhighX hhighY

/-- A fourth layer of size three retains a degree-three core and all earlier degree-six rows. -/
theorem fourth_three_first_pair_density (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 3) :
    let a := (ball E V u 2).card - 1
    let n := (ball E V u 3).card - 1
    16 * n + 5 * a ≤ n * n := by
  classical
  let U := (ball E V u 3).erase u
  let H := (ball E V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
      ball_mono_radius (by decide : 2 ≤ 3) (Finset.mem_of_mem_erase hv)⟩
  have hminU := minOut_prefix_erase (d := 3) hf hu (by decide : 3 + 1 ≤ 5) hmin
    (by rw [h4])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN E U v).card := by
    intro v hv
    exact (hmin v (ball_subset (Finset.mem_of_mem_erase hv))).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5)
        (Finset.mem_of_mem_erase hv)))
  have hh := three_core_six_density (hf.mono_set hUV) hminU hHU hhigh
  have hUc : U.card = (ball E V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball E V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  rwa [hUc, hHc] at hh

/-- A small nonempty third layer makes the retained-core inequality strict. -/
theorem fourth_three_first_pair_density_strict (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 3)
    (h3pos : 0 < (ball E V u 3 \ ball E V u 2).card)
    (h3small : (ball E V u 3 \ ball E V u 2).card ≤ 5) :
    let a := (ball E V u 2).card - 1
    let n := (ball E V u 3).card - 1
    16 * n + 5 * a + 1 ≤ n * n := by
  classical
  let U := (ball E V u 3).erase u
  let H := (ball E V u 2).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hHU : H ⊆ U := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
      ball_mono_radius (by decide : 2 ≤ 3) (Finset.mem_of_mem_erase hv)⟩
  have hminU := minOut_prefix_erase (d := 3) hf hu (by decide : 3 + 1 ≤ 5) hmin
    (by rw [h4])
  have hhigh : ∀ v ∈ H, 6 ≤ (outN E U v).card := by
    intro v hv
    exact (hmin v (ball_subset (Finset.mem_of_mem_erase hv))).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5)
        (Finset.mem_of_mem_erase hv)))
  have hdiff : U \ H = ball E V u 3 \ ball E V u 2 := by
    ext v
    simp only [U, H, Finset.mem_sdiff, Finset.mem_erase]
    have hroot : v = u → v ∈ ball E V u 2 := by
      intro heq
      rw [heq]
      exact self_mem_ball hu
    tauto
  have hh := three_core_six_density_strict (hf.mono_set hUV) hminU hHU hhigh
    (by rw [hdiff]; exact Finset.card_pos.mp h3pos) (by rw [hdiff]; exact h3small)
  have hUc : U.card = (ball E V u 3).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hHc : H.card = (ball E V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  rwa [hUc, hHc] at hh

/-- With at least twelve vertices in the first pair, fourth layer three forces full size 24. -/
theorem fourth_three_deficient_exact (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hpair : 12 ≤ (outN E V u).card + (ball E V u 2 \ ball E V u 1).card)
    (hb4 : (ball E V u 4).card ≤ 24)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 3) :
    (ball E V u 4).card = 24 := by
  have hd := fourth_three_first_pair_density hf hu hmin h4
  dsimp only at hd
  have h1 := card_B1 (hf.mono_bound (by decide)) hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  have ha : 12 ≤ (ball E V u 2).card - 1 := by omega
  by_contra hn
  have hN : (ball E V u 3).card - 1 ≤ 19 := by omega
  have hprod := Nat.mul_le_mul_right ((ball E V u 3).card - 1) hN
  nlinarith

/-- Third layer four is impossible after first pair (10,5), for every host order. -/
theorem no_ten_five_four (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 10)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 4) : False := by
  have hh := third_four_first_pair_density_strong hf hu hmin h3
  dsimp only at hh
  rw [h1, h2] at hh
  omega

/-- No deficient degree-six root has last two layers (4,3), at any host order. -/
theorem no_four_three_deficient (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hb4 : (ball E V u 4).card ≤ 24)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 4)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 3) : False := by
  have hd := fourth_three_first_pair_density_strict hf hu hmin h4
    (by omega) (by omega)
  dsimp only at hd
  let n := (ball E V u 3).card - 1
  let a := (ball E V u 2).card - 1
  have h1 := card_B1 (hf.mono_bound (by decide)) hu
  have hminu := hmin u hu
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 2 ≤ 3))
  have h34 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  have hna : n = a + 4 := by dsimp only [n,a]; omega
  have hnlo : 10 ≤ n := by dsimp only [n]; omega
  have hn20 : n ≤ 20 := by dsimp only [n]; omega
  change 16 * n + 5 * a + 1 ≤ n * n at hd
  have hp20 := Nat.mul_le_mul_right n hn20
  have hn19 : n ≤ 19 := by nlinarith
  have hp19 := Nat.mul_le_mul_right n hn19
  nlinarith

end LeanCH.BR.BRsub
