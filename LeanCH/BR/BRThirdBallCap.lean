import LeanCH.BR.BRSmallHighCycle
import LeanCH.BR.BRPrefixRetention
import LeanCH.BR.BRFiveCutoff

/-! A uniform third-to-second ball cap, with the lower-degree order inputs explicit. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem third_layer_ge_of_third_cap_and_lower_orders {q s : ℕ} (hs : 4 ≤ s) (hsq : s + 1 ≤ q)
    (hsize : ∀ d, 2 ≤ d → d < s → ∀ (F : CH.Digraph) (U : Finset ℕ),
      QFree F U q → (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → q * d + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hu : u ∈ V) (hthird : (ball D V u 3).card ≤ 3 * s + 1) :
    s ≤ (ball D V u 3 \ ball D V u 2).card := by
  classical
  let A := (ball D V u 2).erase u
  let X := outN D V u
  let Z := ball D V u 3 \ ball D V u 2
  have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXA : X ⊆ A := by
    change outN D V u ⊆ (ball D V u 2).erase u
    rw [← erase_ball_one_eq_outN hf (by omega : 1 ≤ q) hu]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXc : s ≤ X.card := hmin u hu
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hAne : A.Nonempty := hXne.mono hXA
  have hAc : A.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hpos : 0 < (ball D V u 2).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  have hpart : Z.card + (ball D V u 2).card = (ball D V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hhigh : ∀ v ∈ X, s ≤ (outN D A v).card := by
    intro v hv
    exact (hmin v (outN_subset hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q)
        ((mem_ball_one hu).mpr (Or.inr hv))))
  have hZge : s ≤ Z.card := by
    by_contra hn
    have hZle : Z.card ≤ s - 1 := by omega
    by_cases hZsmall : Z.card ≤ 1
    · have hmA : ∀ v ∈ A, s - 1 ≤ (outN D A v).card :=
        minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin (by
          change (s - 1) + Z.card ≤ s; omega)
      have hh := hsize (s - 1) (by omega) (by omega) D A (hf.mono_set hAV) hmA hAne
      have hmul := Nat.mul_le_mul_right (s - 1) hsq
      have hs1 : s - 1 + 1 = s := by omega
      have hAupper : A.card ≤ 3 * s := by omega
      nlinarith
    by_cases hZeq : Z.card = s - 1
    · have hmA : ∀ v ∈ A, 1 ≤ (outN D A v).card :=
        minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin (by
          change 1 + Z.card ≤ s; omega)
      have hh := small_one_high_degree_count_of_le (by omega : 3 ≤ s) (by omega : s ≤ q)
        (hf.mono_set hAV) (by omega : A.card ≤ q + s) hmA hXA hhigh
      omega
    · have hd : 2 ≤ s - Z.card := by omega
      have hds : s - Z.card < s := by omega
      have hmA : ∀ v ∈ A, s - Z.card ≤ (outN D A v).card :=
        minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hmin (by
          change (s - Z.card) + Z.card ≤ s; omega)
      have hh := hsize (s - Z.card) hd hds D A (hf.mono_set hAV) hmA hAne
      have hmul := Nat.mul_le_mul_right (s - Z.card) hsq
      have hmul2 := Nat.mul_le_mul_left s hd
      have hsum : (s - Z.card) + Z.card = s := by omega
      have hAupper : A.card ≤ 2 * s + (s - Z.card) := by omega
      nlinarith
  exact hZge

theorem second_ball_cap_of_third_and_lower_orders {q s : ℕ} (hs : 4 ≤ s) (hsq : s + 1 ≤ q)
    (hsize : ∀ d, 2 ≤ d → d < s → ∀ (F : CH.Digraph) (U : Finset ℕ),
      QFree F U q → (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → q * d + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hu : u ∈ V) (hthird : (ball D V u 3).card ≤ 3 * s + 1) :
    (ball D V u 2).card ≤ 2 * s + 1 := by
  have hh := third_layer_ge_of_third_cap_and_lower_orders hs hsq hsize hf hmin hu hthird
  have he := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  omega

theorem third_ball_ge_of_lower_orders {q s : ℕ} (hs : 4 ≤ s) (hsq : s + 1 ≤ q)
    (hsize : ∀ d, 2 ≤ d → d < s → ∀ (F : CH.Digraph) (U : Finset ℕ),
      QFree F U q → (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → q * d + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V) :
    3 * s + 1 ≤ (ball D V u 3).card := by
  by_contra hn
  have hh := third_layer_ge_of_third_cap_and_lower_orders hs hsq hsize hf hmin hu (by omega)
  have htwo := card_ball_two_ge_twice (by omega : 2 ≤ s) (hf.mono_bound (by omega)) hmin hu
  have he := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  omega

end LeanCH.BR.BRsGen
