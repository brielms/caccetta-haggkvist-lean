import LeanCH.BR.BRThirdBallCap

/-! The radius-three lower bound reaches q=s, with lower-degree order inputs explicit. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem third_ball_ge_on_diagonal {q s : ℕ} (hs : 4 ≤ s) (hsq : s ≤ q)
    (hsize : ∀ d, 2 ≤ d → d < s → ∀ (F : CH.Digraph) (U : Finset ℕ),
      QFree F U q → (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → q * d + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V) :
    3 * s + 1 ≤ (ball D V u 3).card := by
  classical
  by_contra hn
  have hcap : (ball D V u 3).card ≤ 3 * s := by omega
  have htwo := card_ball_two_ge_twice (by omega : 2 ≤ s) (hf.mono_bound hsq) hm hu
  let A := (ball D V u 2).erase u
  let X := outN D V u
  let Z := ball D V u 3 \ ball D V u 2
  have hAV : A ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hXA : X ⊆ A := by
    change outN D V u ⊆ (ball D V u 2).erase u
    rw [← erase_ball_one_eq_outN hf (by omega : 1 ≤ q) hu]
    exact Finset.erase_subset_erase u (ball_mono_radius (by decide))
  have hXc : s ≤ X.card := hm u hu
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hAne : A.Nonempty := hXne.mono hXA
  have hAc : A.card = (ball D V u 2).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  have hpart : Z.card + (ball D V u 2).card = (ball D V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have hZle : Z.card ≤ s - 1 := by omega
  have hhigh : ∀ v ∈ X, s ≤ (outN D A v).card := by
    intro v hv
    exact (hm v (outN_subset hv)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ q)
        ((mem_ball_one hu).mpr (Or.inr hv))))
  by_cases hZsmall : Z.card ≤ 1
  · have hmA : ∀ v ∈ A, s - 1 ≤ (outN D A v).card :=
      minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hm
        (by change (s - 1) + Z.card ≤ s; omega)
    have hh := hsize (s - 1) (by omega) (by omega) D A (hf.mono_set hAV) hmA hAne
    have hmul := Nat.mul_le_mul_left q (show 3 ≤ s - 1 by omega)
    omega
  by_cases hZ1 : Z.card = s - 1
  · have hmA : ∀ v ∈ A, 1 ≤ (outN D A v).card :=
      minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hm
        (by change 1 + Z.card ≤ s; omega)
    have hh := small_one_high_degree_count_of_le (by omega : 3 ≤ s) hsq
      (hf.mono_set hAV) (by omega : A.card ≤ q + s) hmA hXA hhigh
    omega
  by_cases hZ2 : Z.card = s - 2
  · have hmA : ∀ v ∈ A, 2 ≤ (outN D A v).card :=
      minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hm
        (by change 2 + Z.card ≤ s; omega)
    have hh := hsize 2 (by decide) (by omega) D A (hf.mono_set hAV) hmA hAne
    have hAeq : A.card = q * 2 + 1 := by omega
    have hb2 : Ball q 2 := by
      intro G W hG hOut v hv
      exact ball_growth q (by omega) G W hG (fun w hw => (hOut w hw).ge) v hv (q - 1) (by omega)
    have hreg := (dt_reg (by omega : 1 ≤ q) hb2 (hf.mono_set hAV) hmA hAeq).1
    obtain ⟨x, hx⟩ := hXne
    have hlow := hreg x (hXA hx)
    have hhi := hhigh x hx
    omega
  have hd : 3 ≤ s - Z.card := by omega
  have hds : s - Z.card < s := by omega
  have hmA : ∀ v ∈ A, s - Z.card ≤ (outN D A v).card :=
    minOut_prefix_erase hf hu (by omega : 2 + 1 ≤ q) hm
      (by change (s - Z.card) + Z.card ≤ s; omega)
  have hh := hsize (s - Z.card) (by omega) hds D A (hf.mono_set hAV) hmA hAne
  have hmul := Nat.mul_le_mul_left q hd
  omega

end LeanCH.BR.BRsGen
