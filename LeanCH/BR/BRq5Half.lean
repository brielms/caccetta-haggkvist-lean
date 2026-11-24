import LeanCH.BR.BRHalfBallGrowth
import LeanCH.BR.BR75

/-! Uniform degree-five half-radius growth, from the checked radii three and four. -/

namespace LeanCH.BR.BRq5
open BRq2 BRq3 BRq4 BR45 BRsGen

theorem half_ball_five : ∀ k, 3 ≤ k → ∀ {D : CH.Digraph} {V : Finset ℕ} {u : ℕ},
    QFree D V (2 * k - 1) → (∀ v ∈ V, 5 ≤ (outN D V v).card) → u ∈ V →
    5 * k + 1 ≤ (ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk D V u hf hm hu
    by_cases hk3 : k = 3
    · subst k
      exact card_ball_three_ge_sixteen hf hm hu
    by_cases hk4 : k = 4
    · subst k
      exact BR75.card_ball_four_seven_free hf hm hu
    have hk5 : 5 ≤ k := by omega
    have hinner := ih (k - 2) (by omega) (by omega)
      (hf.mono_bound (by omega)) hm hu
    have hprev := ih (k - 1) (by omega) (by omega)
      (hf.mono_bound (by omega)) hm hu
    have hk2 : k - 2 + 2 = k := by omega
    have hk1 : k - 2 + 1 = k - 1 := by omega
    have hh := half_radius_growth_step (s := 5) (k := k - 2) (by decide)
      (by omega) (by omega : 2 * (k - 2 + 2) - 1 ≤ 2 * k - 1)
      (fun _ _ hF hmF hn => dt_size (by omega)
        (ball_all4 (2 * k - 1) (by omega)) hF hmF hn)
      hf hm hu hinner (by simpa only [hk1] using hprev)
    simpa only [hk2] using hh

theorem second_ball_cap_of_fourth {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 8) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hu : u ∈ V) (hcap : (ball D V u 4).card ≤ 21) :
    (ball D V u 2).card ≤ 11 := by
  classical
  by_contra hn
  let c := (ball D V u 3 \ ball D V u 2).card
  let t := (ball D V u 4 \ ball D V u 3).card
  have hc : c + (ball D V u 2).card = (ball D V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have ht : t + (ball D V u 3).card = (ball D V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have htlt : t < 5 := by
    by_contra hnlt
    have hh := BR65.second_ball_cap_of_third (hf.mono_bound (by decide)) hm hu (by omega)
    omega
  have hb := prefix_deficiency_of_ball (k := 2) (by decide : 1 ≤ 8)
    (ball_all4 8 (by decide)) hf hu (by decide) hm (by decide : 4 ≤ 5) htlt
  change 33 ≤ (ball D V u 3).card - 1 + c * (4 + t - 5) at hb
  have hct : c + t ≤ 9 := by omega
  interval_cases t <;> simp_all <;> omega

end LeanCH.BR.BRq5
