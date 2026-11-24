import LeanCH.BR.BRThirdBallCap
import LeanCH.BR.BRDeficiencyCompletion

/-! A fourth-to-second ball cap with explicit lower-degree order inputs. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem second_ball_cap_of_fourth_and_lower_orders {q s : ℕ} (hs : 4 ≤ s) (hsq : s + 3 ≤ q)
    (hsize : ∀ d, 2 ≤ d → d < s → ∀ (F : CH.Digraph) (U : Finset ℕ),
      QFree F U q → (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → q * d + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hu : u ∈ V) (hcap : (ball D V u 4).card ≤ 4 * s + 1) :
    (ball D V u 2).card ≤ 2 * s + 1 := by
  classical
  by_contra hn
  let c := (ball D V u 3 \ ball D V u 2).card
  let t := (ball D V u 4 \ ball D V u 3).card
  let N := (ball D V u 3).card - 1
  have hc : c + (ball D V u 2).card = (ball D V u 3).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have ht : t + (ball D V u 3).card = (ball D V u 4).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have htlt : t < s := by
    by_contra htge
    have hh := second_ball_cap_of_third_and_lower_orders hs (by omega) hsize hf hm hu (by omega)
    omega
  have hb := prefix_deficiency_of_size (hsize (s - 1) (by omega) (by omega))
    (k := 2) hf hu (by omega) hm (by omega : s - 1 ≤ s) htlt
  change q * (s - 1) + 1 ≤ N + c * (s - 1 + t - s) at hb
  have hN : N + t ≤ 4 * s := by dsimp only [N]; omega
  have hct : c + t + 1 ≤ 2 * s := by omega
  have hs1 : s - 1 + 1 = s := by omega
  have hqmul := Nat.mul_le_mul_right (s - 1) hsq
  by_cases ht0 : t = 0
  · have hloss : s - 1 + t - s = 0 := by omega
    rw [hloss, Nat.mul_zero, Nat.add_zero] at hb
    have hsq4 := Nat.mul_le_mul_left s hs
    nlinarith only [hb, hN, hs1, hqmul, hsq4, hs, ht0]
  · have hloss : s - 1 + t - s = t - 1 := by omega
    have ht1 : t - 1 + 1 = t := by omega
    have hgap : s - t - 1 + t + 1 = s := by omega
    have hgap' : s - t + t = s := by omega
    have hmul := Nat.mul_le_mul_right (t - 1) hct
    have hp := Nat.zero_le ((s - t - 1) * (s - t))
    rw [hloss] at hb
    nlinarith only [hb, hN, hs1, ht1, hgap, hgap', hmul, hp, hqmul, hs]

end LeanCH.BR.BRsGen
