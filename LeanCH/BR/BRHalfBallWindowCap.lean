import LeanCH.BR.BRHalfBallWindow
import LeanCH.BR.BRSecondBallBoundary

/-! Boundary regularity in the uniform range q >= 2s-1. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45 Compose.Boundary

theorem window_cap_deficiency_strict {s r q N c t : ℕ}
    (hs : 3 ≤ s) (hr : 3 ≤ r) (hqs : 2 * s - 1 ≤ q) (hqr : 2 * r ≤ q)
    (hN : N + t + 1 ≤ s * r + 1) (hc : c + t + 1 ≤ 2 * s + 1) (ht : t < s) :
    N + c * (s - 1 + t - s) < q * (s - 1) + 1 := by
  by_cases hsr : s ≤ r
  · exact half_radius_cap_deficiency_strict (by omega) hsr hqr hN hc ht
  have hs1 : s - 1 + 1 = s := by omega
  by_cases ht0 : t = 0
  · have hloss : s - 1 + t - s = 0 := by omega
    rw [hloss, Nat.mul_zero, Nat.add_zero]
    have hqmul := Nat.mul_le_mul_right (s - 1) hqr
    have hs2 : s - 2 + 2 = s := by omega
    have hp := Nat.zero_le ((s - 2) * r)
    nlinarith
  · have hloss : s - 1 + t - s = t - 1 := by omega
    have ht1 : t - 1 + 1 = t := by omega
    have hgap : s - t - 1 + t + 1 = s := by omega
    have hgap' : s - t + t = s := by omega
    have hmul := Nat.mul_le_mul_right (t - 1) hc
    have hp := Nat.zero_le ((s - t - 1) * (s - t))
    have hqmul := Nat.mul_le_mul_right (s - 1) (by omega : 2 * s ≤ q + 1)
    have hrmul := Nat.mul_le_mul_left s (by omega : r + 1 ≤ s)
    rw [hloss]
    nlinarith

theorem half_radius_cap_descent_in_window {s q k u : ℕ} (hs : 3 ≤ s) (hk : 1 ≤ k)
    (hqs : 2 * s - 1 ≤ q) (hqr : 2 * (k + 2) ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hcap : (ball D V u (k + 2)).card ≤ s * (k + 2) + 1) :
    (ball D V u (k + 1)).card ≤ s * (k + 1) + 1 := by
  classical
  have hinner := half_ball_in_window hs (by omega) hf hm hu k hk (by omega)
  by_contra hn
  let c := (ball D V u (k + 1) \ ball D V u k).card
  let t := (ball D V u (k + 2) \ ball D V u (k + 1)).card
  have hc : c + (ball D V u k).card = (ball D V u (k + 1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t + (ball D V u (k + 1)).card = (ball D V u (k + 2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have htlt : t < s := by simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *; omega
  have hb := prefix_deficiency_of_size
    (fun _ _ hF hmF hn => order_in_window (s - 1) (by omega) q (by omega) hF hmF hn)
    hf hu (by omega : k + 2 ≤ q) hm (by omega : s - 1 ≤ s) htlt
  have hpos : 0 < (ball D V u (k + 1)).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  have hN : (ball D V u (k + 1)).card - 1 + t + 1 ≤ s * (k + 2) + 1 := by omega
  have hct : c + t + 1 ≤ 2 * s + 1 := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *; omega
  have hh := window_cap_deficiency_strict hs (by omega : 3 ≤ k + 2) hqs hqr hN hct htlt
  change q * (s - 1) + 1 ≤ (ball D V u (k + 1)).card - 1 + c * (s - 1 + t - s) at hb
  omega

theorem second_cap_of_half_cap_in_window {s q k : ℕ}
    (hs : 3 ≤ s) (hq : 2 * s - 1 ≤ q) (hk : 2 ≤ k) (hkq : 2 * k ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hcap : (ball D V u k).card ≤ s * k + 1) :
    (ball D V u 2).card ≤ 2 * s + 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk2 : k = 2
    · subst k; simpa only [Nat.mul_comm s 2] using hcap
    have he2 : k - 2 + 2 = k := by omega
    have he1 : k - 2 + 1 = k - 1 := by omega
    have hp := half_radius_cap_descent_in_window hs (by omega : 1 ≤ k - 2)
      hq (by omega : 2 * (k - 2 + 2) ≤ q) hf hm hu (by simpa only [he2] using hcap)
    apply ih (k - 1) (by omega) (by omega) (by omega)
    simpa only [he1] using hp

theorem boundary_second_cap_in_window {s q : ℕ} (hs : 3 ≤ s) (hq : 2 * s - 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hV : V.card = q * s + 1) :
    ∀ u ∈ V, (ball D V u 2).card ≤ 2 * s + 1 := by
  have hi : ∀ v ∈ V, s * (q / 2) + 1 ≤ (ball D V v (q / 2)).card :=
    fun _ hv => half_ball_in_window hs (by omega) hf hm hv _ (by omega) (by omega)
  have hj : ∀ v ∈ V, s * (q - q / 2) + 1 ≤ (ball D V v (q - q / 2)).card :=
    fun _ hv => half_ball_in_window hs (by omega) hf hm hv _ (by omega) (by omega)
  have he := congrArg (fun a => s * a) (by omega : q / 2 + (q - q / 2) = q)
  simp only [Nat.mul_add] at he
  have heq := two_balls_boundary_cards hf (by omega : q / 2 + (q - q / 2) ≤ q)
    hi hj (by nlinarith)
  intro u hu
  exact second_cap_of_half_cap_in_window hs hq (by omega : 2 ≤ q / 2) (by omega)
    hf hm hu (heq u hu).1.le

/-- Boundary regularity for every degree at cutoff at least twice the degree minus one. -/
theorem br_in_window {s q : ℕ} (hs : 3 ≤ s) (hq : 2 * s - 1 ≤ q) :
    BoundaryRegular q s := by
  apply br_of_second_ball_cap (by omega : 2 ≤ s) (by omega : s ≤ q)
  intro D hf hm
  exact boundary_second_cap_in_window hs hq hf hm (by simp)

end LeanCH.BR.BRsGen
