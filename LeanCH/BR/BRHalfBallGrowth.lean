import LeanCH.BR.BRDeficiencyCompletion

/-! Prefix deficiency propagates half-radius growth once the radius reaches the degree. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem half_radius_deficiency_strict {s r q N c t : ℕ}
    (hs : 2 ≤ s) (hr : s ≤ r) (hq : 2 * r - 1 ≤ q)
    (hN : N + t + 1 ≤ s * r) (hc : c + t + 1 ≤ 2 * s) (ht : t < s) :
    N + c * (s - 1 + t - s) < q * (s - 1) + 1 := by
  have hs1 : s - 1 + 1 = s := by omega
  have hq' : 2 * r ≤ q + 1 := by omega
  have hqmul := Nat.mul_le_mul_right (s - 1) hq'
  by_cases ht0 : t = 0
  · have hloss : s - 1 + t - s = 0 := by omega
    rw [hloss, Nat.mul_zero, Nat.add_zero]
    have hs2 : s - 2 + 2 = s := by omega
    have hr1 : r - 1 + 1 = r := by omega
    have hp := Nat.zero_le ((s - 2) * (r - 1))
    nlinarith
  · have hloss : s - 1 + t - s = t - 1 := by omega
    have ht1 : t - 1 + 1 = t := by omega
    have hgap : s - t - 1 + t + 1 = s := by omega
    have hmul := Nat.mul_le_mul_right (t - 1) hc
    have hp := Nat.zero_le ((s - t - 1) * (s - t))
    have hgap' : s - t + t = s := by omega
    have hs2 : s - 2 + 2 = s := by omega
    have hrad : r - s + s = r := by omega
    have hprod := Nat.zero_le ((r - s) * (s - 2))
    rw [hloss]
    nlinarith

/-- Two preceding ball bounds and the lower-degree order theorem propagate growth.
The only lower-degree input is the explicitly supplied order bound at degree s-1. -/
theorem half_radius_growth_step {s q k u : ℕ} (hs : 2 ≤ s) (hsk : s ≤ k + 2)
    (hq : 2 * (k + 2) - 1 ≤ q)
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s - 1 ≤ (outN F U v).card) → U.Nonempty → q * (s - 1) + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hinner : s * k + 1 ≤ (ball D V u k).card)
    (hprev : s * (k + 1) + 1 ≤ (ball D V u (k + 1)).card) :
    s * (k + 2) + 1 ≤ (ball D V u (k + 2)).card := by
  classical
  by_contra hn
  let c := (ball D V u (k + 1) \ ball D V u k).card
  let t := (ball D V u (k + 2) \ ball D V u (k + 1)).card
  have hc : c + (ball D V u k).card = (ball D V u (k + 1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t + (ball D V u (k + 1)).card = (ball D V u (k + 2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have htlt : t < s := by simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *; omega
  have hb := prefix_deficiency_of_size hsize hf hu (by omega : k + 2 ≤ q) hm
    (by omega : s - 1 ≤ s) htlt
  have hpos : 0 < (ball D V u (k + 1)).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  have hN : (ball D V u (k + 1)).card - 1 + t + 1 ≤ s * (k + 2) := by omega
  have hct : c + t + 1 ≤ 2 * s := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *
    omega
  have hh := half_radius_deficiency_strict hs hsk hq hN hct htlt
  change q * (s - 1) + 1 ≤ (ball D V u (k + 1)).card - 1 + c * (s - 1 + t - s) at hb
  omega

theorem half_radius_cap_deficiency_strict {s r q N c t : ℕ}
    (hs : 2 ≤ s) (hr : s ≤ r) (hq : 2 * r ≤ q)
    (hN : N + t + 1 ≤ s * r + 1) (hc : c + t + 1 ≤ 2 * s + 1) (ht : t < s) :
    N + c * (s - 1 + t - s) < q * (s - 1) + 1 := by
  have hs1 : s - 1 + 1 = s := by omega
  have hqmul := Nat.mul_le_mul_right (s - 1) hq
  by_cases ht0 : t = 0
  · have hloss : s - 1 + t - s = 0 := by omega
    rw [hloss, Nat.mul_zero, Nat.add_zero]
    have hs2 : s - 2 + 2 = s := by omega
    have hp := Nat.zero_le ((s - 2) * r)
    nlinarith
  · have hloss : s - 1 + t - s = t - 1 := by omega
    have ht1 : t - 1 + 1 = t := by omega
    have hgap : s - t - 1 + t + 1 = s := by omega
    have hmul := Nat.mul_le_mul_right (t - 1) hc
    have hp := Nat.zero_le ((s - t - 1) * (s - t))
    have hgap' : s - t + t = s := by omega
    have hs2 : s - 2 + 2 = s := by omega
    have hrad : r - s + s = r := by omega
    have hprod := Nat.zero_le ((r - s) * (s - 2))
    rw [hloss]
    nlinarith

/-- At an even half-radius cutoff, a tight ball cap descends one radius. -/
theorem half_radius_cap_descent {s q k u : ℕ} (hs : 2 ≤ s) (hsk : s ≤ k + 2)
    (hq : 2 * (k + 2) ≤ q)
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s - 1 ≤ (outN F U v).card) → U.Nonempty → q * (s - 1) + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hinner : s * k + 1 ≤ (ball D V u k).card)
    (hcap : (ball D V u (k + 2)).card ≤ s * (k + 2) + 1) :
    (ball D V u (k + 1)).card ≤ s * (k + 1) + 1 := by
  classical
  by_contra hn
  let c := (ball D V u (k + 1) \ ball D V u k).card
  let t := (ball D V u (k + 2) \ ball D V u (k + 1)).card
  have hc : c + (ball D V u k).card = (ball D V u (k + 1)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t + (ball D V u (k + 1)).card = (ball D V u (k + 2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have htlt : t < s := by simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *; omega
  have hb := prefix_deficiency_of_size hsize hf hu (by omega : k + 2 ≤ q) hm
    (by omega : s - 1 ≤ s) htlt
  have hpos : 0 < (ball D V u (k + 1)).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  have hN : (ball D V u (k + 1)).card - 1 + t + 1 ≤ s * (k + 2) + 1 := by omega
  have hct : c + t + 1 ≤ 2 * s + 1 := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *
    omega
  have hh := half_radius_cap_deficiency_strict hs hsk hq hN hct htlt
  change q * (s - 1) + 1 ≤ (ball D V u (k + 1)).card - 1 + c * (s - 1 + t - s) at hb
  omega

end LeanCH.BR.BRsGen
