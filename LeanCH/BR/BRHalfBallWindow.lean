import LeanCH.BR.BRHalfBallGrowth
import LeanCH.BR.BRFiveCutoff

/-! Native prefix-deficiency proof of the order bound in Shen's high-cutoff window. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem window_deficiency_strict {s r q N c t : ℕ}
    (hs : 3 ≤ s) (hr : 3 ≤ r) (hqs : 2 * s - 2 ≤ q) (hqr : 2 * r - 1 ≤ q)
    (hN : N + t + 1 ≤ s * r) (hc : c + t + 1 ≤ 2 * s) (ht : t < s) :
    N + c * (s - 1 + t - s) < q * (s - 1) + 1 := by
  by_cases hsr : s ≤ r
  · exact half_radius_deficiency_strict (by omega) hsr hqr hN hc ht
  have hs1 : s - 1 + 1 = s := by omega
  by_cases ht0 : t = 0
  · have hloss : s - 1 + t - s = 0 := by omega
    rw [hloss, Nat.mul_zero, Nat.add_zero]
    have hq' : 2 * r ≤ q + 1 := by omega
    have hqmul := Nat.mul_le_mul_right (s - 1) hq'
    have hs2 : s - 2 + 2 = s := by omega
    have hr1 : r - 1 + 1 = r := by omega
    have hp := Nat.zero_le ((s - 2) * (r - 1))
    nlinarith
  · have hloss : s - 1 + t - s = t - 1 := by omega
    have ht1 : t - 1 + 1 = t := by omega
    have hgap : s - t - 1 + t + 1 = s := by omega
    have hgap' : s - t + t = s := by omega
    have hmul := Nat.mul_le_mul_right (t - 1) hc
    have hp := Nat.zero_le ((s - t - 1) * (s - t))
    have hqmul := Nat.mul_le_mul_right (s - 1) (by omega : 2 * s ≤ q + 2)
    have hrmul := Nat.mul_le_mul_left s (by omega : r + 1 ≤ s)
    rw [hloss]
    nlinarith

theorem half_radius_growth_in_window {s q k u : ℕ} (hs : 3 ≤ s) (hk : 1 ≤ k)
    (hqs : 2 * s - 2 ≤ q) (hqr : 2 * (k + 2) - 1 ≤ q)
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
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at *; omega
  have hh := window_deficiency_strict hs (by omega : 3 ≤ k + 2) hqs hqr hN hct htlt
  change q * (s - 1) + 1 ≤ (ball D V u (k + 1)).card - 1 + c * (s - 1 + t - s) at hb
  omega

theorem half_ball_of_lower_order_in_window {s q : ℕ} (hs : 3 ≤ s) (hq : 2 * s - 2 ≤ q)
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s - 1 ≤ (outN F U v).card) → U.Nonempty → q * (s - 1) + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V) :
    ∀ k, 1 ≤ k → 2 * k - 1 ≤ q → s * k + 1 ≤ (ball D V u k).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hkq
    by_cases hk1 : k = 1
    · subst k
      rw [card_B1 (hf.mono_bound (by omega)) hu]
      have hh := hm u hu
      simpa using Nat.add_le_add_right hh 1
    by_cases hk2 : k = 2
    · subst k
      have hh := card_ball_two_ge_twice (by omega : 2 ≤ s) (hf.mono_bound (by omega)) hm hu
      simpa only [Nat.mul_comm s 2] using hh
    have hk3 : 3 ≤ k := by omega
    have hi := ih (k - 2) (by omega) (by omega) (by omega)
    have hp := ih (k - 1) (by omega) (by omega) (by omega)
    have he2 : k - 2 + 2 = k := by omega
    have he1 : k - 2 + 1 = k - 1 := by omega
    have hh := half_radius_growth_in_window hs (by omega : 1 ≤ k - 2) hq
      (by omega : 2 * (k - 2 + 2) - 1 ≤ q) hsize hf hm hu hi
      (by simpa only [he1] using hp)
    simpa only [he2] using hh

theorem order_of_lower_order_in_window {s q : ℕ} (hs : 3 ≤ s) (hq : 2 * s - 2 ≤ q)
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s - 1 ≤ (outN F U v).card) → U.Nonempty → q * (s - 1) + 1 ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hne : V.Nonempty) : q * s + 1 ≤ V.card := by
  have hi : ∀ v ∈ V, s * (q / 2) + 1 ≤ (ball D V v (q / 2)).card :=
    fun _ hv => half_ball_of_lower_order_in_window hs hq hsize hf hm hv _ (by omega) (by omega)
  have hj : ∀ v ∈ V, s * (q - q / 2) + 1 ≤ (ball D V v (q - q / 2)).card :=
    fun _ hv => half_ball_of_lower_order_in_window hs hq hsize hf hm hv _ (by omega) (by omega)
  have hh := card_ge_of_two_balls hf (by omega : q / 2 + (q - q / 2) ≤ q) hi hj hne
  have he := congrArg (fun a => s * a) (by omega : q / 2 + (q - q / 2) = q)
  simp only [Nat.mul_add] at he
  nlinarith

/-- The high-cutoff order theorem, with its lower-degree input discharged by induction. -/
theorem order_in_window : ∀ s, 2 ≤ s → ∀ q, 2 * s - 2 ≤ q →
    ∀ {D : CH.Digraph} {V : Finset ℕ}, QFree D V q →
      (∀ v ∈ V, s ≤ (outN D V v).card) → V.Nonempty → q * s + 1 ≤ V.card := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs q hq D V hf hm hn
    by_cases hs2 : s = 2
    · subst s
      simpa only [Nat.mul_comm q 2] using corB (by omega) hf hm hn
    have hs3 : 3 ≤ s := by omega
    apply order_of_lower_order_in_window hs3 hq ?_ hf hm hn
    intro F U hF hmin hne
    exact ih (s - 1) (by omega) (by omega) q (by omega) hF hmin hne

theorem half_ball_in_window {s q : ℕ} (hs : 3 ≤ s) (hq : 2 * s - 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (k : ℕ) (hk : 1 ≤ k) (hkq : 2 * k - 1 ≤ q) :
    s * k + 1 ≤ (ball D V u k).card :=
  half_ball_of_lower_order_in_window hs hq
    (fun _ _ hF hmF hn => order_in_window (s - 1) (by omega) q (by omega) hF hmF hn)
    hf hm hu k hk hkq

/-- The literal cycle conclusion in Shen's known high-cutoff range. -/
theorem ch_in_window {s q n : ℕ} (hs : 2 ≤ s) (hq : 2 * s - 2 ≤ q)
    (hn : 0 < n) (hnq : n ≤ q * s) {D : CH.Digraph}
    (hloop : CH.Loopless D n) (hdeg : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, s ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hdeg (Finset.mem_range.mp hv)
  have hh := order_in_window s hs q hq hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hh
  omega

end LeanCH.BR.BRsGen
