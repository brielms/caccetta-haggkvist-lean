import LeanCH.BR.BRq5Half
import LeanCH.BR.BR55Consequences
import LeanCH.BR.BR45

/-! Boundary regularity and the literal CH cycle bound at degree five, for every cutoff. -/

namespace LeanCH.BR.BRq5
open BRq2 BRq3 BRq4 BR45 BRsGen Compose.Boundary

/-- Arbitrary-host order input for the next degree's deficiency argument. -/
theorem card_ge_five_mul {q : ℕ} (hq : 5 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hne : V.Nonempty) :
    q * 5 + 1 ≤ V.card := by
  by_cases hq5 : q = 5
  · subst q; exact card_ge_twenty_six hf hm hne
  by_cases hq6 : q = 6
  · subst q; exact card_ge_thirty_one hf hm hne
  have hq7 : 7 ≤ q := by omega
  have hi : ∀ v ∈ V, 5 * (q / 2) + 1 ≤ (ball D V v (q / 2)).card :=
    fun _ hv => half_ball_five (q / 2) (by omega) (hf.mono_bound (by omega)) hm hv
  have hj : ∀ v ∈ V, 5 * (q - q / 2) + 1 ≤ (ball D V v (q - q / 2)).card :=
    fun _ hv => half_ball_five (q - q / 2) (by omega) (hf.mono_bound (by omega)) hm hv
  have hh := card_ge_of_two_balls hf (by omega : q / 2 + (q - q / 2) ≤ q) hi hj hne
  omega

theorem fourth_cap_of_half_cap {q k : ℕ} (hk : 4 ≤ k) (hkq : 2 * k ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hu : u ∈ V) (hcap : (ball D V u k).card ≤ 5 * k + 1) :
    (ball D V u 4).card ≤ 21 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk4 : k = 4
    · subst k; exact hcap
    have hk5 : 5 ≤ k := by omega
    have hk2 : k - 2 + 2 = k := by omega
    have hk1 : k - 2 + 1 = k - 1 := by omega
    have hinner := half_ball_five (k - 2) (by omega) (hf.mono_bound (by omega)) hm hu
    have hprev := half_radius_cap_descent (s := 5) (k := k - 2) (by decide)
      (by omega) (by omega : 2 * (k - 2 + 2) ≤ q)
      (fun _ _ hF hmF hn => dt_size (by omega) (ball_all4 q (by omega)) hF hmF hn)
      hf hm hu hinner (by simpa only [hk2] using hcap)
    apply ih (k - 1) (by omega) (by omega) (by omega)
    simpa only [hk1] using hprev

theorem boundary_second_ball_cap {q : ℕ} (hq : 8 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ v ∈ V, 5 ≤ (outN D V v).card) (hV : V.card = q * 5 + 1) :
    ∀ u ∈ V, (ball D V u 2).card ≤ 11 := by
  have hi : ∀ v ∈ V, 5 * (q / 2) + 1 ≤ (ball D V v (q / 2)).card :=
    fun _ hv => half_ball_five (q / 2) (by omega) (hf.mono_bound (by omega)) hm hv
  have hj : ∀ v ∈ V, 5 * (q - q / 2) + 1 ≤ (ball D V v (q - q / 2)).card :=
    fun _ hv => half_ball_five (q - q / 2) (by omega) (hf.mono_bound (by omega)) hm hv
  have heq := two_balls_boundary_cards hf (by omega : q / 2 + (q - q / 2) ≤ q)
    hi hj (by omega)
  intro u hu
  have hfour := fourth_cap_of_half_cap (by omega : 4 ≤ q / 2) (by omega)
    hf hm hu (heq u hu).1.le
  exact second_ball_cap_of_fourth (hf.mono_bound hq) hm hu hfour

/-- No open structural input remains at degree five. -/
theorem br_q_five (q : ℕ) (hq : 0 < q) : BoundaryRegular q 5 := by
  by_cases hq1 : q = 1
  · subst q
    apply br_of_ball (by decide)
    intro D V hf ho u hu
    exact Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  by_cases hq2 : q = 2
  · subst q
    apply br_of_ball (by decide)
    intro D V hf ho u hu
    change 6 ≤ (ball D V u 1).card
    classical
    have heq : ball D V u 1 = insert u (outN D V u) := by
      ext v; simp only [mem_ball_one hu, Finset.mem_insert]
    have hnot : u ∉ outN D V u := fun h => loopfree hf (by decide) hu (mem_outN.mp h).2
    rw [heq, Finset.card_insert_of_notMem hnot, ho u hu]
  by_cases hq3 : q = 3
  · subst q; exact BR35.br_five
  by_cases hq4 : q = 4
  · subst q; exact BR45.br_four_five
  by_cases hq5 : q = 5
  · subst q; exact BR55.br_five_five
  by_cases hq6 : q = 6
  · subst q; exact BR65.br_six_five
  by_cases hq7 : q = 7
  · subst q; exact BR75.br_seven_five
  have hq8 : 8 ≤ q := by omega
  apply br_of_second_ball_cap (by decide : 2 ≤ 5) (by omega : 5 ≤ q)
  intro D hf hm
  exact boundary_second_ball_cap hq8 hf hm (by simp)

theorem ch_five_of_le {q n : ℕ} (hq : 0 < q) (hn : 0 < n) (hnq : n ≤ q * 5)
    {G : CH.Digraph} (hloop : CH.Loopless G n) (hdeg : CH.MinOutdegreeAtLeast G n 5) :
    CH.HasDirectedCycleAtMost G n q :=
  ch_of_boundaryRegular (by decide) (br_q_five q hq) hn hnq hloop hdeg

/-- The literal Caccetta-Haggkvist cycle bound at minimum degree five, for every order. -/
theorem ch_five_all {n : ℕ} {G : CH.Digraph} (hn : 0 < n) (hloop : CH.Loopless G n)
    (hdeg : CH.MinOutdegreeAtLeast G n 5) :
    CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 5) := by
  have hc : CH.ceilDiv n 5 = (n + 4) / 5 := by unfold CH.ceilDiv; omega
  apply ch_five_of_le (by omega) hn (by omega) hloop hdeg

end LeanCH.BR.BRq5
