import LeanCH.BR.BRThresholdDensity
import LeanCH.BR.BRShortestCycle

/-! Critical ball plateaus and six-cycle supports in small mixed-degree cores. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

/-- A critical-size ball containing a high row cannot be closed. -/
theorem critical_ball_strict_growth {D : CH.Digraph} {V : Finset ℕ} {q d k u : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hm : ∀ v ∈ V, d ≤ (outN D V v).card) (hu : u ∈ V)
    (hh : d + 1 ≤ (outN D V u).card) (hprev : q * d + 1 ≤ (ball D V u k).card) :
    q * d + 2 ≤ (ball D V u (k + 1)).card := by
  classical
  by_contra hn
  have hsub : ball D V u k ⊆ ball D V u (k + 1) := ball_mono_radius (by omega)
  have hcard := Finset.card_le_card hsub
  have heq : ball D V u k = ball D V u (k + 1) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hretain : ∀ v ∈ ball D V u k, outN D V v ⊆ outN D (ball D V u k) v := by
    intro v hv w hw
    obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
    exact mem_outN.mpr ⟨heq ▸ ball_step hv hwV hvw, hvw⟩
  have hmB : ∀ v ∈ ball D V u k, d ≤ (outN D (ball D V u k) v).card :=
    fun v hv => (hm v (ball_subset hv)).trans (Finset.card_le_card (hretain v hv))
  have hreg := (dt_reg hq hb (hf.mono_set ball_subset) hmB (by omega)).1
    u (self_mem_ball hu)
  have hhigh := Finset.card_le_card (hretain u (self_mem_ball hu))
  omega

theorem six_free_high_ball_five {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (hm : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hu : u ∈ V) (hh : 6 ≤ (outN D V u).card) : 14 ≤ (ball D V u 5).card := by
  have hb : Ball 6 2 := by
    intro F W hF ho v hv
    exact ball_growth 6 (by decide) F W hF (fun x hx => (ho x hx).ge) v hv 5 (by decide)
  exact critical_ball_strict_growth (by decide : 1 ≤ 6) hb hf hm hu (by omega)
    (threshold_two_ball_four (by decide) hf hm hu hh)

/-- High rows improve both outgoing mass and the complementary incoming cap. -/
theorem six_free_two_core_density {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 6) (hm : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hh : ∀ v ∈ H, 6 ≤ (outN D V v).card) :
    13 * V.card + 7 * H.card ≤ V.card * V.card := by
  have hcapH : ∀ v ∈ H, (inN D V v).card + 14 ≤ V.card := by
    intro v hv
    have hb := six_free_high_ball_five hf hm (hHV hv) (hh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by decide : 5 + 1 ≤ 6)
    omega
  have hcapL : ∀ v ∈ V \ H, (inN D V v).card + 11 ≤ V.card := by
    intro v hv
    have hvV := (Finset.mem_sdiff.mp hv).1
    have hb := ball_growth 6 (by decide) D V hf hm v hvV 5 (by decide)
    have hi := incoming_add_ball_le hf hvV (by decide : 5 + 1 ≤ 6)
    omega
  have hsH := Finset.sum_le_sum hcapH
  have hsL := Finset.sum_le_sum hcapL
  have hoH := Finset.sum_le_sum hh
  have hoL := Finset.sum_le_sum (s := V \ H) (fun v hv => hm v (Finset.mem_sdiff.mp hv).1)
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsL hoH hoL
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  nlinarith [congrArg (fun n => n * V.card) hc]

theorem six_cycle_support_of_not_six_free {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (hn : V.Nonempty) (hnot : ¬ QFree D V 6) :
    ∃ M : Finset ℕ, M ⊆ V ∧ M.card = 6 ∧ OutEq 1 D M := by
  obtain ⟨p, M, hp, hF, hMV, hM, hOut⟩ := exists_minimal_cycle_support
    (by decide : 1 ≤ 5) hf hm hn
  have hp5 : p = 5 := by
    by_contra hne
    exact hnot (hF.mono_bound (by omega))
  exact ⟨M, hMV, by omega, hOut⟩

theorem six_cycle_in_two_core {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hH : 13 ≤ H.card) (hV : V.card ≤ 18) :
    ∃ M : Finset ℕ, M ⊆ V ∧ M.card = 6 ∧ OutEq 1 D M := by
  have hn : V.Nonempty := Finset.card_pos.mp (by have := Finset.card_le_card hHV; omega)
  apply six_cycle_support_of_not_six_free hf (fun v hv => by have := hm v hv; omega) hn
  intro h6
  have hd := six_free_two_core_density h6 hm hHV hh
  have hsq := Nat.mul_le_mul_left V.card hV
  omega

theorem six_cycle_in_three_core {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v ∈ V, 3 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hH : 7 ≤ H.card) (hV : V.card ≤ 20) :
    ∃ M : Finset ℕ, M ⊆ V ∧ M.card = 6 ∧ OutEq 1 D M := by
  have hn : V.Nonempty := Finset.card_pos.mp (by have := Finset.card_le_card hHV; omega)
  apply six_cycle_support_of_not_six_free hf (fun v hv => by have := hm v hv; omega) hn
  intro h6
  have hd := mixed_degree_density_of_ball (by decide : 1 ≤ 6) (ball_all 6 (by decide)) h6 hm hHV hh
  have hsq := Nat.mul_le_mul_left V.card hV
  omega

end LeanCH.BR.BRsGen
