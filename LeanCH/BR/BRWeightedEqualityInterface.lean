import LeanCH.BR.BRWeightedEqualityCycle

/-! The boundary-equality branch: regular hosts close, while every proper
tight cycle has both actual rich exterior interfaces at value one. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem degree_one_equalizers_agree {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hout : OutEq 1 D V)
    (hin : ∀ v ∈ V, (inN D V v).card = 1)
    (w p : ℕ → ℚ) (hr : ∀ v ∈ V, row q D V w v = 1)
    (hc : ∀ v ∈ V, col q D V p v = 1) : ∀ v ∈ V, w v = p v := by
  let r : ℕ → ℚ := fun _ => 1 / (q + 1)
  have hden : (q : ℚ) + 1 ≠ 0 := by positivity
  have hrr : ∀ v ∈ V, row q D V r v = 1 := by
    intro v hv
    rw [row, outW_eq_mass]
    simp only [r, mass, Finset.sum_const, nsmul_eq_mul, hout v hv, Nat.cast_one, one_mul]
    field_simp
    ring
  have hrc : ∀ v ∈ V, col q D V r v = 1 := by
    intro v hv
    change row q (fun a b => D b a) V r v = 1
    rw [row, outW_eq_mass]
    change r v + q * mass (inN D V v) r = 1
    simp only [r, mass, Finset.sum_const, nsmul_eq_mul, hin v hv, Nat.cast_one, one_mul]
    field_simp
    ring
  have hw := column_equalizer_unique_on (D := fun a b => D b a) hq hr hrr
  have hp := column_equalizer_unique_on hq hc hrc
  exact fun v hv => (hw v hv).trans (hp v hv).symm

theorem proper_exterior_mass_pos {V M : Finset ℕ} (hMV : M ⊆ V) (hne : M ≠ V)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v) : 0 < mass (V \ M) w := by
  have hE : (V \ M).Nonempty := by
    by_contra hn
    have hVM : V ⊆ M := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hn)
    exact hne (Finset.Subset.antisymm hMV hVM)
  exact Finset.sum_pos (fun v hv => hw v (Finset.mem_sdiff.mp hv).1) hE

theorem proper_cycle_rich_receivers {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hne : M ≠ V) (hM : M.card = q + 1)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v) (c : ℚ)
    (hr : ∀ v ∈ M, row q D V w v = c) (hfeas : mass V w ≤ c) :
    (cycleRichReceivers D V M).Nonempty := by
  have hmass := proper_exterior_mass_pos hMV hne w hw
  have hbound := cycle_rich_receiver_mass hMV hM hin w (fun v hv => (hw v hv).le) c hr
  have hsur : 0 ≤ ((q : ℚ) + 1) * (c - mass V w) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hfeas)
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hbound
  simp only [mass, Finset.sum_empty, mul_zero] at hbound
  change ((q : ℚ) + 1) * (c - mass V w) + mass (V \ M) w ≤ 0 at hbound
  linarith

theorem proper_cycle_rich_senders {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hne : M ≠ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 < p v) (c : ℚ)
    (hc : ∀ v ∈ M, col q D V p v = c) (hfeas : mass V p ≤ c) :
    (cycleRichSenders D V M).Nonempty :=
  proper_cycle_rich_receivers (D := fun a b => D b a) hMV hne hM hout p hp c hc hfeas

end LeanCH.BR.WeightedSD
