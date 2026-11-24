import LeanCH.BR.BRMinimumRootGeometry
import LeanCH.BR.BRWeightedSplitBudget

/-! Local minimum-weight and cut-budget rules. No successful global split
or smaller-graph induction is assumed in these statements. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem nonempty_mass_ge_minimum {V A : Finset ℕ} (hAV : A ⊆ V) (hA : A.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x) (M : ℚ) (hmin : ∀ x ∈ V, M ≤ a x) :
    M ≤ mass A a := by
  obtain ⟨x, hx⟩ := hA
  exact (hmin x (hAV hx)).trans (single_le_sum (fun z hz => ha z (hAV hz)) hx)

theorem minimum_new_head_pays {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {v x : ℕ}
    {C : Finset (ℕ × ℕ)} (a α : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (hmin : ∀ z ∈ outN D V v, a v ≤ a z) (hα : ∀ z ∈ outN D V v, 0 ≤ α z)
    (hm : mass (outN D V v) α = a v) (hnew : (splitNew q D V v C x).Nonempty) :
    q * mass (splitBlocked q D V v C x) α ≤ q * mass (splitNew q D V v C x) a := by
  have hNT : splitNew q D V v C x ⊆ outN D V v := fun z hz =>
    (mem_filter.mp (mem_sdiff.mp hz).1).1
  have hN := nonempty_mass_ge_minimum hNT hnew a
    (fun z hz => ha z (outN_subset hz)) (a v) hmin
  have hB : mass (splitBlocked q D V v C x) α ≤ a v := by
    rw [← hm]
    exact mass_mono sdiff_subset hα
  exact mul_le_mul_of_nonneg_left (hB.trans hN) (Nat.cast_nonneg q)

theorem transfer_row_gain_le {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V T : Finset ℕ} {r : ℕ} (hTV : T ⊆ V) (hr : r ∈ V) (hloop : ¬ D r r = true)
    (α : ℕ → ℚ) (hα : ∀ z ∈ V, 0 ≤ α z) (hs : ∀ z ∈ V, z ∉ T → α z = 0) :
    α r + q * mass (outN D V r ∩ T) α ≤ q * mass T α := by
  have hsum : α r + mass (outN D V r ∩ T) α ≤ mass T α := by
    by_cases hrT : r ∈ T
    · have hH : outN D V r ∩ T ⊆ T.erase r := by
        intro z hz
        obtain ⟨ho, ht⟩ := mem_inter.mp hz
        refine mem_erase.mpr ⟨?_, ht⟩
        intro he; subst z
        exact hloop (mem_outN.mp ho).2
      have hle := mass_mono hH (fun z hz => hα z (hTV (mem_erase.mp hz).2))
      have he : mass (T.erase r) α + α r = mass T α := sum_erase_add _ _ hrT
      linarith
    · rw [hs r hr hrT, zero_add]
      exact mass_mono inter_subset_right (fun z hz => hα z (hTV hz))
  have hqQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  nlinarith [hα r hr]

/-- Pure budget master: no graph, root, transfer support or induction premise. -/
theorem paid_cut_card_le_one {q : ℕ} {L : Finset ℕ}
    (a : ℕ → ℚ) (M δ gain : ℚ) (hM : 0 ≤ M) (hmin : ∀ z ∈ L, M ≤ a z)
    (hδ : δ ≤ ((q : ℚ) - 1) * M) (hgain : gain ≤ q * M)
    (hpaid : q * mass L a < δ + gain) : L.card ≤ 1 := by
  have hcost : (L.card : ℚ) * M ≤ mass L a := by
    calc
      _ = ∑ z ∈ L, M := by simp
      _ ≤ _ := sum_le_sum hmin
  by_contra hn
  have hcard : (2 : ℚ) ≤ L.card := by exact_mod_cast (by omega : 2 ≤ L.card)
  have htwo : 2 * M ≤ mass L a := by nlinarith
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hmul := mul_le_mul_of_nonneg_left htwo hqQ
  nlinarith

theorem paid_nonloop_cut_row_card_le_one {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V T L : Finset ℕ} {r : ℕ} (hTV : T ⊆ V) (hr : r ∈ V) (hloop : ¬ D r r = true)
    (a α : ℕ → ℚ) (hα : ∀ z ∈ V, 0 ≤ α z) (hs : ∀ z ∈ V, z ∉ T → α z = 0)
    (M δ : ℚ) (hM : 0 ≤ M) (hm : mass T α = M) (hmin : ∀ z ∈ L, M ≤ a z)
    (hδ : δ ≤ ((q : ℚ) - 1) * M)
    (hpaid : q * mass L a < δ + α r + q * mass (outN D V r ∩ T) α) : L.card ≤ 1 := by
  apply paid_cut_card_le_one a M δ (α r + q * mass (outN D V r ∩ T) α) hM hmin hδ
  · simpa only [hm] using transfer_row_gain_le hq hTV hr hloop α hα hs
  · linarith

/-- A locally paid cut at a nonreceiver missing t requires q*alpha(t)<delta.
The conclusion is kept multiplied, so no positive-cutoff premise is needed. -/
theorem paid_cut_missing_receiver_is_light {q : ℕ} {D : CH.Digraph}
    {V T L : Finset ℕ} {r t : ℕ} (hTV : T ⊆ V) (hLV : L ⊆ V) (hL : L.Nonempty)
    (hr : r ∈ V) (hrT : r ∉ T) (ht : t ∈ T) (hrt : ¬ D r t = true)
    (a α : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (hs : ∀ z ∈ V, z ∉ T → α z = 0) (M δ : ℚ)
    (hm : mass T α = M) (hmin : ∀ z ∈ V, M ≤ a z)
    (hpaid : q * mass L a < δ + α r + q * mass (outN D V r ∩ T) α) :
    q * α t < δ := by
  have hcost := nonempty_mass_ge_minimum hLV hL a ha M hmin
  have hH : outN D V r ∩ T ⊆ T.erase t := by
    intro z hz
    obtain ⟨ho, ht'⟩ := mem_inter.mp hz
    refine mem_erase.mpr ⟨?_, ht'⟩
    intro he; subst z
    exact hrt (mem_outN.mp ho).2
  have hheads := mass_mono hH (fun z hz => hα z (hTV (mem_erase.mp hz).2))
  have htotal : mass (T.erase t) α + α t = M := by
    rw [← hm]
    exact sum_erase_add _ _ ht
  rw [hs r hr hrT, add_zero] at hpaid
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hc := mul_le_mul_of_nonneg_left hcost hqQ
  have hh := mul_le_mul_of_nonneg_left hheads hqQ
  nlinarith

theorem interior_paid_cut_is_light {q i j : ℕ} {D : CH.Digraph}
    {V : Finset ℕ} {v t r s x : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hC : RootCuts D V v C) (hcut : (r, s) ∈ C)
    (ht : t ∈ outN D V v) (hx : x ∈ inN D V v)
    (initial : Walk D V t r i) (ending : Walk D V s x j)
    (hi : 1 ≤ i) (hlen : i + 1 + j ≤ q - 1)
    (a α : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v) (hmin : ∀ z ∈ V, a v ≤ a z) (δ : ℚ)
    (hpaid : q * mass (cutHeads V C r) a <
      δ + α r + q * mass (outN D V r ∩ outN D V v) α) : q * α t < δ := by
  obtain ⟨hrV, hsV, hrs, _, _⟩ := hC r s hcut
  obtain ⟨hrT, hrt⟩ := interior_return_tail_exclusions hf hv ht hx initial hrs hsV ending hi hlen
  exact paid_cut_missing_receiver_is_light outN_subset (filter_subset _ _)
    ⟨s, mem_filter.mpr ⟨hsV, hcut⟩⟩ hrV hrT ht hrt a α ha hα hs (a v) δ hm hmin hpaid

end LeanCH.BR.WeightedSD
