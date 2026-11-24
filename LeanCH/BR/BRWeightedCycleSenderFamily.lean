import LeanCH.BR.BRWeightedCycleLoad
import LeanCH.BR.BRWeightedCycleEscape

/-! An actual family: exterior senders whose cycle heads contain a cycle arc.
Each sender occurs once. Nonemptiness is not asserted without a supplier. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def consecutiveCycleSenders (D : CH.Digraph) (V M : Finset ℕ) : Finset ℕ := by
  classical
  exact (V \ M).filter (fun b => ∃ u ∈ outN D M b, ∃ v ∈ outN D M b, D u v = true)

theorem consecutiveCycleSenders_subset {D : CH.Digraph} {V M : Finset ℕ} :
    consecutiveCycleSenders D V M ⊆ V \ M := Finset.filter_subset _ _

theorem exists_consecutive_cycle_selector (D : CH.Digraph) (V M : Finset ℕ) :
    ∃ u : ℕ → ℕ, ∀ b ∈ consecutiveCycleSenders D V M,
      u b ∈ outN D M b ∧ ∃ v ∈ outN D M b, D (u b) v = true := by
  classical
  have h : ∀ b, ∃ u, b ∈ consecutiveCycleSenders D V M →
      u ∈ outN D M b ∧ ∃ v ∈ outN D M b, D u v = true := by
    intro b
    by_cases hb : b ∈ consecutiveCycleSenders D V M
    · obtain ⟨u, hu, v, hv, huv⟩ := (Finset.mem_filter.mp hb).2
      exact ⟨u, fun _ => ⟨hu, v, hv, huv⟩⟩
    · exact ⟨0, fun h => False.elim (hb h)⟩
  choose u hu using h
  exact ⟨u, hu⟩

theorem consecutive_sender_gap_exterior {D : CH.Digraph} {V M : Finset ℕ}
    (hout : OutEq 1 D M) {b u : ℕ} (hu : u ∈ outN D M b)
    (hv : ∃ v ∈ outN D M b, D u v = true) : outGap D V u b ⊆ V \ M := by
  obtain ⟨v, hv, huv⟩ := hv
  intro z hz
  obtain ⟨hzV, huz, hnbz⟩ := mem_outGap.mp hz
  refine Finset.mem_sdiff.mpr ⟨hzV, ?_⟩
  intro hzM
  have hez := Finset.card_le_one.mp (hout u (outN_subset hu)).le z
    (mem_outN.mpr ⟨hzM, huz⟩) v (mem_outN.mpr ⟨outN_subset hv, huv⟩)
  exact hnbz (hez ▸ (mem_outN.mp hv).2)

/-- A supplied tight path provides a member of the actual family. -/
theorem tight_path_consecutive_sender {q l : ℕ} (hl : l + 3 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V \ M) (hab : Walk D V a b l)
    (hIa : (inN D M a).Nonempty) (hOb : 2 ≤ (outN D M b).card)
    (htight : (inN D M a).card + (outN D M b).card = l + 3) :
    b ∈ consecutiveCycleSenders D V M := by
  exact Finset.mem_filter.mpr ⟨hb,
    tight_path_cycle_heads_internal_arc hl hf hMV hM hout hin ha hab hIa hOb htight⟩

/-- The family and selector are derived. All capacity lies in the exterior.
This is an inequality, not a supplier of a strict capacity deficit. -/
theorem exists_cycle_exterior_charge {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hout : OutEq 1 D M)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hm : mass V p = 1) (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c)
    (hc : ∀ v ∈ V, col q D V p v = c) :
    ∃ u : ℕ → ℕ,
      (∀ b ∈ consecutiveCycleSenders D V M,
        u b ∈ outN D M b ∧ ∃ v ∈ outN D M b, D (u b) v = true) ∧
      (∑ b ∈ consecutiveCycleSenders D V M, p b * ((q - 1 : ℚ) * w (u b) + w b)) +
        q * (∑ b ∈ consecutiveCycleSenders D V M,
          p b * mass ((outGap D V b (u b)).erase (u b)) w) ≤
        ∑ z ∈ V \ M, min (q - c + p z - q * mass (ball D V z (q - 2)) p)
          (c * (inN D M z).card - mass (inN D M z) p) * w z := by
  classical
  obtain ⟨u, hu⟩ := exists_consecutive_cycle_selector D V M
  refine ⟨u, hu, ?_⟩
  let T := consecutiveCycleSenders D V M
  have hTV : T ⊆ V := fun b hb => (Finset.mem_sdiff.mp (consecutiveCycleSenders_subset hb)).1
  have huM : ∀ b ∈ T, u b ∈ M := fun b hb => outN_subset (hu b hb).1
  have harc : ∀ b ∈ T, D b (u b) = true := fun b hb => (mem_outN.mp (hu b hb).1).2
  have hl := weighted_gap_discharge_exact u id p w
    (fun b hb => hMV (huM b hb)) harc
    (fun b hb => loopfree hf (by omega : 1 ≤ q) (hMV (huM b hb)))
    (fun b hb => (hr (u b) (hMV (huM b hb))).trans (hr b (hTV hb)).symm)
  have he : (∑ z ∈ V, gapLoad D V T u id p z * w z) =
      ∑ z ∈ V \ M, gapLoad D V T u id p z * w z := by
    symm
    apply Finset.sum_subset Finset.sdiff_subset
    intro z hz hnot
    have hzM : z ∈ M := by simpa only [Finset.mem_sdiff, hz, true_and, not_not] using hnot
    have hzero : gapLoad D V T u id p z = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hn : z ∉ outGap D V (u b) b := by
        intro hg
        exact (Finset.mem_sdiff.mp
          (consecutive_sender_gap_exterior hout (hu b hb).1 (hu b hb).2 hg)).2 hzM
      simp only [id_eq, hn, ite_false]
    rw [hzero, zero_mul]
  rw [he] at hl
  simp only [id_eq, T] at hl
  rw [← hl]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hzV := (Finset.mem_sdiff.mp hz).1
  have h := mul_le_mul_of_nonneg_right
    (gapLoad_last_layer_caps hq hf hsat hMV hTV u huM harc p hp hm c hc hzV) (hw z hzV)
  simpa only [mul_assoc] using h

end LeanCH.BR.WeightedSD
