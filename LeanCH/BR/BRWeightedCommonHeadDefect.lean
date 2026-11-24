import LeanCH.BR.BRWeightedLayerDefect

/-! Common-head multiplicity pays only covered missed pairs. Every reuse of
a head is counted, and the uncovered-pair mass remains explicit. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def uncoveredLayerSenders (q : ℕ) (D : CH.Digraph)
    (V M T : Finset ℕ) (u : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  (missedLayerSenders q D V T u z).filter (fun b => outN D M b ∩ inN D M z = ∅)

theorem missedLayerSenders_subset {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    {u : ℕ → ℕ} {z : ℕ} : missedLayerSenders q D V T u z ⊆ T := by
  intro b hb
  exact (mem_inter.mp (mem_filter.mp hb).1).1

/-- A finite nonnegative cover count, without injectivity or graph geometry. -/
theorem common_head_pair_count {D : CH.Digraph} {M T H : Finset ℕ}
    (hHT : H ⊆ T) (p : ℕ → ℚ) (hp : ∀ b ∈ T, 0 ≤ p b) (z : ℕ) :
    mass H p ≤ (∑ r ∈ inN D M z, inW D T p r) +
      mass (H.filter (fun b => outN D M b ∩ inN D M z = ∅)) p := by
  classical
  have heach : ∀ b ∈ H, p b ≤
      (∑ r ∈ inN D M z, if D b r = true then p b else 0) +
        (if outN D M b ∩ inN D M z = ∅ then p b else 0) := by
    intro b hb
    have hpb := hp b (hHT hb)
    have hn : 0 ≤ ∑ r ∈ inN D M z, if D b r = true then p b else 0 :=
      sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    by_cases h : outN D M b ∩ inN D M z = ∅
    · rw [if_pos h]
      linarith
    · rw [if_neg h, add_zero]
      obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨hrb, hrz⟩ := mem_inter.mp hr
      have hs := single_le_sum (f := fun r => if D b r = true then p b else 0)
        (fun _ _ => by split_ifs <;> positivity) hrz
      simpa only [(mem_outN.mp hrb).2, ite_true] using hs
  have hh := sum_le_sum heach
  have ht : (∑ b ∈ H, ∑ r ∈ inN D M z, if D b r = true then p b else 0) ≤
      ∑ b ∈ T, ∑ r ∈ inN D M z, if D b r = true then p b else 0 := by
    apply sum_le_sum_of_subset_of_nonneg hHT
    intro b hb _
    have hpb := hp b hb
    exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  have he : (∑ b ∈ T, ∑ r ∈ inN D M z, if D b r = true then p b else 0) =
      ∑ r ∈ inN D M z, inW D T p r := by
    rw [sum_comm]
    rfl
  rw [he] at ht
  simp only [sum_add_distrib] at hh
  change (∑ b ∈ H, p b) ≤ _
  simp only [mass, sum_filter]
  linarith

theorem missed_common_head_point {q : ℕ} {D : CH.Digraph} {V M T : Finset ℕ}
    (u : ℕ → ℕ) (p : ℕ → ℚ) (hp : ∀ b ∈ T, 0 ≤ p b) (z : ℕ) :
    mass (missedLayerSenders q D V T u z) p ≤
      (∑ r ∈ inN D M z, inW D T p r) + mass (uncoveredLayerSenders q D V M T u z) p :=
  common_head_pair_count missedLayerSenders_subset p hp z

/-- The actual T,F bound retains the actual selector and uncovered-pair mass. -/
theorem missed_common_head_bound {q : ℕ} {D : CH.Digraph} {V M T F : Finset ℕ}
    (u : ℕ → ℕ) (w p : ℕ → ℚ)
    (hw : ∀ z ∈ F, 0 ≤ w z) (hp : ∀ b ∈ T, 0 ≤ p b) :
    (∑ z ∈ F, mass (missedLayerSenders q D V T u z) p * w z) ≤
      (∑ r ∈ M, inW D T p r * outW D F w r) +
        ∑ z ∈ F, mass (uncoveredLayerSenders q D V M T u z) p * w z := by
  have h := sum_le_sum (fun z hz =>
    mul_le_mul_of_nonneg_right
      (missed_common_head_point (q := q) (D := D) (V := V) (M := M) u p hp z) (hw z hz))
  have he : (∑ z ∈ F, (∑ r ∈ inN D M z, inW D T p r) * w z) =
      ∑ r ∈ M, inW D T p r * outW D F w r := by
    simp only [inN, sum_filter, sum_mul, outW, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro z hz
    split_ifs <;> ring
  simp only [add_mul, sum_add_distrib] at h
  rwa [he] at h

theorem uncoveredLayerSenders_eq_empty_of_coverage {q : ℕ} {D : CH.Digraph}
    {V M T : Finset ℕ} {u : ℕ → ℕ} {z : ℕ}
    (hcover : ∀ b ∈ missedLayerSenders q D V T u z,
      (outN D M b ∩ inN D M z).Nonempty) :
    uncoveredLayerSenders q D V M T u z = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨hb, he⟩ := mem_filter.mp hb
  exact (hcover b hb).ne_empty he

/-- Coverage is an explicit premise; this theorem does not supply it. -/
theorem missed_common_head_bound_of_coverage {q : ℕ} {D : CH.Digraph}
    {V M T F : Finset ℕ} (u : ℕ → ℕ) (w p : ℕ → ℚ)
    (hw : ∀ z ∈ F, 0 ≤ w z) (hp : ∀ b ∈ T, 0 ≤ p b)
    (hcover : ∀ z ∈ F, ∀ b ∈ missedLayerSenders q D V T u z,
      (outN D M b ∩ inN D M z).Nonempty) :
    (∑ z ∈ F, mass (missedLayerSenders q D V T u z) p * w z) ≤
      ∑ r ∈ M, inW D T p r * outW D F w r := by
  have h := missed_common_head_bound (q := q) (D := D) (V := V) (M := M) u w p hw hp
  have hz : (∑ z ∈ F, mass (uncoveredLayerSenders q D V M T u z) p * w z) = 0 := by
    apply sum_eq_zero
    intro z hz
    rw [uncoveredLayerSenders_eq_empty_of_coverage (hcover z hz)]
    simp [mass]
  simpa only [hz, add_zero] using h

/-- Exact equalizer cut factors bound the actual T,F wedge capacity.
The value c is arbitrary and there is no normalization or q positivity premise. -/
theorem common_head_exterior_capacity {q : ℕ} {D : CH.Digraph} {V M T F : Finset ℕ}
    (hMV : M ⊆ V) (hT : T ⊆ V \ M) (hF : F ⊆ V \ M)
    (w p : ℕ → ℚ) (hw : ∀ z ∈ V, 0 ≤ w z) (hp : ∀ b ∈ V, 0 ≤ p b)
    (c : ℚ) (hr : ∀ r ∈ M, row q D V w r = c) (hc : ∀ r ∈ M, col q D V p r = c) :
    (q : ℚ)^2 * (∑ r ∈ M, inW D T p r * outW D F w r) ≤
      ∑ r ∈ M, (c - col q D M p r) * (c - row q D M w r) := by
  rw [mul_sum]
  apply sum_le_sum
  intro r hrM
  have hi : inW D T p r ≤ inW D (V \ M) p r := by
    apply sum_le_sum_of_subset_of_nonneg hT
    intro b hb _
    have hpb := hp b (mem_sdiff.mp hb).1
    split_ifs <;> positivity
  have ho : outW D F w r ≤ outW D (V \ M) w r := by
    apply sum_le_sum_of_subset_of_nonneg hF
    intro z hz _
    have hwz := hw z (mem_sdiff.mp hz).1
    split_ifs <;> positivity
  have hno : 0 ≤ outW D F w r := by
    apply sum_nonneg
    intro z hz
    have hwz := hw z (mem_sdiff.mp (hF hz)).1
    split_ifs <;> positivity
  have hni : 0 ≤ inW D (V \ M) p r := by
    apply sum_nonneg
    intro b hb
    have hpb := hp b (mem_sdiff.mp hb).1
    split_ifs <;> positivity
  have hprod := mul_le_mul_of_nonneg_left (mul_le_mul hi ho hno hni) (sq_nonneg (q : ℚ))
  have hout : (q : ℚ) * outW D (V \ M) w r = c - row q D M w r := by
    have h := row_cut_split (q := q) (D := D) hMV w r
    rw [hr r hrM] at h
    linarith
  have hin : (q : ℚ) * inW D (V \ M) p r = c - col q D M p r := by
    have h := row_cut_split (q := q) (D := fun a b => D b a) hMV p r
    change col q D V p r = col q D M p r + q * inW D (V \ M) p r at h
    rw [hc r hrM] at h
    linarith
  apply hprod.trans_eq
  rw [← hin, ← hout]
  ring

/-- Unconditional: uncovered bad pairs are retained in full. -/
theorem missed_common_head_exterior_bound {q : ℕ} {D : CH.Digraph}
    {V M T F : Finset ℕ} (hMV : M ⊆ V) (hT : T ⊆ V \ M) (hF : F ⊆ V \ M)
    (u : ℕ → ℕ) (w p : ℕ → ℚ)
    (hw : ∀ z ∈ V, 0 ≤ w z) (hp : ∀ b ∈ V, 0 ≤ p b)
    (c : ℚ) (hr : ∀ r ∈ M, row q D V w r = c) (hc : ∀ r ∈ M, col q D V p r = c) :
    (q : ℚ)^2 * (∑ z ∈ F, mass (missedLayerSenders q D V T u z) p * w z) ≤
      (∑ r ∈ M, (c - col q D M p r) * (c - row q D M w r)) +
        (q : ℚ)^2 * (∑ z ∈ F, mass (uncoveredLayerSenders q D V M T u z) p * w z) := by
  have h := mul_le_mul_of_nonneg_left
    (missed_common_head_bound (q := q) (D := D) (V := V) (M := M) u w p
      (fun z hz => hw z (mem_sdiff.mp (hF hz)).1)
      (fun b hb => hp b (mem_sdiff.mp (hT hb)).1)) (sq_nonneg (q : ℚ))
  rw [mul_add] at h
  exact h.trans (add_le_add (common_head_exterior_capacity hMV hT hF w p hw hp c hr hc) le_rfl)

theorem missed_common_head_exterior_bound_of_coverage {q : ℕ} {D : CH.Digraph}
    {V M T F : Finset ℕ} (hMV : M ⊆ V) (hT : T ⊆ V \ M) (hF : F ⊆ V \ M)
    (u : ℕ → ℕ) (w p : ℕ → ℚ)
    (hw : ∀ z ∈ V, 0 ≤ w z) (hp : ∀ b ∈ V, 0 ≤ p b)
    (c : ℚ) (hr : ∀ r ∈ M, row q D V w r = c) (hc : ∀ r ∈ M, col q D V p r = c)
    (hcover : ∀ z ∈ F, ∀ b ∈ missedLayerSenders q D V T u z,
      (outN D M b ∩ inN D M z).Nonempty) :
    (q : ℚ)^2 * (∑ z ∈ F, mass (missedLayerSenders q D V T u z) p * w z) ≤
      ∑ r ∈ M, (c - col q D M p r) * (c - row q D M w r) := by
  have h := mul_le_mul_of_nonneg_left
    (missed_common_head_bound_of_coverage u w p
      (fun z hz => hw z (mem_sdiff.mp (hF hz)).1)
      (fun b hb => hp b (mem_sdiff.mp (hT hb)).1) hcover) (sq_nonneg (q : ℚ))
  exact h.trans (common_head_exterior_capacity hMV hT hF w p hw hp c hr hc)

end LeanCH.BR.WeightedSD
