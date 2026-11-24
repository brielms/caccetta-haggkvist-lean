import LeanCH.BR.BRWeightedGapDischarge

/-! Actual sender-indexed loads are bounded by the column equalizer.
Each sender is counted once. No private-witness or normalized selector
assumption is used. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem gapLoad_nonparent_bound {D : CH.Digraph} {V T : Finset ℕ}
    (hTV : T ⊆ V) (u : ℕ → ℕ) (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (z : ℕ) :
    gapLoad D V T u id p z + inW D V p z ≤ mass V p := by
  let S := T.filter (fun b => z ∈ outGap D V (u b) b)
  have hs : S ⊆ V \ inN D V z := by
    intro b hb
    obtain ⟨hbT, hgap⟩ := Finset.mem_filter.mp hb
    have hnbz := (mem_outGap.mp hgap).2.2
    exact Finset.mem_sdiff.mpr ⟨hTV hbT, fun h => hnbz (mem_inN.mp h).2⟩
  have hle := mass_mono hs (fun b hb => hp b (Finset.mem_sdiff.mp hb).1)
  have he : mass S p = gapLoad D V T u id p z := by
    simp only [S, mass, Finset.sum_filter, gapLoad, id_eq]
  rw [he] at hle
  have hsum := Finset.sum_sdiff (Finset.filter_subset (fun b => D b z = true) V) (f := p)
  have hin : mass (inN D V z) p = inW D V p z := by
    simp only [mass, inN, Finset.sum_filter, inW]
  change mass (V \ inN D V z) p + mass (inN D V z) p = mass V p at hsum
  rw [hin] at hsum
  linarith

theorem gapLoad_cycle_parent_bound {D : CH.Digraph} {V M T : Finset ℕ}
    (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ M)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (z : ℕ) :
    gapLoad D V T u id p z ≤ ∑ v ∈ inN D M z, inW D V p v := by
  have ht : ∀ b ∈ T,
      (if z ∈ outGap D V (u b) b then p b else 0) ≤
        ∑ v ∈ inN D M z, if D b v = true then p b else 0 := by
    intro b hb
    have hpb := hp b (hTV hb)
    by_cases h : z ∈ outGap D V (u b) b
    · rw [if_pos h]
      have hub : u b ∈ inN D M z := mem_inN.mpr ⟨hu b hb, (mem_outGap.mp h).2.1⟩
      have hs := Finset.single_le_sum
        (f := fun v => if D b v = true then p b else 0)
        (fun v _ => by split_ifs <;> positivity) hub
      simpa only [harc b hb, ite_true] using hs
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun v _ => by split_ifs <;> positivity)
  have hT := Finset.sum_le_sum ht
  have hV : (∑ b ∈ T, ∑ v ∈ inN D M z, if D b v = true then p b else 0) ≤
      ∑ b ∈ V, ∑ v ∈ inN D M z, if D b v = true then p b else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hTV
    intro b hb _
    have hpb := hp b hb
    exact Finset.sum_nonneg (fun v _ => by split_ifs <;> positivity)
  have he : (∑ b ∈ V, ∑ v ∈ inN D M z, if D b v = true then p b else 0) =
      ∑ v ∈ inN D M z, inW D V p v := by rw [Finset.sum_comm]; rfl
  exact hT.trans (hV.trans_eq he)

theorem gapLoad_column_caps {q : ℕ} {D : CH.Digraph} {V M T : Finset ℕ}
    (hMV : M ⊆ V) (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ M)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (hm : mass V p = 1)
    (c : ℚ) (hc : ∀ v ∈ V, col q D V p v = c) {z : ℕ} (hz : z ∈ V) :
    (q : ℚ) * gapLoad D V T u id p z ≤
      min (q - c + p z) (c * (inN D M z).card - mass (inN D M z) p) := by
  apply le_min
  · have h := gapLoad_nonparent_bound (D := D) hTV u p hp z
    have hcol := hc z hz
    rw [hm] at h
    unfold col at hcol
    have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (gapLoad_cycle_parent_bound hTV u hu harc p hp z)
      (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
    have he : (q : ℚ) * (∑ v ∈ inN D M z, inW D V p v) =
        c * (inN D M z).card - mass (inN D M z) p := by
      rw [Finset.mul_sum]
      have heach : ∀ v ∈ inN D M z, (q : ℚ) * inW D V p v = c - p v := by
        intro v hv
        have hcol := hc v (hMV (mem_inN.mp hv).1)
        unfold col at hcol
        linarith
      simp only [Finset.sum_congr rfl heach, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, mass]
      ring
    rwa [he] at h

theorem cycle_load_charge_bound {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V M T : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ M)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hm : mass V p = 1) (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c)
    (hc : ∀ v ∈ V, col q D V p v = c) :
    (∑ b ∈ T, p b * ((q - 1 : ℚ) * w (u b) + w b)) ≤
      ∑ z ∈ V, min (q - c + p z)
        (c * (inN D M z).card - mass (inN D M z) p) * w z := by
  have hl := weighted_gap_discharge_bound u id p w (fun b hb => hp b (hTV hb)) hw
    (fun b hb => hMV (hu b hb)) harc
    (fun b hb => loopfree hf hq (hMV (hu b hb)))
    (fun b hb => (hr (u b) (hMV (hu b hb))).trans (hr b (hTV hb)).symm)
  apply hl.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have h := mul_le_mul_of_nonneg_right
    (gapLoad_column_caps hMV hTV u hu harc p hp hm c hc hz) (hw z hz)
  simpa only [mul_assoc] using h

/-- Saturation places every contributing sender at distance exactly `q - 1`.
The exclusion of the earlier ball uses a real short closed walk. -/
theorem gap_sender_last_layer {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    {u b z : ℕ} (hu : u ∈ V) (hb : b ∈ V) (hbu : D b u = true)
    (hz : z ∈ outGap D V u b) :
    b ∈ ball D V z (q - 1) \ ball D V z (q - 2) := by
  exact Finset.mem_sdiff.mpr
    ⟨hsat z (mem_outGap.mp hz).1 b hb (mem_outGap.mp hz).2.2,
      outGap_no_short_return (by omega) hf hu hb hbu hz⟩

theorem gapLoad_last_layer_bound {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ V)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (z : ℕ) :
    gapLoad D V T u id p z ≤ mass (ball D V z (q - 1) \ ball D V z (q - 2)) p := by
  let S := T.filter (fun b => z ∈ outGap D V (u b) b)
  have hs : S ⊆ ball D V z (q - 1) \ ball D V z (q - 2) := by
    intro b hb
    obtain ⟨hbT, hgap⟩ := Finset.mem_filter.mp hb
    exact gap_sender_last_layer hq hf hsat (hu b hbT) (hTV hbT) (harc b hbT) hgap
  have hle := mass_mono hs (fun b hb => hp b (ball_subset (Finset.mem_sdiff.mp hb).1))
  have he : mass S p = gapLoad D V T u id p z := by
    simp only [S, mass, Finset.sum_filter, gapLoad, id_eq]
  rwa [he] at hle

/-- The last-layer column capacity, with the earlier-ball mass kept explicit. -/
theorem last_layer_column_mass {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (p : ℕ → ℚ) (hm : mass V p = 1) (c : ℚ)
    {z : ℕ} (hz : z ∈ V) (hc : col q D V p z = c) :
    (q : ℚ) * mass (ball D V z (q - 1) \ ball D V z (q - 2)) p =
      q - c + p z - q * mass (ball D V z (q - 2)) p := by
  have hs := Finset.sum_sdiff (ball_subset (D := D) (W := V) (u := z) (k := q - 1))
    (f := p)
  change mass (V \ ball D V z (q - 1)) p + mass (ball D V z (q - 1)) p = mass V p at hs
  rw [← inN_eq_of_satQ (by omega) hf hsat hz] at hs
  have hi : mass (inN D V z) p = inW D V p z := by
    simp only [mass, inN, Finset.sum_filter, inW]
  rw [hi, hm] at hs
  have hl := Finset.sum_sdiff
    (ball_mono_radius (D := D) (W := V) (u := z) (by omega : q - 2 ≤ q - 1)) (f := p)
  change mass (ball D V z (q - 1) \ ball D V z (q - 2)) p +
    mass (ball D V z (q - 2)) p = mass (ball D V z (q - 1)) p at hl
  unfold col at hc
  nlinarith

theorem gapLoad_last_layer_caps {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ M)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (hm : mass V p = 1)
    (c : ℚ) (hc : ∀ v ∈ V, col q D V p v = c) {z : ℕ} (hz : z ∈ V) :
    (q : ℚ) * gapLoad D V T u id p z ≤
      min (q - c + p z - q * mass (ball D V z (q - 2)) p)
        (c * (inN D M z).card - mass (inN D M z) p) := by
  apply le_min
  · have h := mul_le_mul_of_nonneg_left
      (gapLoad_last_layer_bound hq hf hsat hTV u (fun b hb => hMV (hu b hb)) harc p hp z)
      (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
    rwa [last_layer_column_mass hq hf hsat p hm c hz (hc z hz)] at h
  · exact (gapLoad_column_caps hMV hTV u hu harc p hp hm c hc hz).trans (min_le_right _ _)

theorem cycle_last_layer_charge_bound {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ M)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hm : mass V p = 1) (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c)
    (hc : ∀ v ∈ V, col q D V p v = c) :
    (∑ b ∈ T, p b * ((q - 1 : ℚ) * w (u b) + w b)) ≤
      ∑ z ∈ V, min (q - c + p z - q * mass (ball D V z (q - 2)) p)
        (c * (inN D M z).card - mass (inN D M z) p) * w z := by
  have hl := weighted_gap_discharge_bound u id p w (fun b hb => hp b (hTV hb)) hw
    (fun b hb => hMV (hu b hb)) harc
    (fun b hb => loopfree hf (by omega : 1 ≤ q) (hMV (hu b hb)))
    (fun b hb => (hr (u b) (hMV (hu b hb))).trans (hr b (hTV hb)).symm)
  apply hl.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have h := mul_le_mul_of_nonneg_right
    (gapLoad_last_layer_caps hq hf hsat hMV hTV u hu harc p hp hm c hc hz) (hw z hz)
  simpa only [mul_assoc] using h

end LeanCH.BR.WeightedSD
