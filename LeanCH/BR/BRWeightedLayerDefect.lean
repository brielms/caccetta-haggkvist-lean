import LeanCH.BR.BRWeightedCycleSenderFamily

/-! The actual sender part of a last layer, and its exact unused incidence.
Both the omitted-sender mass and the selected-head defect are retained. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def senderLastLayer (q : ℕ) (D : CH.Digraph) (V T : Finset ℕ) (z : ℕ) : Finset ℕ :=
  T ∩ (ball D V z (q - 1) \ ball D V z (q - 2))

noncomputable def missedLayerSenders (q : ℕ) (D : CH.Digraph) (V T : Finset ℕ)
    (u : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  (senderLastLayer q D V T z).filter (fun b => ¬ D (u b) z = true)

theorem gap_iff_last_layer_head {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    {u b z : ℕ} (hu : u ∈ V) (hb : b ∈ V) (hz : z ∈ V) (hbu : D b u = true) :
    z ∈ outGap D V u b ↔
      b ∈ ball D V z (q - 1) \ ball D V z (q - 2) ∧ D u z = true := by
  constructor
  · intro h
    exact ⟨gap_sender_last_layer hq hf hsat hu hb hbu h, (mem_outGap.mp h).2.1⟩
  · rintro ⟨hl, huz⟩
    exact mem_outGap.mpr ⟨hz, huz,
      no_back_arc hf hz (Finset.mem_sdiff.mp hl).1 (by omega)⟩

theorem gapLoad_add_missed_mass {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ V)
    (harc : ∀ b ∈ T, D b (u b) = true) (p : ℕ → ℚ) {z : ℕ} (hz : z ∈ V) :
    gapLoad D V T u id p z + mass (missedLayerSenders q D V T u z) p =
      mass (senderLastLayer q D V T z) p := by
  have he : T.filter (fun b => z ∈ outGap D V (u b) b) =
      (senderLastLayer q D V T z).filter (fun b => D (u b) z = true) := by
    ext b
    simp only [Finset.mem_filter, senderLastLayer, Finset.mem_inter]
    constructor
    · rintro ⟨hb, hg⟩
      obtain ⟨hl, hz⟩ := (gap_iff_last_layer_head hq hf hsat (hu b hb) (hTV hb) hz (harc b hb)).mp hg
      exact ⟨⟨hb, hl⟩, hz⟩
    · rintro ⟨⟨hb, hl⟩, huz⟩
      exact ⟨hb, (gap_iff_last_layer_head hq hf hsat (hu b hb) (hTV hb) hz (harc b hb)).mpr ⟨hl, huz⟩⟩
  have hg : gapLoad D V T u id p z =
      mass ((senderLastLayer q D V T z).filter (fun b => D (u b) z = true)) p := by
    rw [← he]
    simp only [gapLoad, mass, Finset.sum_filter, id_eq]
  rw [hg]
  simp only [missedLayerSenders, mass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : D (u b) z = true <;> simp [h]

theorem gapLoad_actual_family_bound {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ V)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) {z : ℕ} (hz : z ∈ V) :
    gapLoad D V T u id p z ≤ mass (senderLastLayer q D V T z) p := by
  have h := gapLoad_add_missed_mass hq hf hsat hTV u hu harc p hz
  have hn : 0 ≤ mass (missedLayerSenders q D V T u z) p := by
    apply mass_nonneg
    intro b hb
    exact hp b (hTV (Finset.mem_inter.mp (Finset.mem_filter.mp hb).1).1)
  linarith

theorem actual_sender_layer_column_mass {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (p : ℕ → ℚ) (hm : mass V p = 1) (c : ℚ)
    {z : ℕ} (hz : z ∈ V) (hc : col q D V p z = c) :
    (q : ℚ) * mass (senderLastLayer q D V T z) p =
      q - c + p z - q * mass (ball D V z (q - 2)) p -
        q * mass ((ball D V z (q - 1) \ ball D V z (q - 2)) \ T) p := by
  let L := ball D V z (q - 1) \ ball D V z (q - 2)
  have hsub : senderLastLayer q D V T z ⊆ L := Finset.inter_subset_right
  have he : L \ senderLastLayer q D V T z = L \ T := by
    ext b
    simp only [L, Finset.mem_sdiff, senderLastLayer, Finset.mem_inter]
    tauto
  have hs := Finset.sum_sdiff hsub (f := p)
  change mass (L \ senderLastLayer q D V T z) p +
    mass (senderLastLayer q D V T z) p = mass L p at hs
  rw [he] at hs
  have h := last_layer_column_mass hq hf hsat p hm c hz hc
  change (q : ℚ) * mass L p = _ at h
  change (q : ℚ) * mass (senderLastLayer q D V T z) p =
    q - c + p z - q * mass (ball D V z (q - 2)) p - q * mass (L \ T) p
  nlinarith

theorem last_layer_exact_walk {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {z b : ℕ}
    (hb : b ∈ ball D V z (q - 1) \ ball D V z (q - 2)) : Walk D V z b (q - 1) := by
  obtain ⟨hbV, k, hk, wk⟩ := mem_ball.mp (Finset.mem_sdiff.mp hb).1
  have hn := (Finset.mem_sdiff.mp hb).2
  have he : k = q - 1 := by
    by_contra h
    exact hn (mem_ball.mpr ⟨hbV, k, by omega, wk⟩)
  rwa [he] at wk

/-- A missed incidence has a real last-layer return and a second saturated
return to the selected head. These paths are not assumed to be disjoint. -/
theorem missed_layer_return_paths {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T : Finset ℕ} (hsat : Sat q D V)
    (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ V) {z b : ℕ} (hz : z ∈ V)
    (hb : b ∈ missedLayerSenders q D V T u z) :
    Walk D V z b (q - 1) ∧ u b ∈ ball D V z (q - 1) := by
  obtain ⟨hbL, hn⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbT, hbL⟩ := Finset.mem_inter.mp hbL
  exact ⟨last_layer_exact_walk hq hbL, hsat z hz (u b) (hu b hbT) hn⟩

theorem weighted_layer_discharge_exact {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hTV : T ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ V)
    (harc : ∀ b ∈ T, D b (u b) = true) (w p : ℕ → ℚ)
    (he : ∀ b ∈ T, row q D V w (u b) = row q D V w b) :
    (∑ b ∈ T, p b * ((q - 1 : ℚ) * w (u b) + w b)) +
      q * (∑ b ∈ T, p b * mass ((outGap D V b (u b)).erase (u b)) w) +
      q * (∑ z ∈ V, mass (missedLayerSenders q D V T u z) p * w z) =
      q * (∑ z ∈ V, mass (senderLastLayer q D V T z) p * w z) := by
  have hg := weighted_gap_discharge_exact u id p w hu harc
    (fun b hb => loopfree hf (by omega : 1 ≤ q) (hu b hb)) he
  simp only [id_eq] at hg
  rw [← hg, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [← add_mul, gapLoad_add_missed_mass hq hf hsat hTV u hu harc p hz]

theorem weighted_layer_discharge_on {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V T R : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hTV : T ⊆ V) (hRV : R ⊆ V) (u : ℕ → ℕ) (hu : ∀ b ∈ T, u b ∈ V)
    (harc : ∀ b ∈ T, D b (u b) = true)
    (hsupport : ∀ b ∈ T, outGap D V (u b) b ⊆ R) (w p : ℕ → ℚ)
    (he : ∀ b ∈ T, row q D V w (u b) = row q D V w b) :
    (∑ b ∈ T, p b * ((q - 1 : ℚ) * w (u b) + w b)) +
      q * (∑ b ∈ T, p b * mass ((outGap D V b (u b)).erase (u b)) w) +
      q * (∑ z ∈ R, mass (missedLayerSenders q D V T u z) p * w z) =
      q * (∑ z ∈ R, mass (senderLastLayer q D V T z) p * w z) := by
  have hg := weighted_gap_discharge_exact u id p w hu harc
    (fun b hb => loopfree hf (by omega : 1 ≤ q) (hu b hb)) he
  have hs : (∑ z ∈ V, gapLoad D V T u id p z * w z) =
      ∑ z ∈ R, gapLoad D V T u id p z * w z := by
    symm
    apply Finset.sum_subset hRV
    intro z hz hn
    have hz0 : gapLoad D V T u id p z = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hng : z ∉ outGap D V (u b) b := fun h => hn (hsupport b hb h)
      simp only [id_eq, hng, ite_false]
    rw [hz0, zero_mul]
  rw [hs] at hg
  simp only [id_eq] at hg
  rw [← hg, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [← add_mul, gapLoad_add_missed_mass hq hf hsat hTV u hu harc p (hRV hz)]

theorem cycle_exterior_layer_ledger {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hout : OutEq 1 D M) (u : ℕ → ℕ)
    (hu : ∀ b ∈ consecutiveCycleSenders D V M,
      u b ∈ outN D M b ∧ ∃ v ∈ outN D M b, D (u b) v = true)
    (w p : ℕ → ℚ) (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c) :
    (∑ b ∈ consecutiveCycleSenders D V M, p b * ((q - 1 : ℚ) * w (u b) + w b)) +
      q * (∑ b ∈ consecutiveCycleSenders D V M,
        p b * mass ((outGap D V b (u b)).erase (u b)) w) +
      q * (∑ z ∈ V \ M,
        mass (missedLayerSenders q D V (consecutiveCycleSenders D V M) u z) p * w z) =
      q * (∑ z ∈ V \ M,
        mass (senderLastLayer q D V (consecutiveCycleSenders D V M) z) p * w z) := by
  have hTV : consecutiveCycleSenders D V M ⊆ V :=
    fun b hb => (Finset.mem_sdiff.mp (consecutiveCycleSenders_subset hb)).1
  exact weighted_layer_discharge_on hq hf hsat hTV Finset.sdiff_subset u
    (fun b hb => hMV (outN_subset (hu b hb).1))
    (fun b hb => (mem_outN.mp (hu b hb).1).2)
    (fun b hb => consecutive_sender_gap_exterior hout (hu b hb).1 (hu b hb).2) w p
    (fun b hb => (hr (u b) (hMV (outN_subset (hu b hb).1))).trans (hr b (hTV hb)).symm)

/-- The exterior ledger uses the actual family, not the whole last layer.
The missing selected-head term is explicit and is not set to zero. -/
theorem exists_cycle_exterior_layer_ledger {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hMV : M ⊆ V) (hout : OutEq 1 D M) (w p : ℕ → ℚ)
    (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c) :
    ∃ u : ℕ → ℕ,
      (∀ b ∈ consecutiveCycleSenders D V M,
        u b ∈ outN D M b ∧ ∃ v ∈ outN D M b, D (u b) v = true) ∧
      (∑ b ∈ consecutiveCycleSenders D V M, p b * ((q - 1 : ℚ) * w (u b) + w b)) +
        q * (∑ b ∈ consecutiveCycleSenders D V M,
          p b * mass ((outGap D V b (u b)).erase (u b)) w) +
        q * (∑ z ∈ V \ M,
          mass (missedLayerSenders q D V (consecutiveCycleSenders D V M) u z) p * w z) =
        q * (∑ z ∈ V \ M,
          mass (senderLastLayer q D V (consecutiveCycleSenders D V M) z) p * w z) := by
  classical
  obtain ⟨u, hu⟩ := exists_consecutive_cycle_selector D V M
  exact ⟨u, hu, cycle_exterior_layer_ledger hq hf hsat hMV hout u hu w p c hr⟩

end LeanCH.BR.WeightedSD
