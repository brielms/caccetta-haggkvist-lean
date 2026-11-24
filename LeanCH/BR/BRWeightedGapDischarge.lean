import LeanCH.BR.BRWeightedArcGap

/-! Sum actual escape charges with their full multiplicities. Local separation
for one path does not make escape sets from different paths disjoint. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def gapMultiplicity (D : CH.Digraph) (V T : Finset ℕ) (u b : ℕ → ℕ) (z : ℕ) : ℕ :=
  (T.filter (fun t => z ∈ outGap D V (u t) (b t))).card

def gapLoad (D : CH.Digraph) (V T : Finset ℕ) (u b : ℕ → ℕ)
    (r : ℕ → ℚ) (z : ℕ) : ℚ :=
  ∑ t ∈ T, if z ∈ outGap D V (u t) (b t) then r t else 0

theorem sum_gap_mass (D : CH.Digraph) (V T : Finset ℕ) (u b : ℕ → ℕ) (w : ℕ → ℚ) :
    (∑ t ∈ T, mass (outGap D V (u t) (b t)) w) =
      ∑ z ∈ V, (gapMultiplicity D V T u b z : ℚ) * w z := by
  have hm (t : ℕ) : mass (outGap D V (u t) (b t)) w =
      ∑ z ∈ V, if z ∈ outGap D V (u t) (b t) then w z else 0 := by
    have he : V.filter (fun z => z ∈ outGap D V (u t) (b t)) =
        outGap D V (u t) (b t) := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(mem_outGap.mp h).1, h⟩⟩
    rw [← Finset.sum_filter, he]
    rfl
  simp only [Finset.sum_congr rfl (fun t _ => hm t)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, gapMultiplicity]

theorem gap_discharge_exact {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    (u b : ℕ → ℕ) (w : ℕ → ℚ)
    (hu : ∀ t ∈ T, u t ∈ V) (harc : ∀ t ∈ T, D (b t) (u t) = true)
    (hloop : ∀ t ∈ T, ¬ D (u t) (u t) = true)
    (he : ∀ t ∈ T, row q D V w (u t) = row q D V w (b t)) :
    (q : ℚ) * (∑ z ∈ V, (gapMultiplicity D V T u b z : ℚ) * w z) =
      (∑ t ∈ T, ((q - 1 : ℚ) * w (u t) + w (b t))) +
        q * ∑ t ∈ T, mass ((outGap D V (b t) (u t)).erase (u t)) w := by
  rw [← sum_gap_mass, Finset.mul_sum]
  simp only [Finset.sum_congr rfl (fun t ht =>
    equal_rows_arc_gap_exact w (hu t ht) (harc t ht) (hloop t ht) (he t ht)),
    Finset.sum_add_distrib, ← Finset.mul_sum]

theorem gap_discharge_bound {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    (u b : ℕ → ℕ) (w : ℕ → ℚ) (hw : ∀ z ∈ V, 0 ≤ w z)
    (hu : ∀ t ∈ T, u t ∈ V) (harc : ∀ t ∈ T, D (b t) (u t) = true)
    (hloop : ∀ t ∈ T, ¬ D (u t) (u t) = true)
    (he : ∀ t ∈ T, row q D V w (u t) = row q D V w (b t)) :
    (∑ t ∈ T, ((q - 1 : ℚ) * w (u t) + w (b t))) ≤
      (q : ℚ) * ∑ z ∈ V, (gapMultiplicity D V T u b z : ℚ) * w z := by
  have hs := Finset.sum_le_sum (fun t ht =>
    equal_rows_arc_gap_lower w hw (hu t ht) (harc t ht) (hloop t ht) (he t ht))
  rwa [← Finset.mul_sum, sum_gap_mass] at hs

theorem sum_weighted_gap_mass (D : CH.Digraph) (V T : Finset ℕ)
    (u b : ℕ → ℕ) (r w : ℕ → ℚ) :
    (∑ t ∈ T, r t * mass (outGap D V (u t) (b t)) w) =
      ∑ z ∈ V, gapLoad D V T u b r z * w z := by
  have hm (t : ℕ) : mass (outGap D V (u t) (b t)) w =
      ∑ z ∈ V, if z ∈ outGap D V (u t) (b t) then w z else 0 := by
    have he : V.filter (fun z => z ∈ outGap D V (u t) (b t)) =
        outGap D V (u t) (b t) := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(mem_outGap.mp h).1, h⟩⟩
    rw [← Finset.sum_filter, he]
    rfl
  simp only [Finset.sum_congr rfl (fun t _ => congrArg (fun s => r t * s) (hm t)),
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [gapLoad, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : z ∈ outGap D V (u t) (b t) <;> simp [h]

theorem weighted_gap_discharge_exact {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    (u b : ℕ → ℕ) (r w : ℕ → ℚ)
    (hu : ∀ t ∈ T, u t ∈ V) (harc : ∀ t ∈ T, D (b t) (u t) = true)
    (hloop : ∀ t ∈ T, ¬ D (u t) (u t) = true)
    (he : ∀ t ∈ T, row q D V w (u t) = row q D V w (b t)) :
    (q : ℚ) * (∑ z ∈ V, gapLoad D V T u b r z * w z) =
      (∑ t ∈ T, r t * ((q - 1 : ℚ) * w (u t) + w (b t))) +
        q * ∑ t ∈ T, r t * mass ((outGap D V (b t) (u t)).erase (u t)) w := by
  rw [← sum_weighted_gap_mass, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have h := equal_rows_arc_gap_exact w (hu t ht) (harc t ht) (hloop t ht) (he t ht)
  calc
    _ = r t * ((q : ℚ) * mass (outGap D V (u t) (b t)) w) := by ring
    _ = _ := by rw [h]; ring

theorem weighted_gap_discharge_bound {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    (u b : ℕ → ℕ) (r w : ℕ → ℚ) (hr : ∀ t ∈ T, 0 ≤ r t)
    (hw : ∀ z ∈ V, 0 ≤ w z)
    (hu : ∀ t ∈ T, u t ∈ V) (harc : ∀ t ∈ T, D (b t) (u t) = true)
    (hloop : ∀ t ∈ T, ¬ D (u t) (u t) = true)
    (he : ∀ t ∈ T, row q D V w (u t) = row q D V w (b t)) :
    (∑ t ∈ T, r t * ((q - 1 : ℚ) * w (u t) + w (b t))) ≤
      (q : ℚ) * ∑ z ∈ V, gapLoad D V T u b r z * w z := by
  rw [weighted_gap_discharge_exact u b r w hu harc hloop he]
  apply le_add_of_nonneg_right
  apply mul_nonneg (Nat.cast_nonneg q)
  apply Finset.sum_nonneg
  intro t ht
  apply mul_nonneg (hr t ht)
  exact mass_nonneg (fun z hz => hw z (mem_outGap.mp (Finset.mem_erase.mp hz).2).1)

end LeanCH.BR.WeightedSD
