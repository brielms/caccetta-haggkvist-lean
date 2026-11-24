import LeanCH.BR.BRArbitraryFoldGeometry
import LeanCH.BR.BRWeightedPositiveParentTransfer

/-! Fold accounting for arbitrary deleted sets and arbitrary receiver cuts.
The exact identities use only their displayed local hypotheses. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem fold_weight_mass {V S : Finset ℕ} {y : ℕ} (hSV : S ⊆ V)
    (hy : y ∈ V \ S) (a : ℕ → ℚ) :
    mass (V \ S) (addWeightAt a y (mass S a)) = mass V a := by
  rw [mass_addWeightAt hy]
  exact sum_sdiff hSV

theorem fold_receiver_row {q : ℕ} {D : CH.Digraph} {V S B : Finset ℕ} {y : ℕ}
    (hy : y ∈ V \ S) (hno : ∀ s ∈ S, ¬ D y s = true) (hloop : ¬ D y y = true)
    (hB : B ⊆ outN D V y) (a : ℕ → ℚ) :
    row q (foldGraph D V S B y) (V \ S) (addWeightAt a y (mass S a)) y =
      row q D V a y + mass S a - q * mass B a := by
  have hloopE : ¬ foldGraph D V S B y y y = true := by
    intro he
    obtain ⟨_, _, h | ⟨_, s, hs, hys⟩⟩ := of_decide_eq_true he
    · exact hloop (of_decide_eq_true h).1
    · exact hno s hs hys
  have hsplit : mass (outN D V y \ B) a + mass B a = outW D V a y := by
    rw [outW_eq_mass]
    exact sum_sdiff hB
  rw [row, outW_addWeightAt hy, if_neg hloopE, add_zero, outW_eq_mass,
    foldGraph_receiver_heads hy hno]
  simp only [addWeightAt, ite_true, row]
  rw [← hsplit]
  ring

theorem fold_other_row {q : ℕ} {D : CH.Digraph} {V S B : Finset ℕ} {y x : ℕ}
    (hSV : S ⊆ V) (hy : y ∈ V \ S)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (hx : x ∈ V \ S) (hxy : x ≠ y) :
    row q D V a x ≤ row q (foldGraph D V S B y) (V \ S)
      (addWeightAt a y (mass S a)) x := by
  have hA := mass_nonneg (fun s hs => ha s (hSV hs))
  have hkeep : outN D (V \ S) x ⊆ outN (foldGraph D V S B y) (V \ S) x := by
    intro z hz
    obtain ⟨hzK, hxz⟩ := mem_outN.mp hz
    exact mem_outN.mpr ⟨hzK, decide_eq_true ⟨hx, hzK, Or.inl
      (decide_eq_true ⟨hxz, fun h => hxy h.1⟩)⟩⟩
  have hmono : outW D (V \ S) a x ≤ outW (foldGraph D V S B y) (V \ S) a x := by
    rw [outW_eq_mass, outW_eq_mass]
    exact mass_mono hkeep (fun z hz => ha z (mem_sdiff.mp (outN_subset hz)).1)
  have hgain : outW D S a x ≤ if foldGraph D V S B y x y = true then mass S a else 0 := by
    by_cases hp : ∃ s ∈ S, D x s = true
    · have he : foldGraph D V S B y x y = true := decide_eq_true ⟨hx, hy, Or.inr ⟨rfl, hp⟩⟩
      rw [if_pos he, outW_eq_mass]
      exact mass_mono outN_subset (fun s hs => ha s (hSV hs))
    · have hz : outW D S a x = 0 := by
        apply sum_eq_zero
        intro s hs
        have hn : ¬ D x s = true := fun h => hp ⟨s, hs, h⟩
        simp [hn]
      rw [hz]
      split_ifs <;> linarith
  rw [row, row, outW_split hSV, outW_addWeightAt hy]
  simp only [addWeightAt, if_neg hxy, add_zero]
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  nlinarith

theorem fold_new_parent_gain {q : ℕ} {D : CH.Digraph} {V S B : Finset ℕ} {y x : ℕ}
    (hSV : S ⊆ V) (hy : y ∈ V \ S)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (hx : x ∈ V \ S) (hxy : x ≠ y)
    (hp : ∃ s ∈ S, D x s = true) (hnxy : ¬ D x y = true) :
    row q D V a x + q * a y ≤
      row q (foldGraph D V S B y) (V \ S) (addWeightAt a y (mass S a)) x := by
  have he : foldGraph D V S B y x y = true := decide_eq_true ⟨hx, hy, Or.inr ⟨rfl, hp⟩⟩
  have hsub : insert y (outN D (V \ S) x) ⊆ outN (foldGraph D V S B y) (V \ S) x := by
    apply insert_subset (mem_outN.mpr ⟨hy, he⟩)
    intro z hz
    obtain ⟨hzK, hxz⟩ := mem_outN.mp hz
    exact mem_outN.mpr ⟨hzK, decide_eq_true ⟨hx, hzK, Or.inl
      (decide_eq_true ⟨hxz, fun h => hxy h.1⟩)⟩⟩
  have hyn : y ∉ outN D (V \ S) x := fun h => hnxy (mem_outN.mp h).2
  have hmass := mass_mono hsub (fun z hz => ha z (mem_sdiff.mp (outN_subset hz)).1)
  have hs : mass (insert y (outN D (V \ S) x)) a = a y + mass (outN D (V \ S) x) a := sum_insert hyn
  rw [hs, ← outW_eq_mass, ← outW_eq_mass] at hmass
  have hloss : outW D S a x ≤ mass S a := by
    rw [outW_eq_mass]
    exact mass_mono outN_subset (fun s hs => ha s (hSV hs))
  rw [row, row, outW_split hSV, outW_addWeightAt hy, if_pos he]
  simp only [addWeightAt, if_neg hxy, add_zero]
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  nlinarith

theorem fold_feasible_of_budget {q : ℕ} {D : CH.Digraph} {V S B : Finset ℕ} {y : ℕ}
    (hSV : S ⊆ V) (hy : y ∈ V \ S) (hno : ∀ s ∈ S, ¬ D y s = true)
    (hloop : ¬ D y y = true) (hB : B ⊆ outN D V y)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hb : q * mass B a ≤ mass S a + c - mass V a) :
    ∀ x ∈ V \ S, mass (V \ S) (addWeightAt a y (mass S a)) ≤
      row q (foldGraph D V S B y) (V \ S) (addWeightAt a y (mass S a)) x := by
  intro x hx
  rw [fold_weight_mass hSV hy a]
  by_cases hxy : x = y
  · subst x
    rw [fold_receiver_row hy hno hloop hB a]
    linarith [hr y (mem_sdiff.mp hy).1]
  · exact (hc.trans (hr x (mem_sdiff.mp hx).1)).trans (fold_other_row hSV hy a ha hx hxy)

end LeanCH.BR.WeightedSD
