import LeanCH.BR.BRWeightedPositiveParentTransfer

/-! A retained receiver head pays an additional strict-source margin.
The original frozen common-parent sources are unchanged. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem row_addWeightAt {q : ℕ} {D : CH.Digraph} {K : Finset ℕ} {z : ℕ}
    (hz : z ∈ K) (a : ℕ → ℚ) (δ : ℚ) (x : ℕ) :
    row q D K (addWeightAt a z δ) x = row q D K a x +
      (if x = z then δ else 0) + q * (if D x z = true then δ else 0) := by
  rw [row, outW_addWeightAt hz]
  simp only [addWeightAt, row]
  ring

theorem common_parent_bank_strict_of_retained_head {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hret : (outN D V y \ firstHeadBank q D V S y).Nonempty) :
    mass S a + q * (c - mass V a) < q * mass (firstHeadBank q D V S y) a := by
  by_contra hn
  obtain ⟨z, hz⟩ := hret
  have hq1 : 1 ≤ q := by omega
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hyK := common_parent_receiver_retained hq1 hf hy hS
  let E := parentTransferGraph q D V S y
  let b := addWeightAt a y (mass S a)
  let δ := c - mass V a
  have hδ : 0 < δ := sub_pos.mpr hc
  have hA := mass_nonneg (fun s hs => ha s (hSV hs))
  have hb : ∀ x ∈ V \ S, 0 ≤ b x :=
    fun x hx => addWeightAt_nonneg ha hA y x (mem_sdiff.mp hx).1
  have hez : z ∈ outN E (V \ S) y := by
    change z ∈ outN (parentTransferGraph q D V S y) (V \ S) y
    rwa [parentTransfer_receiver_heads hq hf hy hS]
  have hzK := outN_subset hez
  have hyz := (mem_outN.mp hez).2
  have hz_ne_y : z ≠ y := by
    intro he
    subst z
    exact loopfree hf hq1 hy (mem_outN.mp (mem_sdiff.mp hz).1).2
  have hfree : QFree E (V \ S) q := parentTransferGraph_qfree hq hf hy hS
  have hm : mass (V \ S) (addWeightAt b z δ) = c := by
    rw [mass_addWeightAt hzK]
    change mass (V \ S) (addWeightAt a y (mass S a)) + δ = c
    rw [parentTransfer_mass hq1 hf hy hS a]
    dsimp [δ]
    ring
  have hnn : ∀ x ∈ V \ S, 0 ≤ addWeightAt b z δ x :=
    addWeightAt_nonneg hb hδ.le z
  have hfeas : ∀ x ∈ V \ S,
      mass (V \ S) (addWeightAt b z δ) ≤ row q E (V \ S) (addWeightAt b z δ) x := by
    intro x hx
    rw [hm, row_addWeightAt hzK]
    by_cases hxy : x = y
    · subst x
      rw [if_neg (Ne.symm hz_ne_y), if_pos hyz, add_zero]
      change c ≤ row q (parentTransferGraph q D V S y) (V \ S)
        (addWeightAt a y (mass S a)) y + q * δ
      rw [parentTransfer_receiver_row hq hf hy hS a]
      dsimp [δ]
      have hbound : q * mass (firstHeadBank q D V S y) a ≤
          mass S a + q * (c - mass V a) := le_of_not_gt hn
      linarith [hr y hy]
    · have hrow := (hr x (mem_sdiff.mp hx).1).trans
        (parentTransfer_other_row hq1 hf hy hS a ha hx hxy)
      change c ≤ row q E (V \ S) b x at hrow
      have h1 : 0 ≤ if x = z then δ else 0 := by split_ifs <;> linarith
      have h2 : 0 ≤ (q : ℚ) * (if E x z = true then δ else 0) :=
        mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> linarith)
      linarith
  have hsup : SmallRow q E ((V \ S).filter (fun x => 0 < addWeightAt b z δ x)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (parentTransfer_card_lt hSV hSne))
      (hfree.mono_set (filter_subset _ _))
  have hzpos : 0 < addWeightAt b z δ z := by
    simp only [addWeightAt, ite_true]
    linarith [hb z hzK]
  have he := positive_coordinate_tight_of_support_smallRow hq
    (addWeightAt b z δ) hnn hsup hfeas hzK hzpos
  rw [hm, row_addWeightAt hzK, if_pos rfl] at he
  have hrow := (hr z (mem_sdiff.mp hzK).1).trans
    (parentTransfer_other_row hq1 hf hy hS a ha hzK hz_ne_y)
  change c ≤ row q E (V \ S) b z at hrow
  have h2 : 0 ≤ (q : ℚ) * (if E z z = true then δ else 0) :=
    mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> linarith)
  linarith

end LeanCH.BR.WeightedSD
