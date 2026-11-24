import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

noncomputable def shellOrigins (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) :=
  V.filter (fun v => (ball D V v k).card ≤ b)

noncomputable def shellFiber (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) (Y : Finset ℕ) :=
  (shellOrigins D V k b).filter (fun v => N2 D V v = Y)

noncomputable def shellDebt (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) (Y : Finset ℕ) :=
  let U := shellFiber D V k b Y
  (∑ v ∈ U, debit b (ball D V v k).card) - U.offDiag.card

/-- The same-shell classes pay with their actual internal ordered holes.
Their receipts can be added to a separate payment by cross-class holes
without counting any physical ordered pair twice. -/
theorem ledger_from_shell_classes {D V q k b F r} (free : QFree D V q) (hq : 2 ≤ q)
    (time : k+k ≤ q) (low : ∀ v ∈ V, b ≤ (ball D V v k).card+1) (order : V.card ≤ 2*b)
    (rooted : ∀ C ∈ F, ∀ v ∈ C, Rooted D V v C) (sub : ∀ C ∈ F, C ⊆ V)
    (degree : OutEq r D V)
    {extra : Finset (ℕ × ℕ)}
    (real : extra ⊆ DotClonePairCompletion.orderedIncomparable D V k)
    (across : ∀ e ∈ extra, N2 D V e.1 ≠ N2 D V e.2)
    (paid :
      (∑ Y ∈ (shellOrigins D V k b).image (N2 D V), (shellDebt D V k b Y : ℚ)) <
        extra.card + (∑ C ∈ F, ∑ v ∈ C, share D V F r (fun v => surplus b (ball D V v k).card) C v)) :
    False := by
  classical
  let U := shellOrigins D V k b
  let P := U.image (N2 D V)
  let fiber := shellFiber D V k b
  let loss := fun v => debit b (ball D V v k).card
  let inner := P.biUnion (fun Y => (fiber Y).offDiag)
  have native : U ⊆ V := filter_subset _ _
  have budget : ∑ v ∈ V, loss v = ∑ Y ∈ P, ∑ v ∈ fiber Y, loss v := by
    have sums := sum_sdiff native (f := loss)
    have zero : ∑ v ∈ V\U, loss v = 0 := by
      apply sum_eq_zero
      intro v hv
      have large : b < (ball D V v k).card := by
        by_contra! fit
        exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, fit⟩)
      simp [loss, debit, not_lt_of_ge large.le, Nat.ne_of_gt large]
    rw [zero, zero_add] at sums
    rw [← sums]
    exact (sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem (N2 D V) hv) loss).symm
  have old : inner ⊆ DotClonePairCompletion.orderedIncomparable D V k := by
    intro e he
    obtain ⟨Y, _, inside⟩ := mem_biUnion.mp he
    have small : fiber Y ⊆ V := (filter_subset _ _).trans native
    apply class_pairs free hq (by omega) degree small (fun a ha b hb => ?_) inside
    exact ((mem_filter.mp ha).2).trans ((mem_filter.mp hb).2).symm
  have separate : (P : Set (Finset ℕ)).PairwiseDisjoint (fun Y => (fiber Y).offDiag) := by
    intro Y _ Z _ ne
    refine disjoint_left.mpr (fun e hy hz => ne ?_)
    have a := (mem_filter.mp (mem_offDiag.mp hy).1).2
    have b := (mem_filter.mp (mem_offDiag.mp hz).1).2
    exact a.symm.trans b
  have sep : Disjoint inner extra := by
    refine disjoint_left.mpr (fun e inInner eExtra => ?_)
    obtain ⟨Y, _, incident⟩ := mem_biUnion.mp inInner
    obtain ⟨ha, hb, _⟩ := mem_offDiag.mp incident
    exact across e eExtra (((mem_filter.mp ha).2).trans ((mem_filter.mp hb).2).symm)
  apply ledger_contradiction free time low order rooted sub degree (union_subset old real)
  change (∑ Y ∈ P, (shellDebt D V k b Y : ℚ)) < _ at paid
  have joined : ((inner ∪ extra).card : ℚ) = (inner.card : ℚ)+extra.card := by
    exact_mod_cast card_union_of_disjoint sep
  have exactCount : (∑ v ∈ V, loss v) ≤ inner.card + (∑ Y ∈ P, shellDebt D V k b Y) := by
    rw [budget, show inner.card=∑ Y ∈ P,(fiber Y).offDiag.card from card_biUnion separate,
      ←sum_add_distrib]
    apply sum_le_sum
    intro Y _
    unfold shellDebt
    change (∑ v ∈ fiber Y, loss v) ≤ (fiber Y).offDiag.card+((∑ v ∈ fiber Y, loss v)-(fiber Y).offDiag.card)
    omega
  have realCount : (∑ v ∈ V, (loss v : ℚ)) ≤ (inner.card : ℚ) +
      (∑ Y ∈ P, (shellDebt D V k b Y : ℚ)) := by exact_mod_cast exactCount
  linarith only [realCount, paid, joined]

/-- Assign every literal second-shell class to one paying cycle, which may
be a terminal reached by a proved routing rule. One strict cycle receipt
then closes the weighted ledger. -/
theorem ledger_from_cycle_receipts {D V q k b r} {F : Finset (Finset ℕ)}
    (free : QFree D V q) (hq : 2 ≤ q)
    (time : k+k ≤ q) (low : ∀ v ∈ V, b ≤ (ball D V v k).card+1) (order : V.card ≤ 2*b)
    (rooted : ∀ C ∈ F, ∀ v ∈ C, Rooted D V v C) (sub : ∀ C ∈ F, C ⊆ V)
    (degree : OutEq r D V)
    (pay : Finset ℕ → Finset ℕ) (holes : Finset ℕ → Finset (ℕ × ℕ))
    (assigned : ∀ Y ∈ (shellOrigins D V k b).image (N2 D V), pay Y ∈ F)
    (real : ∀ C ∈ F, holes C ⊆ DotClonePairCompletion.orderedIncomparable D V k)
    (across : ∀ C ∈ F, ∀ e ∈ holes C, N2 D V e.1 ≠ N2 D V e.2)
    (apart : (F : Set (Finset ℕ)).PairwiseDisjoint holes)
    (paid : ∀ C ∈ F,
      (∑ Y ∈ ((shellOrigins D V k b).image (N2 D V)).filter (fun Y => pay Y = C),
        (shellDebt D V k b Y : ℚ)) ≤
        (holes C).card + (∑ v ∈ C, share D V F r (fun v => surplus b (ball D V v k).card) C v))
    (strict : ∃ C ∈ F,
      (∑ Y ∈ ((shellOrigins D V k b).image (N2 D V)).filter (fun Y => pay Y = C),
        (shellDebt D V k b Y : ℚ)) <
        (holes C).card + (∑ v ∈ C, share D V F r (fun v => surplus b (ball D V v k).card) C v)) :
    False := by
  classical
  let X := F.biUnion holes
  have genuine : X ⊆ DotClonePairCompletion.orderedIncomparable D V k := by
    intro e he
    obtain ⟨C, cf, inside⟩ := mem_biUnion.mp he
    exact real C cf inside
  have different : ∀ e ∈ X, N2 D V e.1 ≠ N2 D V e.2 := by
    intro e he
    obtain ⟨C, cf, inside⟩ := mem_biUnion.mp he
    exact across C cf e inside
  apply ledger_from_shell_classes free hq time low order rooted sub degree genuine different
  obtain ⟨C, cf, strict⟩ := strict
  have summed := sum_lt_sum paid ⟨C, cf, strict⟩
  rw [sum_fiberwise_of_maps_to assigned, sum_add_distrib] at summed
  have count : ((X.card : ℕ) : ℚ) = ∑ C ∈ F, ((holes C).card : ℚ) := by
    exact_mod_cast card_biUnion apart
  rwa [←count] at summed

#print axioms ledger_from_shell_classes
#print axioms ledger_from_cycle_receipts
end LeanCH.BR.PhysicalCycleStock
