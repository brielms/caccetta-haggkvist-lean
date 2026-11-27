import checkpoints.shen_extension.PairPowerReservoir

namespace LeanCH.BR.PairPowerBank
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay PairPowerOrder PairPowerReservoir

/-- With one bank label and the targets fixed, a second bank label can be
chosen outside a prescribed forbidden set. The multiplicity is counted on
actual common parents with the specified exact-length approaches. -/
theorem choose_second {D : CH.Digraph} {V F Y : Finset ℕ} {q s j p : ℕ}
    (free : QFree D V q) (live : V.Nonempty) (room : (j+1)+(j+1) ≤ q)
    (pair : ∀ u∈V, ∀ v∈V, ∃ w∈V, D w u=true ∧ D w v=true)
    (deg : ∀ r∈V, s ≤ (outN D V r).card)
    (pv : p∈V) (pf : p∈F) (space : F.card<s) (ys : Y⊆V) (slots : Y.card≤2^j) :
    ∃ h∈V \ F, h≠p ∧
      (2^(2^j-Y.card+1)-1)*(s-F.card) ≤
        (V \ F).card*(inN D (parentsTo D V p Y (j+1)) h).card := by
  classical
  let C := parentsTo D V p Y (j+1)
  have sub : C⊆V := by
    intro w hw
    exact (mem_inN.mp (mem_filter.mp (show w∈(inN D V p).filter
      (fun r => ∀ a∈Y, Walk D V r a (j+1)) from hw)).1).1
  obtain ⟨v,vv⟩ := live
  have inhabited : V.Nonempty := ⟨v,vv⟩
  have floor := (deg v vv).trans (card_le_card (outN_subset : outN D V v⊆V))
  have has : (V \ F).Nonempty := by
    by_contra! empty
    have fv := card_le_card (sdiff_eq_empty_iff_subset.mp empty)
    omega
  obtain ⟨h,hv,best⟩ := (V \ F).exists_max_image (fun z => (inN D C z).card) has
  have many (r) (rr : r∈C) : s-F.card ≤ (outN D (V \ F) r).card := by
    have eq : outN D (V \ F) r = outN D V r \ F := by
      ext a
      simp only [mem_sdiff,mem_outN]
      tauto
    have count := card_sdiff_add_card_inter (outN D V r) F
    have cap := card_le_card (inter_subset_right : outN D V r ∩ F ⊆ F)
    have high := deg r (sub rr)
    rw [eq]
    omega
  have count : (∑ z∈V \ F,(inN D C z).card) = ∑ r∈C,(outN D (V \ F) r).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun h r => D r h=true)
  have upper : ∑ z∈V \ F,(inN D C z).card ≤ ∑ _z∈V \ F,(inN D C h).card := sum_le_sum best
  have lower : ∑ _r∈C,(s-F.card) ≤ ∑ r∈C,(outN D (V \ F) r).card := sum_le_sum many
  rw [count,sum_const,smul_eq_mul] at upper
  rw [sum_const,smul_eq_mul] at lower
  have bound := parentsTo_card free inhabited room pair pv ys slots
  change 2^(2^j-Y.card+1) ≤ C.card+1 at bound
  exact ⟨h,hv,fun same => (mem_sdiff.mp hv).2 (same ▸ pf),
    (Nat.mul_le_mul_right (s-F.card) (show 2^(2^j-Y.card+1)-1 ≤ C.card by omega)).trans
      (lower.trans upper)⟩

#print axioms choose_second
end LeanCH.BR.PairPowerBank
