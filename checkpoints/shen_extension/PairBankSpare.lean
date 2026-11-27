import checkpoints.shen_extension.SharedHeadSuppliers

/-! After deleting a pair of labels, compare the actual rows that miss both
with the actual rows that hit both. -/

namespace LeanCH.BR.PairBankSpare
open Finset BRq2 BRq3 BR45 BypassRepair

/-- Hitting both deleted columns costs a regular row two heads. Missing
both preserves its full degree. A two-ball lower bound at each deleted
label controls the difference between the numbers of these two kinds. -/
theorem pair_ledger {D : CH.Digraph} {V : Finset ℕ} {q s k p h : ℕ}
    (rows : OutEq s D V) (free : QFree D V q) (three : 3 ≤ q) (hs : 1 ≤ s)
    (none : NoHost q (k+1)) (room : s ≤ q*(k+1)) (pv : p ∈ V) (hv : h ∈ V) (ne : p ≠ h) :
    let P := inN D V p
    let H := inN D V h
    let U := V \ {p,h}
    4*s + (P ∩ H).card ≤ (U \ (P ∪ H)).card + V.card + 2*k := by
  classical
  have price (v) (vv : v ∈ V) : (inN D V v).card + 2*s + 1 ≤ V.card+k := by
    have ball := SharedHeadSuppliers.layer_floor none free (by omega) rows hs room vv
    have cap := ReachLedger.parent_cap (i := 2) free three vv
    omega
  have pp := price p pv
  have ph := price h hv
  have sub : ({p,h} : Finset ℕ) ⊆ V := insert_subset pv (singleton_subset_iff.mpr hv)
  have size := card_sdiff_add_card_eq_card sub
  rw [card_pair ne] at size
  have unionSize := card_union_add_card_inter (inN D V p) (inN D V h)
  have cover := card_le_card_sdiff_add_card (s := V \ {p,h}) (t := inN D V p ∪ inN D V h)
  dsimp only
  omega

/-- In the triangle column, the excess of spare rows over the rows losing
two heads grows with the degree. The lower quota used here is exactly
one more than the integer quotient `(s-1)/3`. -/
theorem triangle_spare {D : CH.Digraph} {V : Finset ℕ} {s p h : ℕ}
    (rows : OutEq s D V) (free : QFree D V 3) (hs : 2 ≤ s)
    (lower : ∀ t < s, NoHost 3 t) (room : V.card ≤ 3*s)
    (pv : p ∈ V) (hv : h ∈ V) (ne : p ≠ h) :
    let P := inN D V p
    let H := inN D V h
    let U := V \ {p,h}
    (P ∩ H).card + (s - 2*((s-1)/3)) ≤ (U \ (P ∪ H)).card := by
  have bound := pair_ledger rows free (by decide) (by omega)
    (lower ((s-1)/3+1) (by omega)) (by omega) pv hv ne
  dsimp only at bound ⊢
  omega

#print axioms triangle_spare
end LeanCH.BR.PairBankSpare

