import checkpoints.shen_extension.SupplierRow
import checkpoints.shen_extension.SupplierFat54

/-!
# Order 54 at degree nine, cutoff six, unconditionally

No `6`-free digraph with every out-degree at least `9` has `54` labels.

`SupplierRow.no54_of_s2` (the closing count `Close54.no54_of_laws` with S5 and L9 from the row
laws) and `SupplierFat54.s2` (S2, with Lemma 5).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close54Final
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar CHRuleCatalog

variable {D : CH.Digraph} {V : Finset ℕ}

/-- **Order 54, out-regular.** -/
theorem no54_regular (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 54) : False :=
  SupplierRow.no54_of_s2 free reg n (SupplierFat54.s2 free reg)

/-- **Order 54.** No `6`-free digraph of minimum out-degree `9` has `54` labels. -/
theorem no_54 (free : QFree D V 6) (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 54) :
    False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no54_regular freeE regE n

/-- No counterexample at degree `9`, cutoff `6` has `54` labels. -/
theorem excluded_54 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 6) :
    p.n ≠ 54 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_54 free deg (by rw [card_range, hn])

#print axioms no54_regular
#print axioms no_54
#print axioms excluded_54
end LeanCH.BR.Close54Final
