import checkpoints.shen_extension.FifthStripAllDense

/-!
# Fifth strip: one decidable cell per shift `a`, and what it closes

`Cell a` bundles the finite checks used at shift `a` (degree `s = a + 7`, cutoff `q = 2a + 7`):
the ledger checks, the local advance at order `qs - 1`, and, where a top argument is
available (even `a` through Seymour, or `a ≥ 37` through the dense table), the local
advance at order `qs` and the dense-table parameters. `cell_below_top` and `cell_top`
turn a cell into the order statements.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAll
open Finset BRq2 BRq3 BR45

def topCase (a : ℕ) : Bool := decide (6 ≤ a ∧ (a % 2 = 0 ∨ 37 ≤ a))

def Cell (a : ℕ) : Prop :=
  FifthStripLedger.Checks a ∧ Top a ((2*a+7)*(a+7)-1) ∧
    (topCase a = true → Top a ((2*a+7)*(a+7)) ∧
      (a % 2 = 0 ∨ ∃ g ∈ range 6, ∃ e ∈ range 40, DenseOK a g e))

instance (a : ℕ) : Decidable (Cell a) := by unfold Cell; infer_instance

/-- A cell forces every nonempty free host to have at least `qs` labels. -/
theorem cell_order {a : ℕ} (ha : 2 ≤ a) (cell : Cell a) :
    MixedRadiusCompletion.Order (2*a+7) (a+7) ((2*a+7)*(a+7)) := by
  intro D V free deg ne
  have L := ledger_floors (by omega) cell.1
  have h := (order_top1 ha) D V free deg ne
  by_contra! small
  exact below_top_false ha L cell.2.1 free deg ne (by omega)

/-- A top cell excludes order `qs`. -/
theorem cell_top {a : ℕ} (ha : 2 ≤ a) (cell : Cell a) (top : topCase a = true)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (deg : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7)) : False := by
  have L := ledger_floors (by omega) cell.1
  obtain ⟨tc, par⟩ := cell.2.2 top
  rcases par with ev | ⟨g, -, e, -, ok⟩
  · exact top_false_even ha (m := a/2) (by omega) L tc free deg ne size
  · exact top_false_dense ha L tc (cell_order ha cell) ok free deg ne size

#print axioms cell_order
#print axioms cell_top
end LeanCH.BR.FifthStripAll
