import checkpoints.shen_extension.LoneRow
import checkpoints.shen_extension.SharedParentFirstHops
import checkpoints.shen_extension.BackwardBallBank

namespace LeanCH.BR.LoneRowCatalog
open Finset BRq2 BRq3 BypassRepair BypassBankReplay BypassTwoStepRow JointShortcutReplay LoneRow

attribute [aesop safe forward (immediate := [none,cell,lone]) (rule_sets := [CHGraphFamilies])] on_cell
attribute [aesop safe forward (immediate := [hq,none,cell,lone]) (rule_sets := [CHGraphFamilies])] marked_bypass
attribute [aesop safe forward (immediate := [L,kc,far]) (rule_sets := [CHGraphFamilies])] far_exit
attribute [aesop safe forward (immediate := [near,cell,lone]) (rule_sets := [CHGraphFamilies])] near_exit
attribute [aesop safe forward (immediate := [L,kc]) (rule_sets := [CHGraphFamilies])] column
ch_family_split_result column
attribute [aesop safe forward (immediate := [hq,none,cell,band,kc]) (rule_sets := [CHGraphFamilies])] band_column_parent
ch_family_split_result band_column_parent

/-- Reuse the surviving column already marked by the repair. -/
@[aesop safe forward (immediate := [hq,cell]) (rule_sets := [CHGraphFamilies])]
theorem target_column {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (hq : 2 ≤ q) (cell : Marked X m) : m.target ∈ cols X.D (X.V \ m.bank) m.x := by
  refine mem_cols.mpr ⟨cell.zu, ?_, cell.fresh⟩
  rintro eq
  exact digonfree X.free hq (cell.sub cell.erased) (mem_sdiff.mp cell.xu).1
    (eq ▸ cell.pz) cell.xp

@[aesop safe forward (immediate := [hq,cell,mark,bill,order]) (rule_sets := [CHGraphFamilies])]
theorem order_if_bill {q r n} {X : ShenMinimumOrder.Source q r} {m : Cell} {y h}
    (hq : 2 ≤ q) (cell : Marked X m) (mark : LostAt X.D (X.V \ m.bank) m.bank (r-1) m.x y h)
    (bill : 2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0))
    (order : X.V.card ≤ n) : q*(r-1)+3 ≤ n :=
  descendant_slots_floor hq cell mark.erased bill order

/-- The complement of the bill forces both debts at the original labels. -/
@[aesop safe forward (immediate := [hq,none,cell,lone,mark,unpaid]) (rule_sets := [CHGraphFamilies])]
theorem swapped_column {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} {y h}
    (hq : 2 ≤ q) (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m)
    (mark : LostAt X.D (X.V \ m.bank) m.bank (r-1) m.x y h)
    (unpaid : ¬ 2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0)) :
    SwapReturn X.D X.V m.bank q (r-1) m.x h ∧
      ∃ k ∈ cols X.D (X.V \ m.bank) m.x, X.D h k = true ∧
        ∃ v l, Blocks X.D X.V (X.V \ m.bank) q (r-1) m.x v k l ∧ v ≠ y ∧ X.D v h ≠ true ∧
          (X.D m.x h = true → l+2=q) :=
  (lost_head_deep hq none cell lone mark).resolve_left (fun pair => unpaid pair.1)

ch_family_split_result swapped_column

#print axioms target_column
#print axioms order_if_bill
#print axioms swapped_column
end LeanCH.BR.LoneRowCatalog
