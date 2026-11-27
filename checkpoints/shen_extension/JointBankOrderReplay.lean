import checkpoints.shen_extension.JointBankParentChoice
import checkpoints.shen_extension.JointBankBinaryReturn

namespace LeanCH.BR.BypassBankReplay
open Finset BRq3 BR45 BypassRepair JointShortcutReplay

/-- The parent alternatives for the same marked bank record its native order. -/
structure SelectedParentOrder {q s : ℕ} (X : ShenMinimumOrder.Source q s) (m : Cell) : Prop where
  shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent ↔ X.V.card = q*(s-1)+2
  missed : MissedParent X.D (X.V \ m.bank) (s-1) m.parent ↔ q*(s-1)+3 ≤ X.V.card
  exponential : SharedParent X.D (X.V \ m.bank) (s-1) m.parent →
    (∀ p ∈ X.V, 2^(q-1) < (inN X.D X.V p).card) ∧ 2^(q-1) < s

/-- Choose a joint-short bank whose parent alternatives carry checked bounds. -/
theorem exists_ordered_joint_mark {q s} (X : ShenMinimumOrder.Source q s)
    (reg : OutEq s X.D X.V) (hq : 3 ≤ q) (hs : 4 ≤ s)
    (room : X.V.card ≤ q*s) (none : NoHost q (s-1)) :
    ∃ m, Marked X m ∧ JointShort X m ∧ SelectedParentOrder X m := by
  obtain ⟨m, marked, joint, shared, missed⟩ := exists_classified_joint_mark X reg hq hs room none
  exact ⟨m, marked, joint, shared, missed, fun h =>
    exponential_at_two X reg (by omega) (by omega) (shared.mp h) none⟩

@[aesop safe forward (immediate := [certificate,common]) (rule_sets := [CHGraphFamilies])]
theorem selected_shared_degree {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (certificate : SelectedParentOrder X m) (common : SharedParent X.D (X.V \ m.bank) (s-1) m.parent) :
    2^(q-1) < s := (certificate.exponential common).2

@[aesop safe forward (immediate := [certificate,miss,order]) (rule_sets := [CHGraphFamilies])]
theorem selected_missed_input_order {q s n} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (certificate : SelectedParentOrder X m) (miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (order : X.V.card ≤ n) : q*(s-1)+3 ≤ n := (certificate.missed.mp miss).trans order

#print axioms exists_ordered_joint_mark
#print axioms selected_shared_degree
#print axioms selected_missed_input_order
end LeanCH.BR.BypassBankReplay
