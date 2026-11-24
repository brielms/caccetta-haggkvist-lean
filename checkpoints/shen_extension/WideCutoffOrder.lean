import checkpoints.shen_extension.RootLowerQuotas
import checkpoints.shen_extension.BankAverage

/-!
# Cutoff at least the degree: one label above the pair band

A minimum-order source of degree `r` with every lower quota excluded has at
least `q (r-1) + 2` labels. When `r ≤ q` it has at least `q (r-1) + 3`:
on `q (r-1) + 2` labels every two labels would need a common parent, and the
rows hold too few pairs of heads (`BankAverage.wide_cutoff_order`).
-/

namespace LeanCH.BR.WideCutoffOrder
open Finset BRq2 BRq3 BypassRepair

/-- The order bound on the source, guarded by the two numerical conditions. -/
theorem source_order {q r} {X : ShenMinimumOrder.Source q r} (_free : QFree X.D X.V q)
    (lower : ∀t,t<r → NoHost q t) : 2≤r → r≤q → q*(r-1)+3≤X.V.card :=
  fun two wide => BankAverage.wide_cutoff_order X.free X.degree X.nonempty two wide
    (lower (r-1) (by omega))

attribute [aesop safe forward (immediate := [_free,lower]) (rule_sets := [CHGraphFamilies])]
  source_order

#print axioms source_order
end LeanCH.BR.WideCutoffOrder
