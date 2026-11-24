import checkpoints.shen_extension.ErasedQuotaFrontier
import checkpoints.shen_extension.ReachDescentCatalog

/-!
# Every lower quota, on free parameters

The least descendant excludes a smaller host at every quota below its
degree. The rules below consume that one fact on free `q` and `r`, so they
apply to any graph, set and row whose own statements name the same `q` and
`r`. They do not mention an input record. A caller publishes the fact once
in its own spelling of the cutoff and the degree.
-/

namespace LeanCH.BR.RootLowerQuotas
open Finset BRq2 BRq3 BR45 BypassRepair ParentBankPeel ReachDescentCatalog FragmentScoreEquality

/-- Growth floors at every root and radius of a minimum-order source. -/
theorem source_floors {q r} {X : ShenMinimumOrder.Source q r} (_free : QFree X.D X.V q)
    (lower : ∀t,t<r → NoHost q t) (hq : 0<q) (hr : 0<r) : Floors X.D X.V q r :=
  (ReachDescentCatalog.source_floors (X:=X) lower hq hr X.nonempty).1

/-- The radius, pair and bank bounds at the source's own order. -/
theorem source_bounds {q r} {X : ShenMinimumOrder.Source q r} (_free : QFree X.D X.V q)
    (lower : ∀t,t<r → NoHost q t) (hq : 0<q) (hr : 0<r) : Bounds q r X.V.card :=
  (ReachDescentCatalog.source_floors (X:=X) lower hq hr X.nonempty).2

/-- A cheap row's head bank is tested at every positive quota below `r`,
on the same graph, carrier, short row and cheap row. -/
theorem ceiling_of_quotas {D : CH.Digraph} {U : Finset ℕ} {q r x v : ℕ}
    (packet : ShortBankLimit D U q (r-1) x v) (lower : ∀t,t<r → NoHost q t) :
    ParentBankCeiling D U q (r-1) x v :=
  bank_ceiling packet fun d _ dt=>lower d (by omega)

/-- The two-quota form used by rules that fix one lower degree. -/
theorem quota_at {q r t : ℕ} (lower : ∀t,t<r → NoHost q t) (below : t<r) : NoHost q t :=
  lower t below

attribute [aesop safe forward (immediate := [_free,lower,hq,hr]) (rule_sets := [CHGraphFamilies])]
  source_floors source_bounds
attribute [aesop safe forward (immediate := [packet,lower]) (rule_sets := [CHGraphFamilies])]
  ceiling_of_quotas

#print axioms source_floors
#print axioms source_bounds
#print axioms ceiling_of_quotas
end LeanCH.BR.RootLowerQuotas
