import checkpoints.shen_extension.QuotaBankPromotion
import checkpoints.shen_extension.BankAverage

/-!
# One order above the quota window, when the cutoff is at least the degree

`BankAverage.wide_cutoff_order`: a graph with no cycle of length at most `q`
and minimum outdegree `d`, where `2 ≤ d ≤ q` and degree `d - 1` has no host at
cutoff `q`, has at least `q (d-1) + 3` vertices. On `q (d-1) + 2` vertices
every two would need a common parent, and the rows hold too few pairs of heads.

Here the bound is put in the form the order tables consume. For every degree
`d` whose lower quota is known, it is an `OrderBound`, so it transfers to
every input of larger degree by deleting vertices. The window is stated in
`n`, `r`, the cutoff and the number of known lower quotas; no degree is named.
-/

namespace LeanCH.BR.WideQuotaWindow
open Finset BRq2 BRq3 CHRuleCatalog BypassRepair GuardedFamilyRules ProjectedQuotaTransfer

/-- The order bound at degree `d`, from the host exclusion one degree down. -/
theorem order_bound {q d : ℕ} (two : 2 ≤ d) (wide : d ≤ q) (lower : NoHost q (d-1)) :
    OrderBound q d (q*(d-1)+2) :=
  ⟨by omega, fun _ _ free live degree => by
    have := BankAverage.wide_cutoff_order free degree live two wide lower
    omega⟩

/-- Some degree `d` with `2 ≤ d ≤ min q r`, whose lower quota `d - 1` is among
the `quotaLimit` known ones, excludes the order `n` after spending `r - d`. -/
@[ch_numeric_guard] def Window (n r q quotaLimit : ℕ) : Prop :=
  ∃ d ∈ Icc 2 (min q r), d ≤ quotaLimit ∧ Fits n r q q d (q*(d-1)+2)

instance {n r q quotaLimit} : Decidable (Window n r q quotaLimit) := by
  unfold Window
  infer_instance

theorem excluded {p : Input} {quotaLimit} (bad : Bad p)
    (known : ∀k,k<quotaLimit → NoHost (cutoff p) k) : ¬Window p.n p.s (cutoff p) quotaLimit := by
  rintro ⟨d,dm,room,fits⟩
  obtain ⟨two,cap⟩ := mem_Icc.mp dm
  exact forbidden bad
    (order_bound two (cap.trans (min_le_left _ _)) (known (d-1) (by omega))) fits

theorem from_prefix {p : Input} (bad : Bad p) : ¬Window p.n p.s (cutoff p) projectionFloor :=
  excluded bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] from_prefix

#print axioms order_bound
#print axioms excluded
#print axioms from_prefix
end LeanCH.BR.WideQuotaWindow
