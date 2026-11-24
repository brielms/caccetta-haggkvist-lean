import checkpoints.shen_extension.RectangleShellFloor

namespace LeanCH.BR.AvoidedHeadQuota
open Finset BRq2 BRq3 BypassRepair CHRuleCatalog ProjectedQuotaTransfer GuardedFamilyRules
open CompromiseQuotaTransfer (recorded)

/-- A bank of order q*t+1 raises the bound to 3*r+2-t. Parameter e
is the extra lower quota needed to fit an actual subset of r+2+e rows.
The gain from each additional unit of quota is q-1 slots. -/
theorem raised_bound {q t r e} (cut : 3≤q) (two : 2≤t) (extra : e≤t) (slots : 3+e≤q*e)
    (mult : r=q*t+1) (boundary : Compose.Boundary.BoundaryRegular q t)
    (small : NoHost q t) (none : NoHost q (t+e)) : OrderBound q r (3*r+2-t) := by
  have qt := Nat.mul_le_mul_right t cut
  refine ⟨by omega,?_⟩
  intro D V free live degree
  by_contra! order
  obtain ⟨E,sub,reg⟩ := exists_outEq degree
  apply boundary_exit (qfree_sub sub free) live reg cut boundary small none
    (by omega) (by omega) mult (by omega) (by omega)
    (m:=r+2+e) (by omega) (by omega) (by rw [Nat.mul_add]; omega) (by omega)

/-- The stronger quota is available as soon as its diagonal fits. Putting
the decision in the table also serves numerical inputs whose cutoff is
given by a quotient rather than a separate equality hypothesis. -/
theorem spendable_prefix {q d m} (known : ∀k,k<d → NoHost q k) (bound : OrderBound q d m) :
    ∀k,k<(if q*d≤m then d+1 else d) → NoHost q k := by
  split
  next fit => exact CompromiseQuotaTransfer.extend_prefix known bound fit
  next => exact known

-- A table value, not a law: `recorded` is the degree-nine compromise theorem (score 18).
def spendingFloor (q : ℕ) := if q*recorded.degree≤recorded.degree+recorded.score then
  recorded.degree+1 else recorded.degree

theorem available {p : Input} (bad : Bad p) :
    ∀k,k<spendingFloor (cutoff p) → NoHost (cutoff p) k :=
  spendable_prefix (d:=recorded.degree) (available_lower_hosts bad) (CompromiseQuotaTransfer.recorded_bound bad)

@[ch_numeric_guard] def LiftWindow (n r q floor : ℕ) : Prop :=
  3≤q ∧ ∃t∈range floor,2≤t ∧ ¬WeightedSD.NativePressureRegion q t ∧
    ∃e∈Icc 1 t,3+e≤q*e ∧ t+e<floor ∧
    Fits n r q q (q*t+1) (3*(q*t+1)+2-t)

instance {n r q floor} : Decidable (LiftWindow n r q floor) := by
  unfold LiftWindow WeightedSD.NativePressureRegion
  infer_instance

theorem lift_excluded {p : Input} {floor} (bad : Bad p)
    (known : ∀k,k<floor → NoHost (cutoff p) k) : ¬LiftWindow p.n p.s (cutoff p) floor := by
  rintro ⟨cut,t,tm,two,region,e,em,slots,room,fits⟩
  exact forbidden bad (raised_bound cut two (mem_Icc.mp em).2 slots rfl
    (WeightedSD.boundary_regular_outside_pressure_region cut two region)
    (known t (mem_range.mp tm)) (known _ room)) fits

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] available
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] lift_excluded
attribute [aesop safe forward (immediate := [cut,two,extra,slots,mult,boundary,small,none])
  (rule_sets := [CHGraphFamilies])] raised_bound
#print axioms raised_bound
#print axioms spendable_prefix
#print axioms available
#print axioms lift_excluded
end LeanCH.BR.AvoidedHeadQuota
