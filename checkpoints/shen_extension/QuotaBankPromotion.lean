import checkpoints.shen_extension.QuotaProjectionReplay
import checkpoints.shen_extension.ParentBankPeel

namespace LeanCH.BR.ProjectedQuotaTransfer
open Finset BRq2 BRq3 BR45 CHRuleCatalog BypassRepair ParentBankPeel

/-- A graph obtained at a lower quota is enumerated on its own labels
before invoking the certified numerical floor. -/
theorem lower_hosts {p : Input} {floor} (bad : Bad p) (floorLaw : ∀c : Input,Bad c → floor≤c.s) :
    ∀t,t<floor → NoHost (cutoff p) t := by
  intro t low
  exact GuardedProfileBudget.quotas_from_exclusions (K:=range floor) bad
    (fun c bc atRank=>Nat.not_lt_of_ge (floorLaw c bc) (mem_range.mp atRank)) t (mem_range.mpr low)

/-- The peeled parent-bank cap competes with demand at any affordable
intermediate degree and bank size. Each integer in the test comes from
a measured quota, the two-step deletion, or the earlier peeling theorem. -/
@[ch_numeric_guard] def PeelWindow (n r q floor : ℕ) : Prop :=
  2≤q ∧ ∃d∈Icc 2 (min r floor),
    let m := q*(d-1)+2
    n+d≤m+r ∧ ∃s∈Icc 1 d,
      (m-(floorTable q d (q-2)+1)-s)*(d*d/4)+peelCap q d s<s*(m-s)

instance {n r q floor} : Decidable (PeelWindow n r q floor) := by unfold PeelWindow; infer_instance

theorem peel_after_prefix {p : Input} {floor} (bad : Bad p)
    (lower : ∀t,t<floor → NoHost (cutoff p) t) : ¬PeelWindow p.n p.s (cutoff p) floor := by
  rintro ⟨hq,d,dm,fit,s,sm,bill⟩
  obtain ⟨two,lim⟩ := mem_Icc.mp dm
  have hs := (mem_Icc.mp sm).2
  let m := cutoff p*(d-1)+2
  have excluded : Excluded (cutoff p) d m := by
    intro D V size free rank
    exact bank_regime free rank size (fun t ht=>lower t (lt_of_lt_of_le ht (lim.trans (min_le_right ..))))
      hq two rfl hs bill
  have bound : GuardedFamilyRules.OrderBound (cutoff p) d m := by
    refine ⟨by dsimp [m]; omega,?_⟩
    intro D V free live degree
    by_contra! small
    exact pad_regime excluded free degree rfl ⟨card_pos.mpr live,small⟩
  exact GuardedFamilyRules.forbidden bad bound ⟨le_rfl,lim.trans (min_le_left ..),fit⟩

private abbrev quotaOf {d : ℕ} (_ : ClosedQuota d) := d
-- A table value, not a law: the quota closed so far is degree 8, by the finite order table
-- behind `from_recorded_projection`. Every window that takes `floor` is symbolic in it.
abbrev projectionFloor := quotaOf from_recorded_projection + 1

/-- Keep the previously completed prefix as the single input to the lower
host supplier; the entire peel test is free in its degree and bank size. -/
theorem available_lower_hosts {p : Input} (bad : Bad p) : ∀t,t<projectionFloor → NoHost (cutoff p) t :=
  lower_hosts bad (fun _ b=>replay_completed_floor b)

theorem promoted_peel {p : Input} (bad : Bad p) : ¬PeelWindow p.n p.s (cutoff p) projectionFloor :=
  peel_after_prefix bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] available_lower_hosts promoted_peel
attribute [aesop safe forward (immediate := [bad,lower]) (rule_sets := [CHGraphFamilies])] peel_after_prefix
#print axioms lower_hosts
#print axioms peel_after_prefix
#print axioms promoted_peel
end LeanCH.BR.ProjectedQuotaTransfer
