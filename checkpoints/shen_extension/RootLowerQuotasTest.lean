import checkpoints.shen_extension.RootLowerQuotas
import checkpoints.shen_extension.CoverageContradictions

/-! Regression for `RootLowerQuotas`, in the capstone's own spelling: a local
abbreviation `q`, the degree `s`, and the single published lower-quota fact. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
namespace LeanCH.BR.RootLowerQuotasTest
open Lean Elab Tactic Meta CHRuleCatalog BypassDegreeDescent FragmentScoreEquality

elab "expect_fact " c:ident n:num : tactic => withMainContext do
  let name ← resolveGlobalConstNoOverload c
  let mut k : Nat := 0
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if (← instantiateMVars d.type).consumeMData.isAppOf name then k := k+1
  logInfo m!"PROBE {name} count={k}"
  unless k==n.getNat do throwError "expected {n.getNat} facts headed {name}, found {k}"

theorem capstone_spelling {n s : ℕ} {D E : CH.Digraph} {U : Finset ℕ} {x v : ℕ}
    (inputBad : Bad ⟨n,s,D⟩) (hMinimalChild : MinimalChild ⟨n,s,D⟩) (hs : 0<s) :
    let q := CH.ceilDiv n s
    0<q → ∀ source : ShenMinimumOrder.Source q s, BRq2.QFree source.D source.V q →
      ShortBankLimit E U q (s-1) x v → True := by
  intro q hq source free packet
  replay_ch_typed_families
  expect_fact ParentBankCeiling 0
  expect_fact ParentBankPeel.Floors 0
  -- the one line the capstone adds
  have hAllLowerQuotas : ∀t,t<s → BypassRepair.NoHost q t :=
    ReachDescentCatalog.lower_quotas hMinimalChild hq
  replay_ch_typed_families
  expect_fact ParentBankCeiling 1
  expect_fact ParentBankPeel.Floors 1
  expect_fact ReachDescentCatalog.Bounds 2   -- at the input's order and at the source's own
  replay_ch_typed_families                    -- unchanged repeat
  expect_fact ParentBankCeiling 1
  expect_fact ParentBankPeel.Floors 1
  trivial

#print axioms capstone_spelling
end LeanCH.BR.RootLowerQuotasTest
