#!/usr/bin/env bash
# From the repository root, with the capstone dependencies already built.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
src=checkpoints/shen_extension
out=.lake/ch-root-replay
mkdir -p "$out" ".lake/build/lib/lean/$src"
for module in CommonParentEndpointPath CommonParentEndpointReplay EndpointPrivateRows; do
  lake env lean -o ".lake/build/lib/lean/$src/$module.olean" "$src/$module.lean" >"$out/$module.log" 2>&1
done
pair_dir=checkpoints/pair_tilt_20261119
mkdir -p ".lake/build/lib/lean/$pair_dir"
for module in PairTilt DeadExitInterval TwoExitBlockers; do
  lake env lean -o ".lake/build/lib/lean/$pair_dir/$module.olean" "$pair_dir/$module.lean"
done
for module in PortParentInvariant LabelledLeakageCapacity LabelledLeakageControl SoleExitWeightGap TwoExitOverlapCap TwoHeadRepairLanes TwoHeadRepairReplay TwoHeadRepairReroot OneParentReroot RerootTerminalRows TwoHeadForcedMiss ParentReturnDeposit TwoParentWithdrawalDual TwoParentReturnPivot TwoParentOpposedBanks TwoParentOldWeight TwoParentReturnCapacity SparseParentDual NativeReturnAccounts TwoParentReverseCharge ReturnSponsorMass MissedFreshCut LateTargetReach ReturnTargetReach ReturnTargetCycles CrossValueOmissions ReturnCycleOmissions ReturnSuffixCover OmittedCycleProgress RestorationAtGate SharedExitReturn MenuEscapeGrowth LastArcGatePayment LastArcPriceTransport LastArcCompetitor LastArcDistanceConflict LastArcSeparatorSink LastArcMergePayment LastArcReturnMenu LastArcHeadDeposit LastArcMenuPayment CycleSpread EndpointBills ThirdPrice DepositTrace AttachmentLaws BoundaryReceiverWitness ReceiverMixture ReceiverRetry ReceiverRetryMerge ReceiverTwoLoss ReceiverBank CorridorOriginalBills ReceiverBankPrice ReceiverSharedBank IndependentReturnGeometry ReturnIncidenceAntichain CHRootExclusions CHRuleCatalog CHExitSuppliers CHContextCatalog; do
  lake env lean -o ".lake/build/lib/lean/$src/$module.olean" "$src/$module.lean" >"$out/$module.log" 2>&1
done
lake env lean -o ".lake/build/lib/lean/$pair_dir/SwappedParentRoom.olean" "$pair_dir/SwappedParentRoom.lean"
for module in EvenCutoffDescent OneLossCutoffDescent LastArcParameterControls CutoffCapstoneEntry TwoHeadAncestorReplay; do
  lake env lean -o ".lake/build/lib/lean/checkpoints/shen_extension/$module.olean" "checkpoints/shen_extension/$module.lean"
done
lake env lean --run "$src/RunCHRuleCatalog.lean" --list >"$out/rules.log"
lake env lean --run "$src/RunCHRuleCatalog.lean" --checks >"$out/root.log"
lake env lean --run "$src/RunCHRuleCatalog.lean" --audit-guards >"$out/guards.log"
lake env lean --run "$src/RunCHRuleCatalog.lean" --shen-window >"$out/shen.log"
export CH_CATALOG_TRACE_FILE="$out/events.log"
: >"$CH_CATALOG_TRACE_FILE"
status=0
lake env lean "$src/Capstone.lean" >"$out/capstone.log" 2>&1 || status=$?
tail -1 "$out/root.log"
rg 'CH-CATALOG SUMMARY|CH-EXIT SUMMARY|CH-EXIT closed|: (error|warning)(\([^)]*\))?:|^case |^⊢' "$out/capstone.log" || true
# Lean emits both "error:" and tagged diagnostics such as "error(lean.unknownIdentifier):".
# A partial CH proof is expected to report unsolved goals. Other errors invalidate the replay.
if rg ':[0-9]+:[0-9]+: error(\([^)]*\))?:' "$out/capstone.log" | rg -v ' error: unsolved goals\r?$'; then
  exit 2
fi
echo "Lean exit $status. Full proof contexts and replay evidence are in $out."
exit "$status"
