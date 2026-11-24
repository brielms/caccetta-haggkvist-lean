#!/usr/bin/env bash
# Run from the repository root after check_capstone.sh --build-only.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
src=checkpoints/shen_extension
for module in PackingForwardReplay FamilyWorklistReplay HeadSlotReplay MarkedRepairReplayTest \
  RankedContractionReplayTest WakeAfterPremiseTest RootLowerQuotasTest ReceiverMarkedRootTest DistinctReceiverReplayTest RecursivePrefixReplayTest; do
  printf '\nChecking %s\n' "$module"
  lake env lean "$src/$module.lean"
done
for check in --list --checks --audit-guards --shen-window; do
  printf '\nRunning root catalog %s\n' "$check"
  lake env lean --run "$src/RunCHRuleCatalog.lean" "$check"
done
