import checkpoints.shen_extension.MixedDeletionCover
import checkpoints.shen_extension.InheritedProfileWindow

namespace LeanCH.BR.ProjectedQuotaTransfer
open Finset CHRuleCatalog GuardedProfileBudget

def library_of_source_floor {floor} (source : ∀p : Input,Bad p → floor≤p.s) : QuotaLibrary :=
  ⟨range floor,fun p bad mem=>Nat.not_lt_of_ge (source p bad) (mem_range.mp mem)⟩

def completedLibrary := library_of_source_floor (fun _ bad=>replay_completed_floor bad)

theorem inherited_at_completed {p : Input} (bad : Bad p) :
    ¬InheritedProfileWindow.Fits p.n p.s (cutoff p) completedLibrary.ranks :=
  InheritedProfileWindow.excludes bad completedLibrary

theorem direct_at_completed {p : Input} (bad : Bad p) :
    ¬Window p.n p.s (cutoff p) completedLibrary.ranks :=
  raw_window (raw_budget bad) completedLibrary.excluded

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
  inherited_at_completed direct_at_completed
#print axioms inherited_at_completed
#print axioms direct_at_completed
end LeanCH.BR.ProjectedQuotaTransfer
