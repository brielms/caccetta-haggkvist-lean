import checkpoints.shen_extension.TallBankTransferReplay
import checkpoints.shen_extension.TallBankTransferStrong

namespace LeanCH.BR.TallBankTransfer

attribute [aesop safe forward
  (immediate := [free,reg,degree,diag,distance,positive,order,floor,profile])
  (rule_sets := [CHGraphFamilies])] weak_sink_of_balanced_profile

ch_family_split_result weak_sink_of_balanced_profile

#print axioms weak_sink_of_balanced_profile
end LeanCH.BR.TallBankTransfer
