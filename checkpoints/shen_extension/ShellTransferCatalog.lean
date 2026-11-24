import checkpoints.shen_extension.RootLayerTransit
import checkpoints.shen_extension.CHFamilyDeclarations

namespace LeanCH.BR
attribute [aesop safe forward (immediate := [free,hq,sub,small,internal,xm]) (rule_sets := [CHGraphFamilies])]
  ShellCycleSupply.rooted_on_small_set
attribute [aesop safe forward (immediate := [free,hq,uv]) (rule_sets := [CHGraphFamilies])] ShellCycleSupply.head_exterior
attribute [aesop safe forward (immediate := [free,hq,reg,uv,fit,narrow]) (rule_sets := [CHGraphFamilies])]
  ShellCycleSupply.narrow_supply
ch_family_split_result ShellCycleSupply.equal_rows
end LeanCH.BR
