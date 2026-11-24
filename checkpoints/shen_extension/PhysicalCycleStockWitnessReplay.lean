import checkpoints.shen_extension.PhysicalCycleStockDag
import checkpoints.shen_extension.PhysicalCycleStockFullLayers
import checkpoints.shen_extension.PhysicalCycleStockOverlap
import checkpoints.shen_extension.PhysicalCycleStockClassLedger
import checkpoints.shen_extension.PhysicalCycleStockMiddle
import checkpoints.shen_extension.PhysicalCycleStockPrimary
import checkpoints.shen_extension.PhysicalCycleStockChain
import checkpoints.shen_extension.PhysicalCycleStockAnchors

namespace LeanCH.BR.PhysicalCycleStock

attribute [aesop safe forward (immediate := [free,hq,reg,hu,second,escapes,firstDAG,secondDAG,wide])
  (rule_sets := [CHGraphFamilies])] dag_omission
attribute [aesop safe forward (immediate := [free,hq,hr,room,reg,hu,second,third,firstRooted,secondRooted])
  (rule_sets := [CHGraphFamilies])] full_cyclic_layers
attribute [aesop safe forward (immediate := [free,hq,hu,hv,dist,first,toBank,covered,path])
  (rule_sets := [CHGraphFamilies])] first_side_single_contact
attribute [aesop safe forward (immediate := [free,hq,hu,first,wide])
  (rule_sets := [CHGraphFamilies])] first_side_fast_of_width
attribute [aesop safe forward (immediate := [free,hq,time,low,order,rooted,sub,degree,real,across,paid])
  (rule_sets := [CHGraphFamilies])] ledger_from_shell_classes
attribute [aesop safe forward (immediate := [free,hq,time,low,order,rooted,sub,degree,assigned,real,across,apart,paid,strict])
  (rule_sets := [CHGraphFamilies])] ledger_from_cycle_receipts
attribute [aesop safe forward (immediate := [free,hq,reg,hu,fit,hr,room,second,third,capacity])
  (rule_sets := [CHGraphFamilies])] narrow_middle
attribute [aesop safe forward (immediate := [free,hq,reg,hu,fit,gap,chosen,vc,first,size,second,sparse,rooted,width,narrow])
  (rule_sets := [CHGraphFamilies])] primary_two_turns
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,rootA,rootB,ab,bc,bsize,csize])
  (rule_sets := [CHGraphFamilies])] exclusive_step
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,order,s0,s1,s2,rootA,rootB])
  (rule_sets := [CHGraphFamilies])] exclusive_terminal
attribute [aesop safe forward (immediate := [free,hq,hx,reg,full,positive,two,three])
  (rule_sets := [CHGraphFamilies])] rank_four_full_third
attribute [aesop safe forward (immediate := [free,hq,hu,degree,loss,nearby,firstBill,scores])
  (rule_sets := [CHGraphFamilies])] fifth_prefix_budget

ch_family_split_result exclusive_step

end LeanCH.BR.PhysicalCycleStock

