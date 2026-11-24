import checkpoints.shen_extension.PhysicalCycleStock
import checkpoints.shen_extension.PhysicalCycleStockShells
import checkpoints.shen_extension.PhysicalCycleStockOrigins
import checkpoints.shen_extension.CHFamilyDeclarations

namespace LeanCH.BR.PhysicalCycleStock

attribute [aesop safe forward (immediate := [free,hq,reg,root,room,late,ceiling,capacity,low])
  (rule_sets := [CHGraphFamilies])] low_third_second
attribute [aesop safe forward (immediate := [free,hq,reg,hu,fit,hr,second,third])
  (rule_sets := [CHGraphFamilies])] narrow_cycle
attribute [aesop safe forward (immediate := [free,hq,reg,hu,near,room,third,loss,fit4,fit5,cap2,cap3])
  (rule_sets := [CHGraphFamilies])] anchored_fourth
attribute [aesop safe forward
  (immediate := [free,hq,reg,hu,hv,distinct,extras,awayA,awayB,secondU,secondV,thirdU,thirdV])
  (rule_sets := [CHGraphFamilies])] second_side_pairs
attribute [aesop safe forward (immediate := [free,time,one,hv,dist,first,toBank,near,path])
  (rule_sets := [CHGraphFamilies])] first_side_contact
attribute [aesop safe forward (immediate := [free,time,hq,hv,dist,first,toBank,fast])
  (rule_sets := [CHGraphFamilies])] fast_first_side
attribute [aesop safe forward (immediate := [free,hq,rootC,rootK,regular,complete,sparse,width,limit,vc,vk])
  (rule_sets := [CHGraphFamilies])] complete_exclusive
attribute [aesop safe forward (immediate := [free,cut,rooted,degree,width])
  (rule_sets := [CHGraphFamilies])] turns_bound
attribute [aesop safe forward (immediate := [free,hq,time,reg,sub,same])
  (rule_sets := [CHGraphFamilies])] class_pairs
attribute [aesop safe forward (immediate := [free,time,low,order,rooted,sub,degree,real,funded])
  (rule_sets := [CHGraphFamilies])] ledger_contradiction

end LeanCH.BR.PhysicalCycleStock
