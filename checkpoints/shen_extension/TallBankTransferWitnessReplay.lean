import checkpoints.shen_extension.TallBankTransferWitness
import checkpoints.shen_extension.TallBankTransferStrongReplay

namespace LeanCH.BR.TallBankTransfer

attribute [aesop safe forward (immediate := [free,time,uv,size,ha,hb,ne,sa,sb,all,rows,same])
  (rule_sets := [CHGraphFamilies])] common_sink_layer_fits_third
attribute [aesop safe forward (immediate := [free,diag,room,xv,yv,sizeX,sizeY,degree,complete,hx,hb,back])
  (rule_sets := [CHGraphFamilies])] equal_bank_return_shape
attribute [aesop safe forward (immediate := [free,diag,room,reg,av,weak])
  (rule_sets := [CHGraphFamilies])] weak_equal_shell
attribute [aesop safe forward (immediate := [free,diag,room,reg,uv,ha,stop,two,three,weak])
  (rule_sets := [CHGraphFamilies])] weak_sink_entry_ledger

ch_family_split_result weak_equal_shell

end LeanCH.BR.TallBankTransfer

