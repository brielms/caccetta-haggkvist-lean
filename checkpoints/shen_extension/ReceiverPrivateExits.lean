import checkpoints.shen_extension.ReceiverAlignedReplay
import checkpoints.shen_extension.ReceiverNeutralQuota

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45

/-- A reconstructed row cannot miss even one of these specific labels. -/
@[aesop safe forward (immediate := [row,member,miss]) (rule_sets := [CHGraphFamilies])]
theorem impossible_remote {D H q t g b}
    (row : remote D H q t g=outN D H g) (member : b∈remote D H q t g)
    (miss : D g b≠true) : False := miss (mem_outN.mp (row ▸ member)).2

/-- Instantiate at an actual marked return, retaining the private parent. -/
@[aesop safe forward (immediate := [rows,zm,bm,arc,miss]) (rule_sets := [CHGraphFamilies])]
theorem labelled_parent {D H V Y q t g z b}
    (rows : ∀z∈Y,∀b∈H,D z b=true → D g b≠true →
      ∃a∈tight D H t g,Walk D H b a (q-2) ∧ Y\outN D V a={z})
    (zm : z∈Y) (bm : b∈H) (arc : D z b=true) (miss : D g b≠true) :
    ∃a∈tight D H t g,Walk D H b a (q-2) ∧ Y\outN D V a={z} :=
  rows z zm b bm arc miss

ch_family_split_result labelled_parent
#print axioms impossible_remote
#print axioms labelled_parent
end LeanCH.BR.BoundaryTightParentReach
