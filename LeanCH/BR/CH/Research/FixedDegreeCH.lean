-- leanevolve-block: claim:research-fixed-degree-ch

import LeanCH.BR.CH.Conjecture

namespace CH.Research

/-- The CH statement with the outdegree fixed to `r`. -/
def FixedDegreeCH (r : Nat) : Prop :=
  ∀ (n : Nat) (G : CH.Digraph),
    0 < n →
    0 < r →
    CH.Loopless G n →
    CH.MinOutdegreeAtLeast G n r →
    CH.HasDirectedCycleAtMost G n (CH.ceilDiv n r)

end CH.Research
