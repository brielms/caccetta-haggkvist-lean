import checkpoints.shen_extension.ShortfallBridge
import LeanCH.BR.BRWeightedPressureFrontier
import LeanCH.BR.BR37Z
import LeanCH.BR.BR37
import LeanCH.BR.BRq5All
import LeanCH.BR.BR96

/-!
# Root boundary regularity closes the lone child one degree up

`Compose.Boundary.BoundaryRegular q d` is the root statement: on `q d + 1` labels with minimum
out-degree `d` and no directed cycle of length at most `q`, every in-degree is `d`.

* `inRegular_of_boundaryRegular`: it gives the carrier form `QBoundaryInRegular q d`.
* `lone_exit_boundaryRegular`: so a lone child at degree `r` and cutoff `q` is impossible whenever
  boundary regularity is known at `(q, r-1)`.
* Instances from the root catalog: degree 6 at every cutoff (`br_q_five`), degree 7 at cutoff 9
  (`br_nine_six`), cutoff 3 at degrees 5 to 8 (`br_four`, `br_five`, `br_six`, `br_seven`).
-/

namespace LeanCH.BR.RootRegularBridge
open Finset BRq2 BRq3 BypassRepair BypassBankReplay LoneRow ShortfallBridge
open LeanCH.BR.Closure.BoundaryHub

/-- Root boundary regularity in carrier form. -/
theorem inRegular_of_boundaryRegular {q d : ℕ} (hq : 1 ≤ q)
    (br : Compose.Boundary.BoundaryRegular q d) : QBoundaryInRegular q d := by
  intro E W free size deg v hv
  obtain ⟨n, hsub⟩ := BRsGen35.exists_range W
  have hloop : CH.Loopless (BRsGen35.resD E W) n := by
    intro x _
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨hx, _, hxx⟩ := BRsGen35.resD_eq.mp he
    exact loopfree free hq hx hxx
  have hout (x : ℕ) (hx : x ∈ W) : outN (BRsGen35.resD E W) W x = outN E W x := by
    ext y
    simp only [mem_outN, BRsGen35.resD_eq]
    tauto
  have hreg := BR37.induced_regular_in br hsub size hloop
    (WeightedSD.qfree_restriction_no_short free n)
    (fun x hx => by
      change d ≤ (outN (BRsGen35.resD E W) W x).card
      rw [hout x hx]
      exact deg x hx)
  have hin : W.filter (fun u => BRsGen35.resD E W u v = true) = BR45.inN E W v := by
    ext u
    simp only [mem_filter, BR45.mem_inN, BRsGen35.resD_eq]
    tauto
  rw [← hin]
  exact hreg v hv

/-- No survivor graph with exactly one row short by one, wherever the root law is known. -/
theorem near_of_boundaryRegular {q d : ℕ} (br : Compose.Boundary.BoundaryRegular q d)
    (none : NoHost q d) (hq : 1 ≤ q) (hd : 2 ≤ d) : NoNearHost q d :=
  near_of_inRegular (inRegular_of_boundaryRegular hq br) none hq hd

variable {q r : ℕ}

/-- **The lone child closes from root boundary regularity one degree down.** -/
@[aesop safe forward (immediate := [br,hq,hr,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem lone_exit_boundaryRegular {X : ShenMinimumOrder.Source q r} {m : Cell}
    (br : Compose.Boundary.BoundaryRegular q (r-1)) (hq : 1 ≤ q) (hr : 3 ≤ r)
    (cell : Marked X m) (lone : LoneBlocked X m) : False :=
  lone_exit_inRegular (inRegular_of_boundaryRegular hq br) hq hr cell lone

/-- Degree six, every cutoff. -/
theorem lone_exit_six {X : ShenMinimumOrder.Source q 6} {m : Cell} (hq : 1 ≤ q)
    (cell : Marked X m) (lone : LoneBlocked X m) : False :=
  lone_exit_boundaryRegular (BRq5.br_q_five q hq) hq (by decide) cell lone

/-- Degree seven at cutoff nine. -/
theorem lone_exit_seven_nine {X : ShenMinimumOrder.Source 9 7} {m : Cell}
    (cell : Marked X m) (lone : LoneBlocked X m) : False :=
  lone_exit_boundaryRegular BRq6.br_nine_six (by decide) (by decide) cell lone

/-- Cutoff three at degree eight. -/
theorem lone_exit_three_eight {X : ShenMinimumOrder.Source 3 8} {m : Cell}
    (cell : Marked X m) (lone : LoneBlocked X m) : False :=
  lone_exit_boundaryRegular BR37.br_seven (by decide) (by decide) cell lone

#print axioms inRegular_of_boundaryRegular
#print axioms near_of_boundaryRegular
#print axioms lone_exit_boundaryRegular
#print axioms lone_exit_six
#print axioms lone_exit_seven_nine
#print axioms lone_exit_three_eight
end LeanCH.BR.RootRegularBridge
