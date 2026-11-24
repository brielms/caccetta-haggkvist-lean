import checkpoints.shen_extension.BoundaryHub
import checkpoints.shen_extension.AnchoredDebt
import checkpoints.shen_extension.PrivateHeadClone

/-!
# The shortfall parameter: joining the bank children to the unit-state layer

Two layers of the catalog study the same object under different names.

* The degree-descent layer splits the survivors of a marked bank into `LoneBlocked` (one short row,
  short by one) and `JointShort` (a second short row).
* The earlier layer (`RecursiveDeficitLevels`, `RecursivePrivateCompletion`, `UnitStateBoundary`,
  `TopOvershootProfiles`, `BoundaryHub`) measures any graph by `total s D U`, the sum of the row
  shortfalls at target `s`, and calls `total = 1` a unit graph.

Here the survivor set of a bank is read in that parameter:

* `total_pos`: every survivor set that is not a host has positive shortfall.
* `total_lone`, `lone_unit`: the lone child is exactly shortfall one at target `r-1` on `q(r-1)`
  labels. `joint_total`: a second short row is shortfall at least two.
* `near_of_noPrivate`, `lone_exit_noPrivate`, `lone_exit_inRegular`: the supplied hypotheses of the
  earlier layer close the lone child: no private parent at the boundary order `q(r-1)+1`, or
  in-regularity there.
* `lone_second_bank`: the unit-graph deletion law one degree lower, on the labels of the lone cell.
-/

namespace LeanCH.BR.ShortfallBridge
open Finset BRq2 BRq3 BypassRepair BypassBankReplay BypassTwoStepRow JointShortcutReplay LoneRow
open LeanCH.BR.Closure.DeficitLevels LeanCH.BR.Closure.PrivateCompletion
  LeanCH.BR.Closure.TopOvershoot LeanCH.BR.Closure.BoundaryHub LeanCH.BR.Closure.UnitState

variable {D : CH.Digraph} {U : Finset ℕ} {q t : ℕ}

/-- The lower-quota host exclusion as an order law. -/
theorem orderLaw_of_noHost (none : NoHost q t) : OrderLaw q t (q*t+1) := by
  intro E W free deg live
  by_contra small
  exact none E W live (by omega) free deg

/-- Without a host the shortfall is positive. -/
theorem total_pos (none : NoHost q t) (free : QFree D U q) (live : U.Nonempty)
    (small : U.card ≤ q*t) : 0 < total t D U := by
  by_contra zero
  have all : ∀ v ∈ U, cost t D U v = 0 :=
    (sum_eq_zero_iff (s := U) (f := cost t D U)).mp (by unfold total at zero; omega)
  exact none D U live small free (fun v hv => by
    have := all v hv
    unfold cost at this
    omega)

/-- One row short by one and every other row at quota: shortfall exactly one. -/
theorem total_unit {x : ℕ} (xu : x ∈ U) (row : (outN D U x).card + 1 = t)
    (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card) : total t D U = 1 := by
  unfold total
  rw [sum_eq_single_of_mem x xu (fun v hv ne => by
    have := other v hv ne
    unfold cost
    omega)]
  unfold cost
  omega

theorem total_lone {V : Finset ℕ} {x : ℕ} (L : Lone D V U q t x) : total t D U = 1 :=
  total_unit L.xu L.row L.other

/-- Two distinct short rows: shortfall at least two. -/
theorem total_two {a b : ℕ} (au : a ∈ U) (bu : b ∈ U) (ne : a ≠ b)
    (sa : (outN D U a).card < t) (sb : (outN D U b).card < t) : 2 ≤ total t D U := by
  have sub : ({a, b} : Finset ℕ) ⊆ U := insert_subset au (singleton_subset_iff.mpr bu)
  have le := sum_le_sum_of_subset (f := cost t D U) sub
  rw [sum_pair ne] at le
  unfold total
  unfold cost at le ⊢
  omega

/-- **Carrying shortfall one in the induction.** If neither a host nor a single short row exists
at quota `t`, every survivor set of at most `q t` labels has shortfall at least two. -/
theorem total_ge_two (none : NoHost q t) (near : NoNearHost q t) (free : QFree D U q)
    (live : U.Nonempty) (small : U.card ≤ q*t) : 2 ≤ total t D U := by
  have pos := total_pos none free live small
  by_contra few
  obtain ⟨u, hu, short, full⟩ := unit_profile (show total t D U = 1 by omega)
  exact near D U u hu small free short full

/-- A unit graph at target `d ≥ 2` has at least `q d` labels: one private step would otherwise
pay it inside the lower-quota order. -/
theorem unit_card {d : ℕ} (none : NoHost q d) (hq : 1 ≤ q) (hd : 2 ≤ d) (free : QFree D U q)
    (unit : total d D U = 1) : q*d ≤ U.card := by
  by_contra small
  obtain ⟨u, hu, short, _⟩ := unit_profile unit
  have lt : total d D U < d := by omega
  have pos : 0 < cost d D U u := by
    unfold cost
    omega
  obtain ⟨E, v, fresh, safe, _, _, paid⟩ := private_step free hq lt hu pos
  have card := card_insert_of_notMem fresh
  have none' : total d E (insert v U) = 0 := by omega
  have zero : ∀ w ∈ insert v U, cost d E (insert v U) w = 0 :=
    (sum_eq_zero_iff (s := insert v U) (f := cost d E (insert v U))).mp none'
  exact none E (insert v U) ⟨v, mem_insert_self v U⟩ (by omega) safe (fun w hw => by
    have := zero w hw
    unfold cost at this
    omega)

/-- **No private parent at the boundary order excludes a single short row.** -/
theorem near_of_noPrivate {d : ℕ} (law : QBoundaryNoPrivate q d) (none : NoHost q d)
    (hq : 1 ≤ q) (hd : 2 ≤ d) : NoNearHost q d := by
  intro E W x xw small free row other
  have unit := total_unit xw row other
  have low := unit_card none hq hd free unit
  exact unit_false_of_boundaryNoPrivate law hq hd free (by omega) unit

/-- In-regularity at the boundary order does the same. -/
theorem near_of_inRegular {d : ℕ} (law : QBoundaryInRegular q d) (none : NoHost q d)
    (hq : 1 ≤ q) (hd : 2 ≤ d) : NoNearHost q d :=
  near_of_noPrivate (boundaryNoPrivate_of_inRegular (by omega) law) none hq hd

/-! ### Where the supplied hypothesis is known -/

/-- **In-regularity from the radius-`(q-1)` ball bound.** Parents of a label avoid its ball of
radius `q-1`, so at order `q d + 1` every in-degree is at most `d`; the degree sum makes them
equal. This is the argument of `PrivateHeadClone.degree_two_obstruction` at every degree. -/
theorem inRegular_of_ball {d : ℕ} (hq : 1 ≤ q)
    (grow : ∀ (E : CH.Digraph) (W : Finset ℕ), QFree E W q → (∀ v ∈ W, d ≤ (outN E W v).card) →
      ∀ v ∈ W, d*(q-1)+1 ≤ (ball E W v (q-1)).card) : QBoundaryInRegular q d := by
  intro E W free size deg v hv
  have arith : d*(q-1) + d = q*d := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k+1 := ⟨q-1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have upper : ∀ w ∈ W, (BR45.inN E W w).card ≤ d := by
    intro w wm
    have limit := ExclusiveBankRouting.parent_room hq free wm
    have big := grow E W free deg w wm
    omega
  have sum := BR45.sum_out_in E W
  have lower := sum_le_sum deg
  have higher := sum_le_sum upper
  exact (sum_eq_sum_iff_of_le upper).mp (le_antisymm higher (sum ▸ lower)) v hv

/-- Degree two, every cutoff: the ball bound is `BRq2.ball_growth`. -/
theorem inRegular_two (hq : 1 ≤ q) : QBoundaryInRegular q 2 :=
  inRegular_of_ball hq (fun E W free deg v hv => by
    have := ball_growth q hq E W free deg v hv (q-1) (by omega)
    omega)

/-! ### On the marked cell -/

variable {r : ℕ} {X : ShenMinimumOrder.Source q r} {m : Cell}

theorem survivors_card (cell : Marked X m) : (X.V \ m.bank).card = q*(r-1) := by
  have size := cell.size
  have card := card_sdiff_add_card_eq_card cell.sub
  have pos := card_pos.mpr ⟨m.parent, cell.erased⟩
  omega

/-- The lone child is a unit graph at target `r-1` on exactly `q(r-1)` labels. -/
@[aesop safe forward (immediate := [cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem lone_unit (cell : Marked X m) (lone : LoneBlocked X m) :
    total (r-1) X.D (X.V \ m.bank) = 1 :=
  total_unit cell.xu cell.deficit lone.paid_elsewhere

/-- A second short row is shortfall at least two. -/
@[aesop safe forward (immediate := [cell,joint]) (rule_sets := [CHGraphFamilies])]
theorem joint_total (cell : Marked X m) (joint : JointShort X m) :
    2 ≤ total (r-1) X.D (X.V \ m.bank) := by
  obtain ⟨j, ju, jx, short⟩ := joint
  exact total_two cell.xu ju (Ne.symm jx) (by have := cell.deficit; omega) short

/-- With both exclusions one degree down, every marked bank has a second short row. -/
@[aesop safe forward (immediate := [hq,none,near,cell]) (rule_sets := [CHGraphFamilies])]
theorem joint_of_near (hq : 2 ≤ q) (none : NoHost q (r-1)) (near : NoNearHost q (r-1))
    (cell : Marked X m) : JointShort X m :=
  (split_bank hq none cell).resolve_right (fun lone => near_exit near cell lone)

/-- **The lone child closes from the no-private-parent law one degree down.** -/
@[aesop safe forward (immediate := [law,hq,hr,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem lone_exit_noPrivate (law : QBoundaryNoPrivate q (r-1)) (hq : 1 ≤ q) (hr : 3 ≤ r)
    (cell : Marked X m) (lone : LoneBlocked X m) : False :=
  unit_false_of_boundaryNoPrivate law hq (by omega) (X.free.mono_set sdiff_subset)
    (survivors_card cell) (lone_unit cell lone)

/-- **The lone child closes from in-regularity at the boundary order one degree down.** -/
@[aesop safe forward (immediate := [law,hq,hr,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem lone_exit_inRegular (law : QBoundaryInRegular q (r-1)) (hq : 1 ≤ q) (hr : 3 ≤ r)
    (cell : Marked X m) (lone : LoneBlocked X m) : False :=
  lone_exit_noPrivate (boundaryNoPrivate_of_inRegular (by omega) law) hq hr cell lone

/-- **A second bank inside the lone cell.** With the host exclusion two degrees down, delete any
`Z` leaving at most `q(r-2)` survivors: either the short row points into `Z`, or another surviving
row has two heads in `Z`. -/
theorem lone_second_bank (lower : NoHost q (r-2)) (hr : 2 ≤ r) (cell : Marked X m)
    (lone : LoneBlocked X m) (Z : Finset ℕ) (live : ((X.V \ m.bank) \ Z).Nonempty)
    (small : ((X.V \ m.bank) \ Z).card ≤ q*(r-2)) :
    (m.x ∉ Z ∧ ∃ z ∈ Z, X.D m.x z = true) ∨
      ∃ y ∈ (X.V \ m.bank) \ Z, y ≠ m.x ∧ 2 ≤ (outN X.D Z y).card := by
  have unit : total (r-2+1) X.D (X.V \ m.bank) = 1 := by
    rw [show r-2+1 = r-1 by omega]
    exact lone_unit cell lone
  obtain ⟨u, hu, short, full, law⟩ := unit_low_row_of_total
    (X.free.mono_set sdiff_subset) (orderLaw_of_noHost lower) unit
  have ux : u = m.x := by
    by_contra ne
    have := lone.paid_elsewhere u hu ne
    omega
  rw [ux] at law
  exact law Z live small

#print axioms total_pos
#print axioms total_lone
#print axioms total_two
#print axioms total_ge_two
#print axioms unit_card
#print axioms near_of_noPrivate
#print axioms near_of_inRegular
#print axioms inRegular_of_ball
#print axioms inRegular_two
#print axioms lone_unit
#print axioms joint_total
#print axioms joint_of_near
#print axioms lone_exit_noPrivate
#print axioms lone_exit_inRegular
#print axioms lone_second_bank
end LeanCH.BR.ShortfallBridge
