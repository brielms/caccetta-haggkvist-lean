import checkpoints.shen_extension.ProjectedQuotaTransfer
import checkpoints.shen_extension.ShellBankFrontier
import checkpoints.shen_extension.SinkDepthCover
import checkpoints.shen_extension.OneSpareBoundary

namespace LeanCH.BR.SymbolicQuotaSweep
open CHRuleCatalog BRq2 BRq3

/-- A bad input at cutoff three must have order strictly above this bound. -/
def TriangleBound (m : ℕ) : Prop :=
  ∀ p : Input, Bad p → cutoff p = 3 → m < p.n

/-- At any cutoff, an order floor above the maximal order excludes the whole
strip. If the floor meets that order, only equality needs an endpoint proof. -/
@[ch_numeric_guard] def Covers (m r q : ℕ) : Prop :=
  (q = 3 ∧ q*r ≤ m) ∨
  (4 ≤ q ∧ 3 ≤ r ∧ r ≤ 2*q ∧
    (r+(r-1))*(r+(r-1)+1) < 2*(r*(r+3)+(r-1)*7) ∧ q*r ≤ 4*r) ∨
  q*r < ShellBankFrontier.orderFloor q r ∨
  (q*r ≤ ShellBankFrontier.orderFloor q r ∧
    (SinkDepthCover.Fits (q*r) r q ∨ LowShellCycleSelection.searchedWindow (q*r) r q))

instance {m r q} : Decidable (Covers m r q) := by unfold Covers; infer_instance

/-- The finite cutoff interval comes from Shen descent on a bad input. -/
def unresolved (m r : ℕ) : Finset ℕ :=
  (Finset.Icc 3 (2*r-6)).filter (fun q => ¬ Covers m r q)

/-- Use the triangle bound on this very graph; it may depend on its other marks. -/
theorem outside {m} {p : Input} (bad : Bad p) (tri : cutoff p = 3 → m < p.n) :
    ¬ Covers m p.s (cutoff p) := by
  have size : p.n ≤ cutoff p*p.s := by
    have pos := bad.degree_pos
    change p.n ≤ ((p.n+p.s-1)/p.s)*p.s
    have eq := Nat.mod_add_div (p.n+p.s-1) p.s
    have lt := Nat.mod_lt (p.n+p.s-1) pos
    rw [Nat.mul_comm p.s] at eq
    omega
  have shell := ShellBankFrontier.native_order p bad
  rintro (⟨cut,cap⟩ | ⟨cut,deg,fit,short,cap⟩ | above | ⟨atTop,exit⟩)
  · have := tri cut
    omega
  · have bound := OneSpareGrowth.above_four_times (qfree_of_noShort bad.loopless bad.missing)
      cut (Finset.nonempty_range_iff.mpr bad.order.ne')
      (fun v hv => Compose.FloorSix.out_card bad.degree (Finset.mem_range.mp hv)) deg fit short
    rw [Finset.card_range] at bound
    omega
  · omega
  · have eq : cutoff p*p.s = p.n := by omega
    rw [eq] at exit
    exact exit.elim (SinkDepthCover.exclude bad) (LowShellCycleSelection.outside_search bad)

theorem remaining {m} {p : Input} (bad : Bad p) (tri : cutoff p = 3 → m < p.n) :
    cutoff p ∈ unresolved m p.s := by
  obtain ⟨lo, _, tail⟩ := remaining_from_run p bad
  have hi : cutoff p ≤ 2*p.s-6 := by
    rcases tail with ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo, hi⟩, outside bad tri⟩

/-- If all possible cutoffs are excluded, the degree is closed at every order. -/
theorem certify {m r}
    (tri : ∀ p : Input, Bad p → p.s = r → cutoff p = 3 → m < p.n) (positive : 0 < r)
    (empty : unresolved m r = ∅) : ProjectedQuotaTransfer.ClosedQuota r := by
  refine ⟨positive, fun p bad deg => ?_⟩
  have mem := remaining bad (tri p bad deg)
  rw [deg, empty] at mem
  exact Finset.notMem_empty _ mem

/-- The existing triangle exclusion supplies one certified input bound. -/
def trianglePrefix : {m : ℕ // TriangleBound m} :=
  ⟨24, fun p bad h => Nat.lt_of_not_ge
    (fun small => exclusion_from_run p bad .triangle24 ⟨h, small⟩)⟩

theorem replay_outside {p : Input} (bad : Bad p) :
    ¬ Covers trianglePrefix.val p.s (cutoff p) := outside bad (trianglePrefix.property p bad)

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] replay_outside
attribute [aesop safe forward (immediate := [bad,tri]) (rule_sets := [CHGraphFamilies])] remaining

#print axioms outside
#print axioms certify
end LeanCH.BR.SymbolicQuotaSweep
