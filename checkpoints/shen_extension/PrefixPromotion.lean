import checkpoints.shen_extension.PublicResults

/-!
# Promotion of the completed prefix

Every window of `CoverageRules.ruleWith` that reads the completed prefix reads it through
`ProjectedQuotaTransfer.projectionFloor` (degrees `1 … 8` closed, so the floor is `9`). Each of
those windows has one generic exclusion theorem, stated for an arbitrary floor with the lower
hosts as a hypothesis. This file states the rule with the floor as a parameter and proves it
sound for any floor that is known to bound the degree of every counterexample:

* `ruleWithAt F`: rules 1–32 with the prefix `F` in place of `projectionFloor`
  (`ruleWithAt_floor`: at `F = projectionFloor` it is `CoverageRules.ruleWith`).
* `hosts_every`: a floor law gives `NoHost q t` at every cutoff for every `t < F`.
* `base_zero_at`: for `9 ≤ F`, a closed degree `F - 1` and a floor law `F ≤ s`, no
  counterexample meets `ruleWithAt F` with the climb bounds computed at the floor `F`.
* `ClosedQuota.next`: a closed degree raises the floor law by one. So a closed degree `F`
  together with the floor law `F ≤ s` gives the hypotheses of `base_zero_at` at `F + 1`:
  this is the recursion step.

First use, degree nine (`LeanCH.Results.degree_nine`):

* `closed_nine : ClosedQuota 9`, `floor_ten : Bad p → 10 ≤ p.s`.
* `ruleTen n r q`, `zero_on_bad_ten`, `ch_of_ruleTen`: rules 1–32 at the prefix `10`. Rule 1
  is then `r ≤ 9`, rule 3 the quota window at `9`, and every bank and climb may use hosts of
  degree nine.

Nothing here mentions an order. Whether the promoted rule covers a new cell is an evaluation.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.PrefixPromotion
open Finset CHRuleCatalog ProjectedQuotaTransfer BypassRepair

/-- `CoverageRules.ruleWith` with the completed prefix as the parameter `F`. -/
def ruleWithAt (F b3 b b3' : ℕ) (n r q : ℕ) : Nat :=
  if r ≤ F - 1 then 1
  else if q = 3 ∧ r ≤ 9 then 2
  else if QuotaWindow n r q (F - 1) then 3
  else if 2*r-6 < q ∨ (q = 2*r-6 ∧ (11 < r ∨ n < q*r)) then 4
  else if 7 ≤ r ∧ q = 2*r-7 ∧ n+4 ≤ q*r then 5
  else if 9 ≤ r ∧ q = 2*r-6 ∧ 0 < n ∧ n ≤ q*r then 30
  else if 11 ≤ r ∧ q = 2*r-7 ∧ 0 < n ∧ n+1 ≤ q*r then 31
  else if n < ShellBankFrontier.orderFloor q r then 6
  else if SinkDepthCover.Fits n r q then 7
  else if LowShellCycleSelection.searchedWindow n r q then 8
  else if n < FifthStripLedger.orderFloor q r then 9
  else if PeelWindow n r q F then 10
  else if InheritedProfileWindow.Fits n r q completedLibrary.ranks then 11
  else if MixedBankWindow n r q F then 12
  else if FragmentScoreEquality.FlatWindow n r q F then 13
  else if FragmentScoreEquality.HeadWindow n r q F then 14
  else if FragmentScoreEquality.LowerHeadWindow n r q F then 15
  else if FragmentScoreEquality.HeadQuota n r q F then 16
  else if DistinctReceiverBudget.FifthTransfer n r q then 17
  else if SharedBankOrderTransfer.Window n r q F then 18
  else if FragmentScoreEquality.FourthWindow n r q F then 19
  else if AvoidedHeadQuota.LiftWindow n r q (AvoidedHeadQuota.spendingFloor q) then 20
  else if AvoidedHeadQuota.BoundaryWindow n r q (AvoidedHeadQuota.spendingFloor q) then 21
  else if SymbolicQuotaSweep.Covers SymbolicQuotaSweep.trianglePrefix.val r q then 22
  else if SingleExitProfile.Window n r q F then 23
  else if RecursivePrefixBudget.Window n r q F then 24
  else if RenewedPrefixWitness.Window n r q F then 25
  else if WideQuotaWindow.Window n r q F then 26
  else if ShapeClimb.Window n r q F then 27
  else if ShapeClimbAt3.WindowGWith b3 n r q F then 28
  else if ShapeClimbAt.WindowGWith b n r q F then 29
  else if ShapeClimbAt3.WindowGWith b3' n r q F then 32
  else 0

/-- At the recorded prefix the parametrized rule is the rule of the map. -/
theorem ruleWithAt_floor (b3 b b3' n r q : ℕ) :
    ruleWithAt projectionFloor b3 b b3' n r q = CoverageRules.ruleWith b3 b b3' n r q := rfl

/-- The reach bound of rule 32 at the prefix `F`. -/
def reachBound32At (F q r : ℕ) : ℕ :=
  if q + 8 ≤ 2*r then ShapeClimbMono.guardedBoundM q r F 7 else 0

/-- Rules 1–32 at the prefix `F`, with the three climb bounds computed at that prefix. -/
def ruleBaseAt (F n r q : ℕ) : Nat :=
  ruleWithAt F (ShapeClimbMono.guardedBoundM q r F 1) (ShapeClimbAt.guardedBoundAt q r F 2)
    (reachBound32At F q r) n r q

/-- A floor law gives the lower hosts of every cutoff (`ShapeClimbMono.lower_hosts_every` with
the floor as a hypothesis). -/
theorem hosts_every {F : ℕ} (floorLaw : ∀ c : Input, Bad c → F ≤ c.s) (q t : ℕ) (low : t < F) :
    NoHost q t := by
  intro E U live size free deg
  have cardPos := card_pos.mpr live
  rcases Nat.eq_zero_or_pos t with rfl | pos
  · omega
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · omega
  let p : Input := ⟨q, 1, fun _ _ => false⟩
  have cp : cutoff p = q := by simp [cutoff, CH.ceilDiv, p]
  obtain ⟨c, -, child, cs, -⟩ := BypassDegreeDescent.host_child p pos (by omega) live
    (by rw [cp]; exact size) (by rw [cp]; exact free) deg
  have bad : Bad c := ⟨child.order, child.degree_pos, child.loopless, child.degree,
    fun hit => ShapeClimbMono.arcless_no_cycle _ _ (child.pullback hit)⟩
  have floor : F ≤ c.s := floorLaw c bad
  omega

/-- **The recursion step.** A closed degree raises the floor law by one. -/
theorem ClosedQuota.next {F : ℕ} (cert : ClosedQuota F)
    (floorLaw : ∀ c : Input, Bad c → F ≤ c.s) : ∀ c : Input, Bad c → F + 1 ≤ c.s :=
  fun c bad => next_degree bad cert (floorLaw c bad)

/-- **Rules 1–32 at any completed prefix.** For `9 ≤ F`, if degree `F - 1` is closed and every
counterexample has degree at least `F`, no counterexample meets the rule at the prefix `F`. -/
theorem base_zero_at {F : ℕ} (hF : 9 ≤ F) (cert : ClosedQuota (F - 1))
    (floorLaw : ∀ c : Input, Bad c → F ≤ c.s) (p : Input) (bad : Bad p) :
    ruleBaseAt F p.n p.s (cutoff p) = 0 := by
  have floor : F ≤ p.s := floorLaw p bad
  have known : ∀ t, t < F → NoHost (cutoff p) t := lower_hosts bad floorLaw
  have triangle : cutoff p = 3 → 10 ≤ p.s := CompromiseQuotaTransfer.any_triangle_degree bad
  have quota : ¬QuotaWindow p.n p.s (cutoff p) (F - 1) := quota_window_missed bad cert
  have region := (remaining_from_run p bad).2.2
  have strip : ¬(2*p.s-6 < cutoff p ∨ (cutoff p = 2*p.s-6 ∧ (11 < p.s ∨ p.n < cutoff p*p.s))) := by
    rcases region with ⟨_,_,_,top⟩ | ⟨_,_,_⟩
    · rcases top with eq|⟨deg,eq⟩ <;> omega
    · omega
  have fifth : ¬(7 ≤ p.s ∧ cutoff p = 2*p.s-7 ∧ p.n+4 ≤ cutoff p*p.s) :=
    exclusion_from_run p bad .fifthLow
  have reach : ¬ShapeClimbAt3.WindowGWith (ShapeClimbMono.guardedBoundM (cutoff p) p.s F 1)
      p.n p.s (cutoff p) F := ShapeClimbMono.excludedGM bad (hosts_every floorLaw)
  have climb : ¬ShapeClimbAt.WindowGWith (ShapeClimbAt.guardedBoundAt (cutoff p) p.s F 2)
      p.n p.s (cutoff p) F := ShapeClimbAt.excludedG bad known
  have reach3 : ¬ShapeClimbAt3.WindowGWith (reachBound32At F (cutoff p) p.s) p.n p.s (cutoff p)
      F := by
    unfold reachBound32At
    split
    · exact ShapeClimbMono.excludedGM bad (hosts_every floorLaw)
    · exact fun ⟨_, _, _, pos, le⟩ => by omega
  have fourth : ¬(9 ≤ p.s ∧ cutoff p = 2*p.s-6 ∧ 0 < p.n ∧ p.n ≤ cutoff p*p.s) :=
    fun ⟨hs, hq, hn, hnq⟩ => bad.missing
      (FourthStripTopAll.cycle_fourth_strip_closed_all hs hq hn hnq bad.loopless bad.degree)
  have fifthTop : ¬(11 ≤ p.s ∧ cutoff p = 2*p.s-7 ∧ 0 < p.n ∧ p.n < cutoff p*p.s) :=
    fun ⟨hs, hq, hn, hnq⟩ => bad.missing
      (FifthStripAll.cycle_fifth_strip_below_top_all hs hq hn hnq bad.loopless bad.degree)
  simp [ruleBaseAt, ruleWithAt, reach, climb, reach3, fourth, fifthTop,
    show ¬p.s ≤ F - 1 by omega, show ¬(cutoff p = 3 ∧ p.s ≤ 9) by
      rintro ⟨h,le⟩; exact (triangle h).not_gt (by omega), quota, strip, fifth,
    Nat.not_lt_of_ge (ShellBankFrontier.native_order p bad),
    SinkDepthCover.exclude bad, LowShellCycleSelection.outside_search bad,
    Nat.not_lt_of_ge (ReachCompletionCatalog.bad_order bad), peel_after_prefix bad known,
    inherited_at_completed bad, mixed_after_prefix bad (by omega : 0 < F) known,
    FragmentScoreEquality.replay_flat bad known, FragmentScoreEquality.on_bad bad known,
    FragmentScoreEquality.lower_head_window bad known,
    FragmentScoreEquality.head_quota_exit bad known, DistinctReceiverBudget.fifth_transfer bad,
    SharedBankOrderTransfer.excluded bad known, FragmentScoreEquality.uniform_exit bad known,
    AvoidedHeadQuota.lift_excluded bad (AvoidedHeadQuota.available bad),
    AvoidedHeadQuota.window_excluded bad (AvoidedHeadQuota.available bad),
    SymbolicQuotaSweep.replay_outside bad, SingleExitProfile.excluded bad known,
    RecursivePrefixBudget.excluded bad known, RenewedPrefixWitness.excluded bad known,
    WideQuotaWindow.excluded bad known, ShapeClimb.excluded bad known]

/-- A nonzero cell of the rule at a sound prefix is a Caccetta–Häggkvist bound. -/
theorem ch_of_ruleAt {F : ℕ} (hF : 9 ≤ F) (cert : ClosedQuota (F - 1))
    (floorLaw : ∀ c : Input, Bad c → F ≤ c.s) {n r : ℕ} (D : CH.Digraph) (order : 0 < n)
    (positive : 0 < r) (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (cell : ruleBaseAt F n r (CH.ceilDiv n r) ≠ 0) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  exact cell (base_zero_at hF cert floorLaw ⟨n, r, D⟩ ⟨order, positive, loopless, degree, missing⟩)

/-! ### First use: degree nine -/

/-- Degree nine is a closed degree. -/
theorem closed_nine : ClosedQuota 9 :=
  ⟨by decide, fun p bad hs => by
    have deg := bad.degree
    rw [hs] at deg
    apply bad.missing
    show CH.HasDirectedCycleAtMost p.D p.n (CH.ceilDiv p.n p.s)
    rw [hs]
    exact LeanCH.Results.degree_nine p.D bad.order bad.loopless deg⟩

/-- Every counterexample has degree at least ten. -/
theorem floor_ten {p : Input} (bad : Bad p) : 10 ≤ p.s :=
  ClosedQuota.next closed_nine (fun _ b => replay_completed_floor b) p bad

/-- No host of degree at most nine, at any cutoff. -/
theorem hosts_ten (q t : ℕ) (low : t < 10) : NoHost q t :=
  hosts_every (fun _ b => floor_ten b) q t low

/-- Rules 1–32 at the prefix ten. -/
def ruleTen (n r q : ℕ) : Nat := ruleBaseAt 10 n r q

theorem zero_on_bad_ten (p : Input) (bad : Bad p) : ruleTen p.n p.s (cutoff p) = 0 :=
  base_zero_at (F := 10) (by decide) closed_nine (fun _ b => floor_ten b) p bad

theorem ch_of_ruleTen {n r : ℕ} (D : CH.Digraph) (order : 0 < n) (positive : 0 < r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (cell : ruleTen n r (CH.ceilDiv n r) ≠ 0) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) :=
  ch_of_ruleAt (F := 10) (by decide) closed_nine (fun _ b => floor_ten b) D order positive
    loopless degree cell

#print axioms hosts_every
#print axioms base_zero_at
#print axioms closed_nine
#print axioms floor_ten
#print axioms hosts_ten
#print axioms zero_on_bad_ten
#print axioms ch_of_ruleTen
end LeanCH.BR.PrefixPromotion
