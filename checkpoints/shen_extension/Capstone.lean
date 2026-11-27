import checkpoints.shen_extension.CommonTensorClosure
import checkpoints.shen_extension.ThirdStrip
import checkpoints.shen_extension.ThirdStripEndpoints
import checkpoints.shen_extension.DotTwoPassShellTransport_20261117
import checkpoints.shen_extension.DotFourthStripClosure_20261118
import checkpoints.shen_extension.FourthStrip
import checkpoints.shen_extension.FourthStripFlat
import checkpoints.shen_extension.FourthStripTop
import checkpoints.shen_extension.FifthStripMixedClone
import checkpoints.shen_extension.NearTotalTensor
import checkpoints.shen_extension.SixthStripTraffic
import checkpoints.shen_extension.CumulativeDeficitTensor
import checkpoints.shen_extension.TerminalTransport
import checkpoints.shen_extension.CutReturnIncidence
import checkpoints.shen_extension.TransitionGraph
import checkpoints.shen_extension.ReachTransition
import checkpoints.shen_extension.MinimumOrderProfile
import checkpoints.shen_extension.TightCycleSuccessor
import checkpoints.shen_extension.UnitRowPacking
import checkpoints.shen_extension.FiveParentEndpoint
import checkpoints.shen_extension.UnitLoopCapstone
import checkpoints.shen_extension.CycleClassFrontier
import checkpoints.shen_extension.PunctureFrontier
import checkpoints.shen_extension.MarkedRolePayment
import checkpoints.shen_extension.AllCutoffPacketEscape
import checkpoints.shen_extension.TwoSidedPuncture
import checkpoints.shen_extension.PairEscapeTransition
import checkpoints.shen_extension.PairWithdrawal
import checkpoints.shen_extension.NativePaidHeadFork
import checkpoints.shen_extension.ShortSplitExterior
import checkpoints.shen_extension.ChargedLabelOrbit
import checkpoints.shen_extension.PunctureFlowCapstone
import checkpoints.shen_extension.OpposedExteriorCapacity
import checkpoints.shen_extension.CoupledArcTrajectory
import checkpoints.shen_extension.SharedArcComponentExchange
import checkpoints.shen_extension.SharedArcFlatBudget
import checkpoints.shen_extension.SharedArcPivotFold
import checkpoints.shen_extension.SharedArcCleanRecurrence
import checkpoints.shen_extension.StrictReturnLayers
import checkpoints.shen_extension.PairedReturnCuts
import checkpoints.shen_extension.ForwardMerge
import checkpoints.shen_extension.RankedMerge
import checkpoints.shen_extension.TwoReceiverIntersection
import checkpoints.shen_extension.SharedArcFlatTransport
import checkpoints.shen_extension.SingleArcNeighbourWitness
import checkpoints.shen_extension.SingleArcAlternative
import checkpoints.shen_extension.SingleArcDoubleExchange
import checkpoints.shen_extension.SingleArcPunctureSign
import checkpoints.shen_extension.PunctureWalkCertificate
import checkpoints.shen_extension.OneStepColumnMerge
import checkpoints.shen_extension.EndpointLayerWitness
import checkpoints.shen_extension.ReturnRowPrices
-- The saturated interval child excludes every signed endpoint payment when old flatness is dropped.
import checkpoints.shen_extension.EndpointLayerControl
-- The local return law alone permits a strictly positive tensor at every entry.
import checkpoints.shen_extension.SingleArcLocalSignExample
import checkpoints.shen_extension.StrictFlatSubsetMerge
import checkpoints.shen_extension.StrictMergeSignControl
import checkpoints.shen_extension.SingleArcTensorMerge
import checkpoints.shen_extension.ReachInversePrices
import checkpoints.shen_extension.CommonParentHeadRepair
import checkpoints.shen_extension.CHRuleCatalog
import checkpoints.shen_extension.CHExitSuppliers
import checkpoints.shen_extension.CommonParentEndpointReplay
import checkpoints.shen_extension.CHContextCatalog
import checkpoints.shen_extension.CutoffCapstoneEntry
import checkpoints.shen_extension.TwoHeadAncestorReplay
import checkpoints.shen_extension.TwoParentOpposedBanks
import checkpoints.shen_extension.TwoParentOldWeight
import checkpoints.shen_extension.LastArcCompetitor
import checkpoints.shen_extension.ReturnSuffixCover
import checkpoints.shen_extension.ReturnIncidenceAntichain
import checkpoints.shen_extension.SingleArcMidpointSign
import checkpoints.shen_extension.SingleArcCycleParents
import checkpoints.shen_extension.SingleArcCyclePivot
import checkpoints.shen_extension.SingleArcCycleHead
import checkpoints.shen_extension.SingleArcCycleBalance
import checkpoints.shen_extension.CommonParentRepair
import checkpoints.shen_extension.CornerResidualJoint
import checkpoints.shen_extension.CornerBlockPayment
import checkpoints.shen_extension.CornerBlockExchange
import checkpoints.shen_extension.CornerBlockSubstitution
import checkpoints.shen_extension.CornerBlockInterval
import checkpoints.shen_extension.CornerBlockRegular
import checkpoints.shen_extension.CornerTowerPayment
import checkpoints.shen_extension.WeightedColumnEscape
import checkpoints.shen_extension.RadiusColumnRecurrence
import checkpoints.shen_extension.ThresholdReturn
import checkpoints.shen_extension.IrregularBlockPacking
import LeanCH.BR.BRq5All
import LeanCH.BR.BR96
import LeanCH.BR.Triangle24
import checkpoints.shen_extension.ReceiverSharedBank
import checkpoints.shen_extension.FeederStrictReplay
import checkpoints.shen_extension.VerifiedDegreeFrontier
import checkpoints.shen_extension.PrefixOrderFrontier
import checkpoints.shen_extension.PackingForwardRules
import checkpoints.shen_extension.RankedExteriorParents
import checkpoints.shen_extension.JointShortcutReplay
import checkpoints.shen_extension.RetainedMixedCapacity
import checkpoints.shen_extension.MinimalPowerDescent
import checkpoints.shen_extension.WeightedJointCatalog
import checkpoints.shen_extension.InsertionTestCatalog
import checkpoints.shen_extension.MinimumDegreeFrontier
import checkpoints.shen_extension.ShortfallBankReplay
import checkpoints.shen_extension.ReachCompletionCatalog
import checkpoints.shen_extension.OldCorridorCapacity
import checkpoints.shen_extension.InheritedProfileWindow
import checkpoints.shen_extension.PhysicalCycleStockWitnessReplay
import checkpoints.shen_extension.SecondaryCycleCohort
import checkpoints.shen_extension.TallBankTransferWitnessReplay
import checkpoints.shen_extension.TerminalLayerReturns
import checkpoints.shen_extension.EqualMixedShells
import checkpoints.shen_extension.SinkDepthCover
import checkpoints.shen_extension.CoverageContradictions
import checkpoints.shen_extension.ReceiverMarkedRoot
import checkpoints.shen_extension.ShellExcessFork
import checkpoints.shen_extension.RootLowerQuotas
import checkpoints.shen_extension.WideCutoffOrder
import checkpoints.shen_extension.RecipientUnionReplay
import checkpoints.shen_extension.ShellBankFrontier
import checkpoints.shen_extension.ShellTransferCatalog
import checkpoints.shen_extension.FlatTwoWitnesses
import checkpoints.shen_extension.JointBankOrderReplay
import checkpoints.shen_extension.PairPowerOrder
import checkpoints.shen_extension.PairPowerDomination
import checkpoints.shen_extension.BankRefinementReplay
import checkpoints.shen_extension.CommonHeadCutReplay
import checkpoints.shen_extension.CyclicLayerReplay
import checkpoints.shen_extension.CommonCoreReplay
/-!
# Full CH capstone for the Shen extension path

Run from the repository root:
  lake env lean checkpoints/shen_extension/Capstone.lean

The theorem below is the literal full CH target. Lean checks the completed
cases and reports what remains to prove at the lower-cutoff frontier.
-/

-- Select the joint-short bank at the root's two source entries.
attribute [-aesop] LeanCH.BR.BypassBankReplay.mark

attribute [aesop safe forward (immediate := [joint,lone]) (rule_sets := [CHGraphFamilies])]
  LeanCH.BR.BypassBankReplay.joint_excludes_lone

namespace LeanCH.BR.ShenExtensionCapstone
open BRq2 BRq3 BR45 ShenFirstStrip

private theorem cutoff_one (s : ℕ) : Compose.Boundary.BoundaryRegular 1 s := by
  apply br_of_ball (by decide)
  intro D V hf ho u hu
  change 1≤(ball D V u 0).card
  exact Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩

private theorem cutoff_two (s : ℕ) : Compose.Boundary.BoundaryRegular 2 s := by
  apply br_of_ball (by decide)
  intro D V hf ho u hu
  simp only [Nat.reduceSub,Nat.mul_one]
  classical
  have he : ball D V u 1=insert u (outN D V u) := by
    ext v
    simp only [mem_ball_one hu,Finset.mem_insert]
  have hn : u ∉ outN D V u := fun hh => loopfree hf (by decide) hu (mem_outN.mp hh).2
  rw [he,Finset.card_insert_of_notMem hn,ho u hu]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 96000000 in
/-- Full Caccetta–Häggkvist. Lean exposes the remaining region below. -/
theorem proof : CH.CaccettaHaggkvistConjecture := by with_ch_root_catalog
  apply BypassDegreeDescent.from_root_minimal
  intro original originalBad input inputRepairs inputBad cutoffReduction hNoOneLossChild hNoLowerQuotaHost hMinimalChild
  replay_ch_typed_families
  rcases input with ⟨n,s,D⟩
  obtain ⟨hn,hs,hloop,hdegree,initialCycle⟩ := id inputBad
  change 0<n at hn
  change 0<s at hs
  change CH.Loopless D n at hloop
  change CH.MinOutdegreeAtLeast D n s at hdegree
  change CHRuleCatalog.ReducedCutoff n s at cutoffReduction
  change ¬OneLossCutoffDescent.Window n s (CH.ceilDiv n s) at hNoOneLossChild
  let q := CH.ceilDiv n s
  change BypassRepair.NoHost q (s-1) at hNoLowerQuotaHost
  -- Expose the same minimality proof under the native source's parameters.
  have hSecondQuotaHost : BypassRepair.NoHost q (s-2) :=
    ShortfallBankReplay.next_lower_host inputBad hMinimalChild
  have hThreeDegree : 3≤s := (ShortfallBankReplay.applicable_quota inputBad).2
  have hNativeDegree : 2≤s := (by decide : 2≤6).trans (CHRuleCatalog.remaining_from_run _ inputBad).2.1
  have hcover : n≤q*s := by
    have hmod := Nat.mod_lt (n+s-1) hs
    have hdiv := Nat.mod_add_div (n+s-1) s
    rw [Nat.mul_comm s] at hdiv
    dsimp [q,CH.ceilDiv]
    omega
  have hq : 0<q := by
    by_contra! hz
    have he : q=0 := by omega
    rw [he,Nat.zero_mul] at hcover
    omega
  -- Every lower quota, in the names used below. Rules on free q and r read this one fact.
  have hAllLowerQuotas : ∀t,t<s → BypassRepair.NoHost q t :=
    ReachDescentCatalog.lower_quotas hMinimalChild hq
  change CH.HasDirectedCycleAtMost D n q
  by_cases hwindow : 2*s-4≤q
  · by_contra no
    exact CHRuleCatalog.shen_window_closes ⟨n,s,D⟩ ⟨hn,hs,hloop,hdegree,no⟩ hwindow
  have registeredExclusion (no : ¬CH.HasDirectedCycleAtMost D n q) (g : CHRootExclusions.Gate) :=
    CHRuleCatalog.exclusion_from_run ⟨n,s,D⟩ ⟨hn,hs,hloop,hdegree,no⟩ g
  have registeredOrders (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    CHRuleCatalog.remaining_from_run ⟨n,s,D⟩ ⟨hn,hs,hloop,hdegree,no⟩
  by_cases hq1 : q=1
  · rw [hq1] at hcover ⊢
    exact Compose.Boundary.ch_of_boundaryRegular hs (cutoff_one s) hn hcover hloop hdegree
  by_cases hq2 : q=2
  · rw [hq2] at hcover ⊢
    exact Compose.Boundary.ch_of_boundaryRegular hs (cutoff_two s) hn hcover hloop hdegree
  have hq3 : 3≤q := by omega
  have hNativeCutoff : 2≤q := by omega
  by_cases hSmallRegularCore : ∃U⊆Finset.range n,U.Nonempty ∧ ∃d : ℕ,(d=3 ∨ d=4 ∨ d=5) ∧
      U.card≤3*d ∧ (∀i∈U,(outN D U i).card=d) ∧ (∀i∈U,(inN D U i).card=d)
  · by_contra no
    exact registeredExclusion no .regularCore hSmallRegularCore
  by_cases hbankLaw : q=3 ∧ ShenPuncture.BankLaw s
  · by_contra no
    exact registeredExclusion no .bankLaw hbankLaw
  by_cases hchain : ShenReachTransition.Closes n q D
  · by_contra no
    exact registeredExclusion no .reachTree hchain
  have hSeymourPeels (U : Finset ℕ) (sub : U ⊆ Finset.range n) : ShenSeymour.Peels D U := by
    by_contra stuck
    exact hchain (.seymour hq3 sub stuck)
  have hkernelDense : ¬ShenRootedKernel.Sparse D (Finset.range n) :=
    fun sparse => hchain (.kernels (by omega) hcover hdegree sparse)
  have hexchange : ¬ShenTransversal.ExchangeTest q D (Finset.range n) :=
    fun test => hchain (.exchange test)
  by_cases htree : ShenCircle.Decomposed q D (Finset.range n)
  · by_contra no
    exact registeredExclusion no .circle htree
  have hprimeClasses : ¬(∀ U ⊆ Finset.range n, ShenPrimeTransition.Prime D U →
      ShenParentIntersection.Separated D U U →
      U.card ≤ q+2 ∨ (4≤q ∧ U.card ≤ q+3) ∨ ShenCircle.Consecutive D U) :=
    fun classes => hchain (.columns (by omega) hcover hdegree classes)
  have hprimeWitness (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    ShenParentIntersection.rigid_survivor (by omega : 2≤q) hn hcover hloop hdegree no
  have hminDegree (x) (hx : x ∈ Finset.range n) : s ≤ (outN D (Finset.range n) x).card :=
    Compose.FloorSix.out_card hdegree (Finset.mem_range.mp hx)
  have hRecursivePacking (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    Closure.BankDescentFrontier.recursive_banks (by omega : 2≤q) (qfree_of_noShort hloop no)
      ⟨0,Finset.mem_range.mpr hn⟩ (by simpa only [Finset.card_range] using hcover) hminDegree
  have hPeelPath (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    Closure.ShortestCycleDescent.from_input (by omega : 2≤q) (qfree_of_noShort hloop no)
      ⟨0,Finset.mem_range.mpr hn⟩ (by simpa only [Finset.card_range] using hcover) hminDegree
  by_cases splitTree : Closure.WeightedSplitInduction.Tree q D (fun _ => 1) (Finset.range n)
  · by_contra no
    exact registeredExclusion no .splitTree splitTree
  have hPunctureModel (no : ¬CH.HasDirectedCycleAtMost D n q) :
      ∃X : Closure.ShortestCycleWeights.Model q n,Closure.PunctureFrontier.Conditions X :=
    (CHRuleCatalog.run_sound ⟨n,s,D⟩ ⟨hn,hs,hloop,hdegree,no⟩ CHRuleCatalog.rules 32
      .punctureSource (by decide)).2
  have hSaturatedClass (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    Closure.PunctureFrontier.saturated_from_input (by omega : 2≤q) (qfree_of_noShort hloop no)
      ⟨0,Finset.mem_range.mpr hn⟩ (by simpa only [Finset.card_range] using hcover) hminDegree
  have hRankedLoops (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    Closure.CycleClassFrontier.from_input (by omega : 2≤q) (qfree_of_noShort hloop no)
      ⟨0,Finset.mem_range.mpr hn⟩ (by simpa only [Finset.card_range] using hcover) hminDegree
  have hDenseArc (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    Closure.DenseArc.supply ((qfree_of_noShort hloop no).mono_bound hq3)
      ⟨0,Finset.mem_range.mpr hn⟩ hs hminDegree
  have hUnmatchedRows (no : ¬CH.HasDirectedCycleAtMost D n q) (three : q=3) :=
    Closure.ColumnBlockerEscape.distinct_unmatched ((qfree_of_noShort hloop no).mono_bound hq3)
      ⟨0,Finset.mem_range.mpr hn⟩ hminDegree
      (show (Finset.range n).card≤3*s by simpa only [Finset.card_range,three] using hcover)
  by_cases hOneUnmatchedType : q=3 ∧ ¬ ∃ u∈Finset.range n, ∃ v∈Finset.range n,
      Closure.ColumnBlockerEscape.Unmatched D (Finset.range n) u ∧
      Closure.ColumnBlockerEscape.Unmatched D (Finset.range n) v ∧
      outN D (Finset.range n) u≠outN D (Finset.range n) v
  · by_contra no
    exact registeredExclusion no .oneUnmatched hOneUnmatchedType
  have hMatchingLoops (no : ¬CH.HasDirectedCycleAtMost D n q) (three : q=3) {X}
      (sub : X ⊆ Finset.range n) (renew : ∀ a∈X, ∃ b∈X,
        Closure.ColumnBlockerEscape.Matches D (Finset.range n) a b) :=
    Closure.ColumnBlockerEscape.recurrence ((qfree_of_noShort hloop no).mono_bound hq3)
      hminDegree hs (show (Finset.range n).card≤3*s by simpa only [Finset.card_range,three] using hcover) sub renew
  have hRadiusColumnExit (no : ¬CH.HasDirectedCycleAtMost D n q) (k t : ℕ)
      (room : 3*k≤q) (budget : n≤3*t) :=
    Closure.ColumnBlockerEscape.radius_alternative (qfree_of_noShort hloop no)
      ⟨0,Finset.mem_range.mpr hn⟩ room (by simpa only [Finset.card_range] using budget)
  have hThresholdReturns (no : ¬CH.HasDirectedCycleAtMost D n q) {J H : Finset ℕ} {r k : ℕ}
      (jv : J⊆Finset.range n) (hv : H⊆Finset.range n) (room : k+2≤q)
      (many : ∀h∈H, r≤(outN D (Closure.ThresholdReturn.grown D (Finset.range n) J r k) h).card) :=
    Closure.ThresholdReturn.incidence (qfree_of_noShort hloop no) room jv hv many
  have hRecursiveHeads (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    Closure.RecursiveHeads.from_candidate (qfree_of_noShort hloop no) ⟨0,Finset.mem_range.mpr hn⟩
      hs (by simpa only [Finset.card_range] using hcover) hminDegree
  have hDisjointHeadRows (no : ¬CH.HasDirectedCycleAtMost D n q) (six : 6≤q)
      (small : s<10 ∨ s<4*(q/2-1)+1) :=
    Closure.RecursiveHeads.separated_thinning (qfree_of_noShort hloop no) ⟨0,Finset.mem_range.mpr hn⟩
      hs hminDegree six small
  have hFourCycleOrRectangle (no : ¬CH.HasDirectedCycleAtMost D n q) (u) (hu : u ∈ Finset.range n) :=
    Closure.RecursiveHeads.root_alternative ((qfree_of_noShort hloop no).mono_bound hq3)
      (Finset.card_pos.mp (hs.trans_le (hminDegree u hu)))
  have hHeadRectangle (no : ¬CH.HasDirectedCycleAtMost D n q) (four : 4≤q) (u) (hu : u ∈ Finset.range n) :=
    Closure.RecursiveHeads.rectangle_four ((qfree_of_noShort hloop no).mono_bound four)
      (Finset.card_pos.mp (hs.trans_le (hminDegree u hu)))
  have hcycleSource (no : ¬CH.HasDirectedCycleAtMost D n q) :=
    ShenCycleSuccessor.from_candidate (qfree_of_noShort hloop no) hminDegree
      ⟨0,Finset.mem_range.mpr hn⟩ (by omega) hs
  obtain ⟨kernelHost,khSub,kernelDegree,kernelTerminal⟩ := ShenRootedKernel.terminal_of_candidate
    (q:=q) (D:=D) (V:=Finset.range n) (s:=s) ⟨⟨0,Finset.mem_range.mpr hn⟩,by simpa using hcover,hminDegree⟩
  have hterminalSize (no : ¬CH.HasDirectedCycleAtMost D n q) (x : ℕ) (A : Finset ℕ) :=
    ShenRootedKernel.terminal_kernel_size (x:=x) (A:=A) kernelTerminal (by omega)
      ((qfree_of_noShort hloop no).mono_set khSub)
  by_cases htable : ∃ P : ShenCenterTable.Table q (Finset.range n),
      (∀ i<q, (P.pool i).card ≤ s) ∧ (P.misses D).card ≤ 1
  · by_contra no
    exact registeredExclusion no .centerTable htable
  by_cases hbuffer : ∃ (P : ShenCenterTable.Table q (Finset.range n)) (p : ℕ),
      (∀ i<q, (P.pool i).card≤s) ∧ (P.misses D).card=2 ∧ p∈P.misses D ∧
      (∀ i<q, P.center i≠p) ∧ ∀ a<q, P.center a∈P.misses D →
        P.center a∈DotFullReturnCut.donors D (Finset.range n) q p (P.center (P.label p)) →
        s<(outN D (Finset.range n) (P.center a)).card ∨ (P.pool ((a+1)%q)).card<s
  · by_contra no
    exact registeredExclusion no .buffer hbuffer
  by_cases hhalf : ∀ u∈Finset.range n, let V := Finset.range n
      let B := (ball D V u ((q-1)/2)).erase u
      QFree D B B.card ∨ ((B.card≤2*q ∨ QFree D B ((B.card+1)/2)) ∧
        ∀ x∈B,∀ y∈B,x≠y → (ShenSharedHead.commonOut D V x y).card+1<s)
  · by_contra no
    exact registeredExclusion no .halfBall hhalf
  by_cases h24 : q=3 ∧ n≤24
  · by_contra no
    exact registeredExclusion no .triangle24 h24
  have htriangleOrder : q=3 → 25≤n := by omega
  by_cases htri : q=3 ∧ 3*(n-1)*(n-1)≤6*(n-1)*s+7*s*s
  · by_contra no
    exact registeredExclusion no .nonedgeRatio htri
  have htriangleResidual : q=3 → 6*(n-1)*s+7*s*s<3*(n-1)*(n-1) := by omega
  by_cases hpressure : q=3 ∧ ∃ m≤s,(2*m-s)*(s-1)<2*m*(3*s+1-n) ∧
      ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u,(ShenSharedHead.commonOut D (Finset.range n) u v).card≤m
  · by_contra no
    exact registeredExclusion no .pressure hpressure
  by_cases hpairTest : q=3 ∧ ∃ (F : CH.Digraph) (k : ℕ),(∀ x y,F x y=true → D x y=true) ∧
      OutEq s F (Finset.range n) ∧ ShenSharedHead.CheapPairOnEachActiveArc F (Finset.range n) k ∧
      (k-2)*(k-3)<2*s*(3*s+1-n)
  · by_contra no
    exact registeredExclusion no .pairTest hpairTest
  by_cases hnoFan : q=3 ∧ ∃ (F : CH.Digraph) (k : ℕ),(∀ x y,F x y=true → D x y=true) ∧
      OutEq s F (Finset.range n) ∧ (k-2)*(k-3)<2*s*(3*s+1-n) ∧
      ¬ShenTransitions.MarkedFan F (Finset.range n) s k
  · by_contra no
    exact registeredExclusion no .markedFan hnoFan
  by_cases hshared : q=3 ∧ ∃ F : CH.Digraph, (∀ x y,F x y=true → D x y=true) ∧
      OutEq s F (Finset.range n) ∧ (let g := 3*s+1-n; let V := Finset.range n
      2*ShenSharedHead.sharedMissing F V<n*s*(g*g+3*g) ∨
        ∃ k,2*ShenSharedHead.sharedMissing F V+k*k*ShenSharedHead.activeCount F V<
          (2*k+3)*ShenSharedHead.edges F V (ShenSharedHead.residual F V))
  · by_contra no
    exact registeredExclusion no .sharedHeads hshared
  by_cases hbankCap : q=3 ∧ ∃ b≤6,(b-4)*(b-4)+b+1<s ∧
      ∀ x∈Finset.range n,∀ y∈outN D (Finset.range n) x,(ShenSharedHead.commonOut D (Finset.range n) x y).card≤b
  · by_contra no
    exact registeredExclusion no .bankCap hbankCap
  by_cases hlocal : q=3 ∧ ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u,
      let T := ShenSharedHead.commonOut D (Finset.range n) u v
      QFree D T T.card
  · by_contra no
    exact registeredExclusion no .localBank hlocal
  by_cases hsmall : s≤5
  · by_contra no
    exact registeredExclusion no .lowDegree hsmall
  by_cases hCertifiedPrefix : PrefixFrontier.Gate n s q
  · exact PrefixFrontier.close hn hs hloop hdegree hCertifiedPrefix
  have hdegreeSix : 6≤s := by omega
  have hDegreeTransition := VerifiedDegreeFrontier.cycle_or_remaining D hn hdegreeSix hloop hdegree
  rcases hDegreeTransition with closedDegree | degreeFrontier
  · exact closedDegree
  have hbelowWindow : q<2*s-4 := Nat.lt_of_not_ge hwindow
  by_cases hnextStrip : q=2*s-5
  · by_contra no
    exact registeredExclusion no .thirdStrip hnextStrip
  · have hdeeper : q≤2*s-6 := cutoffReduction.upper.trans (Nat.sub_le_sub_left (by decide : 6≤7) _)
    by_cases hfourthLow : q=2*s-6 ∧ n+2≤q*s
    · by_contra no
      exact registeredExclusion no .fourthLow hfourthLow
    by_cases hfourth : q=2*s-6
    · prefer_ch_descent False.elim (cutoffReduction.no_boundary hdegreeSix hfourth) retaining {
      by_cases high : 12≤s
      · by_contra no
        exact registeredExclusion no .fourthFull ⟨hfourth,high⟩
      have hfourthSmall : s≤11 := by
        first | assumption | exact Nat.le_of_lt_succ (Nat.lt_of_not_ge high)
      by_cases hbelowTop : 8≤s ∧ n<q*s
      · by_contra no
        exact registeredExclusion no .fourthBelow ⟨hfourth,hbelowTop⟩
      by_contra hnoCycle
      obtain ⟨source,horder,hCycleRegular,seed,hSeed,hCycleReach⟩ := hcycleSource hnoCycle
      rw [Finset.card_range] at horder
      obtain ⟨jointBank,hJointMarked,hJointShort,hSelectedParentOrder⟩ :=
        BypassBankReplay.exists_ordered_joint_mark source hCycleRegular hq3
          ((by decide : 4≤6).trans hdegreeSix) (horder.trans hcover) hNoLowerQuotaHost
      have hPaymentImpossible {M x} (C : ShenCycleSuccessor.Cycle source.D source.V q M)
          (hx : x ∈ M) (p : ShenCycleSuccessor.Payment source M x) : False :=
        (horder.trans hcover).not_gt (ShenCycleSuccessor.order_of_payment source (by omega) hs hCycleRegular C hx p)
      obtain ⟨a,ha⟩ : ∃ a, s=a+7 :=
        ⟨s-7,(Nat.sub_add_cancel ((Nat.le_succ 7).trans degreeFrontier.floor)).symm⟩
      have hq' : q=2*a+8 := by
        first
        | assumption
        | rw [hfourth,ha]
          clear * - a
          omega
      have hf : QFree D (Finset.range n) (2*a+8) := by
        rw [← hq']
        exact qfree_of_noShort hloop hnoCycle
      have hmin : ∀ v ∈ Finset.range n, a+7≤(outN D (Finset.range n) v).card := by
        intro v hv
        rw [← ha]
        exact Compose.FloorSix.out_card hdegree (Finset.mem_range.mp hv)
      have hlastTwo : n=q*s ∨ (s=7 ∧ n+1=q*s) := by
        first | exact Or.inl (by assumption) | exact Or.inr (by assumption)
              | clear * - hfourth hfourthLow hbelowTop hcover ha
                omega
      have hStripRigidity : n+1=q*s → ∀ v ∈ Finset.range n,
          (ball D (Finset.range n) v (a+4)).card=(a+7)*(a+4) ∧
          (reverseBall D (Finset.range n) v (a+4)).card=(a+7)*(a+4) := by
        intro hthird
        refine ShenFourthStrip.third_order_rigid hf hmin ?_
        rw [Finset.card_range,← hq',← ha]
        exact hthird
      have hcapped : n+1=q*s → ∀ v ∈ Finset.range n,
          (a+7)*(a+5)≤(ball D (Finset.range n) v (a+5)).card+2 := by
        intro hthird v hv
        refine ShenFourthStrip.capped_R1_growth hf hmin hv ?_
        rw [Finset.card_range,← hq',← ha]
        exact hthird.le
      have hTopR : 8≤s → n=q*s → ∀ v ∈ Finset.range n,
          (a+7)*(a+4)≤(ball D (Finset.range n) v (a+4)).card := by
        intro h8 htop v hv
        have hcard : (Finset.range n).card=(2*a+8)*(a+7) := by
          rw [Finset.card_range,htop,hq',ha]
        exact ShenFourthStrip.top_R_growth hf hmin hv hcard.le (by omega)
      have hTopR1 : 8≤s → ∀ v ∈ Finset.range n,
          (a+7)*(a+5)≤(ball D (Finset.range n) v (a+5)).card+2 :=
        fun h8 v hv => ShenFourthStrip.top_R1_growth hf hmin hv (by omega)
      obtain ⟨weightedSource, hWeightedSource⟩ := hPunctureModel hnoCycle
      obtain ⟨dualBudget,dualSource,hDualSupportSize,hDualSmaller⟩ :=
        Closure.GlobalFamilyDual.select weightedSource (by omega : 2≤q)
      have hNativeSeedLanes := Closure.TwoHeadRepairLanes.native dualSource (by omega : 3≤q) hDualSmaller
      obtain ⟨seedW,seedC,hSeedMass,hSeedStrict,hSeedPos,hSeedRows,hSeedFrontier⟩ :=
        Closure.TwoHeadRepairReplay.on_native dualSource (by omega : 3≤q) hNativeSeedLanes
      obtain ⟨selectedFamily,hSelectedSub,hSelectedCard,hSelectedFeasible,hSelectedMinimal,hSelectedEndpoints⟩ :=
        Closure.JointCycleFamilyBarrier.joint dualSource (by omega : 2≤q)
      obtain ⟨dualX,dualP,dualValue,hDualHigh,hDualXPos,hDualPPos,hDualXMass,hDualPMass,hSelectedRows,hSelectedColumns⟩ :=
        Closure.GlobalFamilyDual.on_family dualSource hDualSmaller hSelectedFeasible
      obtain ⟨dualFamily,hSelectedIn,hDualSub,hSameSelectedGraph,hCompleteFamily,slackA,hSlackA,slackB,hSlackB,hSlackDistinct,
          hSlackProper,hSlackRetained,hForcedPairSlack,hPairCertificate⟩ :=
        Closure.UniversalSlackPair.on_source dualSource (by omega : 2≤q) hDualSmaller hSelectedSub hSelectedCard
          (fun i hi => (hDualXPos i hi).le)
          (fun i hi => by rw [hDualXMass,hSelectedRows i hi]; exact hDualHigh)
      rw [←hSameSelectedGraph] at hCompleteFamily hForcedPairSlack hPairCertificate
      have hDualCard := hSelectedCard.trans (Finset.card_le_card hSelectedIn)
      have hDualRows (i) (hi : i∈dualSource.V) :
          WeightedSD.row q (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V dualX i=dualValue :=
        by rw [hSameSelectedGraph]; exact hSelectedRows i hi
      have hDualColumns (i) (hi : i∈dualSource.V) :
          WeightedSD.col q (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V dualP i=dualValue :=
        by rw [hSameSelectedGraph]; exact hSelectedColumns i hi
      let slackSeed : Closure.PairedFamilyLoop.State dualFamily :=
        ⟨(slackA,slackB),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hSlackA,hSlackB⟩,hSlackDistinct⟩⟩
      have hDualFree := Closure.PrivateArcEndpoints.graph_free dualSource dualFamily
      have hForwardRows (j) (jv : j∈dualSource.V) :
          WeightedSD.mass dualSource.V dualX <
            WeightedSD.row q (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V dualX j := by
        rw [hDualXMass,hDualRows j jv]; exact hDualHigh
      have hBackwardRows (j) (jv : j∈dualSource.V) :
          WeightedSD.mass dualSource.V dualP <
            WeightedSD.row q (fun u v => Closure.FirstPacketBarrier.graph dualSource.D dualFamily v u)
              dualSource.V dualP j := by
        change WeightedSD.mass dualSource.V dualP < WeightedSD.col q _ _ _ j
        rw [hDualPMass,hDualColumns j jv]; exact hDualHigh
      have hForwardReach (U : Finset ℕ) (us : U⊆dualSource.V) (k : ℕ) :=
        Closure.FlatPeelReach.exact_rounds (by omega : 2≤q) hDualFree hDualSmaller us
          (fun i iv=>(hDualXPos i iv).le) (by rw [hDualXMass]; exact hDualHigh) hDualRows k
      have hReverseReach (U : Finset ℕ) (us : U⊆dualSource.V) (k : ℕ) :=
        Closure.FlatPeelReach.exact_rounds (by omega : 2≤q) hDualFree.reverse hDualSmaller us
          (fun i iv=>(hDualPPos i iv).le) (by rw [hDualPMass]; exact hDualHigh) hDualColumns k
      have hForwardArcReturns := @Closure.ForwardMerge.arc_returns q _ _ (by omega : 2≤q)
        hDualFree hDualSmaller dualX hDualXPos hForwardRows
      have hBackwardArcReturns := @Closure.ForwardMerge.arc_returns q _ _ (by omega : 2≤q)
        hDualFree.reverse hDualSmaller dualP hDualPPos hBackwardRows
      have hForwardTriangle := fun (three : q=3) => @Closure.ForwardMerge.triangle_at q _ _
        three hDualFree hDualSmaller dualX hDualXPos hForwardRows
      have hBackwardTriangle := fun (three : q=3) => @Closure.ForwardMerge.triangle_at q _ _
        three hDualFree.reverse hDualSmaller dualP hDualPPos hBackwardRows
      have hForwardDecay := fun (U : Finset ℕ) (us : U⊆dualSource.V) (room : U.card+1<dualSource.V.card) =>
        Closure.ForwardMerge.repeated_decay (by omega : 2≤q) hDualFree hDualSmaller us room dualX hDualXPos hForwardRows
      have hBackwardDecay := fun (U : Finset ℕ) (us : U⊆dualSource.V) (room : U.card+1<dualSource.V.card) =>
        Closure.ForwardMerge.repeated_decay (by omega : 2≤q) hDualFree.reverse hDualSmaller us room dualP hDualPPos hBackwardRows
      have hForwardNoMerge := Closure.ForwardMerge.no_native_merge (by omega : 2≤q) dualSource.free hDualSmaller
      have hNoPair := Closure.RankedMerge.no_pair (by omega : 2≤q) dualSource.free hDualSmaller
      have hParentRecursion := @Closure.TwoReceiverIntersection.upstream_corridor q _ dualSource (by omega : 2≤q)
      have hAllNativeCorners := Closure.TwoReceiverIntersection.all_corners (by omega : 2≤q)
        dualSource.free hDualSmaller dualSource.sat (fun v => (dualSource.weights v : ℚ))
        (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
      have hAllReverseCorners := Closure.TwoReceiverIntersection.reversed_family (by omega : 2≤q)
        dualSource.free hDualSmaller dualSource.sat dualP hDualPPos hBackwardRows
      have hNativeIntersection := fun {b a : dualSource.V} (ba : dualSource.D b a=true) =>
        Closure.TwoReceiverIntersection.corridor_cut (by omega : 2≤q) dualSource.free hDualSmaller
          (a:=a) (b:=b) ba dualSource.sat (fun v => (dualSource.weights v : ℚ))
          (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
      have hForwardCovered := @Closure.RankedMerge.covered_sink q _ _ (by omega : 2≤q) hDualFree hDualSmaller
        dualX hDualXPos (dualValue-1) (sub_pos.mpr hDualHigh) (fun i iv => by
          rw [Closure.ForwardMerge.surplus,hDualRows i iv,hDualXMass])
      have hReverseCovered := @Closure.RankedMerge.covered_sink q _ _ (by omega : 2≤q) hDualFree.reverse hDualSmaller
        dualP hDualPPos (dualValue-1) (sub_pos.mpr hDualHigh) (fun i iv => by
          change dualValue-1≤WeightedSD.col q _ _ dualP i-WeightedSD.mass _ dualP
          rw [hDualColumns i iv,hDualPMass])
      obtain ⟨mergeRoot,hMergeRoot,hMinWeight⟩ := dualSource.V.exists_min_image dualSource.weights dualSource.live
      obtain ⟨mergeParent,hMergeLow,hMergeParent,hMergeCover⟩ :=
        Closure.ForwardShortcutLayers.minimum_covers dualSource (by omega : 2≤q) hDualSmaller
          ⟨mergeRoot,hMergeRoot⟩ (fun v => (dualSource.weights v : ℚ))
          (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
          (fun v hv => by exact_mod_cast hMinWeight v hv)
      have hDualSize : 2≤dualSource.V.card := by
        have := Closure.CyclePhaseFork.support_bound dualSource (by omega : 2≤q)
        omega
      obtain ⟨portScale,portBonus,hPortScale,hPortBonus,hBonusValue,portWeights,hPortWeights,hCyclePortMatching⟩ :=
        Closure.CyclePortMatching.on_family (by omega : 2≤q) hDualHigh hDualSmaller hDualFree
          hDualXPos hDualXMass hDualRows (fun M => (hCompleteFamily M).2)
      obtain ⟨portRoot,hPortRoot,⟨portParent,hPortParent⟩,hRootCollisions⟩ :=
        Closure.CyclePortCollision.collision (by omega : 2≤q) hDualHigh hDualFree hDualXPos
          hDualXMass hDualRows hPortScale hPortBonus hPortWeights
      have hParentOffRoot : portParent≠portRoot := by
        rintro rfl
        exact hDualFree portParent 1 (by omega) (by omega)
          (.step hPortRoot (mem_inN.mp hPortParent).2 (.refl _))
      obtain ⟨portRoute,hPortRoute⟩ := hCyclePortMatching portRoot hPortRoot portParent
        (Finset.mem_erase.mpr ⟨hParentOffRoot,(mem_inN.mp hPortParent).1⟩)
      obtain ⟨hLastPhaseCount,hAnyPortCollision⟩ := hRootCollisions portParent hPortParent
      obtain ⟨portLeft,portRight,hDistinctPortSlots,hLeftParent,hRightParent,hSamePortPosition⟩ :=
        hAnyPortCollision portRoute
      obtain ⟨leftPortCycle,hLeftPortCycle,hLeftOnCycle,hRootOnLeft,hHeadOnLeft⟩ :=
        (hPortRoute portLeft).2.2 hLeftParent
      obtain ⟨rightPortCycle,hRightPortCycle,hRightOnCycle,hRootOnRight,hHeadOnRight⟩ :=
        (hPortRoute portRight).2.2 hRightParent
      obtain ⟨hNativePortMiss,hNativePortDistance,hNativeBicliqueBudget⟩ :=
        Closure.CyclePortNative.on_source dualSource (by omega : 2≤q) hDualSmaller hDualHigh
          hDualXPos hDualPPos hDualXMass hDualPMass hDualRows hDualColumns
      let portGraph := Closure.FirstPacketBarrier.graph dualSource.D dualFamily
      let portU := (dualSource.V.erase portRoot).erase portParent
      let portInnerBall := BRsub.ballSet portGraph portU (outN portGraph portU portRoot) (q-2)
      have portLift (u v) (edge : portGraph u v=true) : dualSource.D u v=true := by
        obtain ⟨C,cc⟩ := Closure.FirstPacketBarrier.active.mp edge
        exact (Closure.MarkedCyclePeeling.mem_col.mp cc).2.2.2
      have portTwo := @Closure.CommonParentHeadRepair.two_rows q portGraph dualSource.D dualSource.V dualX
        portLift (fun K ks O os heads two live => by
          rw [hDualXMass]
          exact (hNativeBicliqueBudget K ks O os heads).1 two live)
        ⟨portParent,(mem_inN.mp hPortParent).1⟩
      obtain ⟨portInner,hPortInner,hPortInnerToParent,hPortInnerMiss,hPortInnerLeast,hPortRecursiveRepair⟩ :=
        Closure.CommonParentHeadRepair.live_run (by omega : 3≤q) hDualFree hDualSmaller dualX hDualXPos
          (by rw [hDualXMass]; exact hDualHigh) hDualRows
          (b:=⟨portParent,(mem_inN.mp hPortParent).1⟩) (a:=⟨portRoot,hPortRoot⟩) (mem_inN.mp hPortParent).2 portTwo
      have hPortTerminal (j : ℕ) (ju : j∈portU) (ja : portGraph j portRoot=true)
          (jb : portGraph j portParent=true) (k : ℕ) (kk : k∈outN portGraph portU portInner) :
          ∃T⊆portU,T.card+1=q ∧ Closure.CommonParentHeadRepair.IndependentHeads portGraph portInnerBall T ∧
            k∈T ∧ Closure.CommonParentHeadRepair.IndependentHeads portGraph
              (portInnerBall.filter (fun r=>portGraph r k=false)) (T.erase k) ∧
            ∃v,Relation.ReflTransGen (Closure.CommonParentHeadRepair.Step q portGraph portU
              (outN portGraph portU portRoot)) ({k},dualX) (T,v) ∧
              Closure.CommonParentEndpointReplay.Fork q portGraph dualSource.V portU
                (outN portGraph portU portRoot) portInnerBall T dualX v ∧
                Closure.EndpointPrivateRows.Tests q portGraph portU (outN portGraph portU portRoot) portInnerBall T v := by
        obtain ⟨_,_,budget,_,go⟩ := hPortRecursiveRepair j ju ja jb
        obtain ⟨l,z,T,v,_,_,_,link,path,ts,count⟩ := go k kk
        exact ⟨T,ts,count,Closure.CommonParentHeadRepair.trace_minor hPortInner (mem_outN.mp kk).2 link path,
          (Closure.CommonParentHeadRepair.avoiding_minor link path).1,
          (Closure.CommonParentHeadRepair.avoiding_minor link path).2,v,path.head link,
          Closure.EndpointPrivateRows.selected (by omega : 3≤q) hDualFree hDualSmaller dualX hDualXPos
            (by rw [hDualXMass]; exact hDualHigh) hDualRows (b:=⟨portParent,(mem_inN.mp hPortParent).1⟩)
            (a:=⟨portRoot,hPortRoot⟩) (mem_inN.mp hPortParent).2 ju hPortInner kk budget link path count⟩
      by_cases hPortFailure : ∃j∈portU,portGraph j portRoot=true ∧ portGraph j portParent=true ∧
          ((∃r∈portInnerBall,(q:ℚ)*WeightedSD.mass (outN portGraph portU r) dualX≤
              dualValue-WeightedSD.mass dualSource.V dualX+dualX j) ∨
           ∃k∈outN portGraph portU portInner,¬∃T⊆portU,T.card+1=q ∧
             Closure.CommonParentHeadRepair.IndependentHeads portGraph portInnerBall T ∧ k∈T ∧
             Closure.CommonParentHeadRepair.IndependentHeads portGraph
               (portInnerBall.filter (fun r=>portGraph r k=false)) (T.erase k) ∧
             ∃v,Relation.ReflTransGen (Closure.CommonParentHeadRepair.Step q portGraph portU
               (outN portGraph portU portRoot)) ({k},dualX) (T,v) ∧
               Closure.CommonParentEndpointReplay.Fork q portGraph dualSource.V portU
                 (outN portGraph portU portRoot) portInnerBall T dualX v ∧
                 Closure.EndpointPrivateRows.Tests q portGraph portU (outN portGraph portU portRoot) portInnerBall T v)
      · obtain ⟨j,ju,ja,jb,fail⟩ := hPortFailure
        rcases fail with ⟨r,rr,low⟩ | ⟨k,kk,deficient⟩
        · exact False.elim (((hPortRecursiveRepair j ju ja jb).2.2.1 r rr).not_ge low)
        · exact False.elim (deficient (hPortTerminal j ju ja jb k kk))
      have hPortLastLayer (i : ↥(ShenReturnCut.slots (dualSource.V.erase portRoot) (Closure.CyclePortMatching.demand portWeights portBonus portParent)))
          (par : Closure.FirstPacketBarrier.graph dualSource.D dualFamily i.val.1 portRoot=true) :=
        hNativePortDistance portRoot hPortRoot (portRoute i).val.1
          (Finset.mem_erase.mp (ShenReturnCut.mem_slots_iff.mp (portRoute i).property).1).2
          i.val.1 (hPortRoute i).2.1 par (hPortRoute i).1
      have hLeftLastLayer := hPortLastLayer portLeft hLeftParent
      have hRightLastLayer := hPortLastLayer portRight hRightParent
      obtain ⟨branchCycle,entry,exitLabel,firstParent,secondParent,firstExit,secondExit,
          sharedLength,entryHead,exitParent,nativeWeights,reverseWeights,entryBonus,exitBonus,
          segmentValue,hEntryBonus,hExitBonus,hSegmentValue,hNativeScale,hReverseScale,
          hSharedSection,hEntryBooking,hExitBooking,hAfterEntry,hBeforeExit⟩ :=
        Closure.CoupledSegmentPorts.on_cycle dualSource (by omega : 2≤q) hDualSmaller
          (C:=leftPortCycle) (by classical exact (Finset.mem_filter.mp (hDualSub hLeftPortCycle)).2)
      have hSegmentReturns := hSharedSection.table (by omega : 2≤q) dualSource.free
      have hSegmentShortcut := hSharedSection.shortcut (by omega : 2≤q) dualSource.free
      have hNativeCycleRoute {A B} (af : A∈Closure.FirstPacketBarrier.family dualSource)
          (bf : B∈Closure.FirstPacketBarrier.family dualSource) :=
        Closure.NativeCycleConnectivity.connected dualSource (by omega : 2≤q) af bf
      have hRouteToSlack := hNativeCycleRoute (hDualSub hLeftPortCycle) (hDualSub hSlackA)
      obtain ⟨thirdCycle,hThirdNative,hThirdOffLeft,hThirdOffBranch,hThirdAdjacent⟩ :=
        Closure.SharedArcInduction.third_cycle dualSource (by omega : 2≤q)
          hSharedSection.cycle₁ hSharedSection.cycle₂ hSharedSection.start
      obtain ⟨attachFamily,hAttachBuilt,hAttachNative,hAttachStart,hAttachSpans,hAttachSmall,
          ⟨attachDual,hAttachDual⟩,hSomeAttachment,hEveryAttachment⟩ :=
        Closure.SharedArcBarrier.on_source dualSource (by omega : 2≤q) hDualSmaller (hDualSub hLeftPortCycle)
      obtain ⟨outsideCycle,hAttachBoundary,hMinimumNewHeads,terminalPrices,terminalValue,hTerminalHigh,
          hTerminalPositive,hTerminalNormalized,hTerminalColumns,hTerminalComparison⟩ :=
        Closure.SharedArcPacketDescent.terminal dualSource (by omega : 2≤q) hDualSmaller hSomeAttachment
          (fun M b => (hEveryAttachment M b).1)
      have hPayExcept {e} (he : e∈Closure.SharedArcBarrier.targets dualSource.D dualSource.V attachFamily outsideCycle) :=
        Closure.SharedArcMinimalPacket.omit_one dualSource (by omega : 2≤q) hDualSmaller hAttachSmall
          hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1) he
      obtain ⟨packetInverse,hPacketInverse,hPacketCharges⟩ :=
        Closure.SharedArcMinimalPacket.charges dualSource (by omega : 2≤q) hDualSmaller hAttachSmall
          hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
      let packetGraph := Closure.FirstPacketBarrier.graph dualSource.D (insert outsideCycle attachFamily)
      have hPacketReachBudget (U : Finset ℕ) := @Closure.ReachInversePrices.column_budget q packetGraph dualSource.V U
        packetInverse (by omega : 2≤q) (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
        (hEveryAttachment _ hAttachBoundary).1 hPacketInverse
      have hPacketReturnChoice := @Closure.ReachInversePrices.alternate q packetGraph dualSource.V packetInverse
        (by omega : 2≤q) (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
        (hEveryAttachment _ hAttachBoundary).1 hPacketInverse
      by_cases hUnderpaidReturn : Closure.ReachInversePrices.Underpaid (q:=q) packetGraph dualSource.V packetInverse ∨
          Closure.ReachInversePrices.Underpaid (q:=q) (fun i j=>packetGraph j i) dualSource.V packetInverse.transpose
      · exact False.elim ((Closure.ReachInversePrices.excludes (by omega : 2≤q)
          (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
          (hEveryAttachment _ hAttachBoundary).1 hPacketInverse) hUnderpaidReturn)
      have hExactPacketParent := Closure.SharedArcPacketReturns.exact_parent dualSource (by omega : 2≤q)
        hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges
      have hDeletionObstruction := @Closure.SharedArcPacketReturns.zero_and_strict q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
        packetInverse hPacketInverse hPacketCharges
      have hPricedAttachmentExit := Closure.SharedArcPacketReturns.blocks_exit dualSource (by omega : 2≤q)
        hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges (fun M b => (hEveryAttachment M b).1)
      have hTerminalProgress := Closure.SharedArcPacketDescent.blocks_progress (p:=terminalPrices) (c:=terminalValue)
        dualSource hPricedAttachmentExit (by
          intro M b count weak v vv
          obtain ⟨_,_,_,_,_,_,_,_,_,plateau⟩ := hTerminalComparison M b count
          exact ((plateau weak).2 v vv).1)
      have hTerminalSquareFloor := @Closure.SharedArcTailExchange.terminal_floor q _ dualSource
        (by omega : 2≤q) attachFamily outsideCycle hAttachBoundary terminalPrices terminalValue hTerminalColumns
        (fun repair => hTerminalProgress (Or.inr repair))
      have hFreshArcTransport := @Closure.SharedArcComponentExchange.transport q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
      have hFreshArcSeparation := @Closure.SharedArcComponentExchange.separate q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
      have hFreshDistanceRectangle := @Closure.SharedArcComponentExchange.distance_rectangle q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
      have hAnyNativeParentFloor := @Closure.SharedArcComponentExchange.all_parents q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
        terminalPrices terminalValue hTerminalColumns (fun repair => hTerminalProgress (Or.inr repair))
      have hExactFlatDynamics := Closure.SharedArcFlatChain.at_terminal dualSource (by omega : 2≤q)
        hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges hTerminalHigh (by
          intro M bm count
          obtain ⟨x,_,d,le,_,xm,rows,_⟩ := hTerminalComparison M bm count
          exact ⟨x,d,le,xm,rows⟩)
      have hSingleArcProfile := @Closure.SingleArcReturnProfile.at_singleton q _ dualSource
        (by omega : 1≤q) attachFamily
      have hSecondNativeArc := @Closure.SingleArcReturnProfile.second_arc q _ dualSource
        (by omega : 1≤q) attachFamily
      have hSingleArcCriterion := @Closure.SingleArcAlternative.singleton_iff q _ dualSource (by omega : 2≤q) attachFamily
      have hDoubleEndpointExchange := @Closure.SingleArcDoubleExchange.native q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily
      have hPunctureSignExit := @Closure.SingleArcPunctureSign.progress q _ dualSource
        (by omega : 2≤q) attachFamily outsideCycle packetInverse terminalPrices terminalValue
      have hBalancedSwitchExit := @Closure.SingleArcPunctureSign.progress_of_switch q _ dualSource
        (by omega : 2≤q) attachFamily outsideCycle packetInverse terminalPrices terminalValue
      have hPunctureShortReturns := @Closure.SingleArcPunctureSign.returns q _ dualSource (by omega : 2≤q) attachFamily
      have hWalkCertificate := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.PunctureWalkCertificate.certificate q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hWalkSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.PunctureWalkCertificate.sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hWalkColumnMoments := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.PunctureWalkCertificate.sign_or_fit q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hWalkColumnCuts := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.PunctureWalkCertificate.common_column q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hOneStepWalkColumn := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.canonical q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc
      have hParentMergeExpansion := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.expansion q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc
      have hCoveredParentSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.cover_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hThinParentSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.thin_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hHeadCoverSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.head_cover_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hCoveredParentsSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.covered_parents_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hFixedMergeSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.fixed_merge_iff q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hEndpointMergeExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.OneStepColumnMerge.endpoint_progress q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hEndpointLayerSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.EndpointLayerWitness.singleton q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hEndpointLayerExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.EndpointLayerWitness.progress q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hReturnRowPayment := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.EndpointLayerWitness.return_payment q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hMissedSetPrices := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.ReturnRowPrices.missed_set_prices q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hCountedReturnPayment := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.ReturnRowPrices.counted_return q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hReturnReserve := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.ReturnRowPrices.return_reserve q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hFlatReturnMass := fun {p : ℕ→ℚ} pc =>
        @Closure.ReturnRowPrices.singleton_return_mass q _ dualSource (by omega : 2≤q) attachFamily p pc
      have hTwoStepEscape := fun {w p : ℕ→ℚ} wp wm wr pc (three : 3≤q) =>
        @Closure.PunctureWalkCertificate.two_step_escape q _ dualSource attachFamily w p wp wm wr pc three hDualSmaller
      have hOrdinaryPuncturePrices := @Closure.SingleArcPunctureSign.ordinary_prices q _ dualSource hDualSmaller
      have hPuncturePricePressure := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.SingleArcPunctureSign.price_pressure q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hPunctureThresholdCycle := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.SingleArcPunctureSign.threshold_cycle q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hPunctureComparisonSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.SingleArcPunctureSign.comparison_rectangle q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
      have hSingleArcPrime := @Closure.SingleArcModuleBoundary.at_singleton q _ dualSource attachFamily
      have hFlatModuleExclusion := @Closure.SingleArcModuleBoundary.on_flat q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hStrictFlatMerges := @Closure.StrictFlatSubsetMerge.native q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hStrictHostMerges := @Closure.StrictFlatSubsetMerge.host q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hEndpointMergeReserve := @Closure.StrictFlatSubsetMerge.endpoint_reserve q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily
      have hTensorWeightedMerges := @Closure.SingleArcTensorMerge.all_cuts q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hTensorMergeExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.SingleArcTensorMerge.progress q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily w p wp wm wr pc
          outsideCycle packetInverse terminalPrices terminalValue
      have hUpstreamOldFeed := @Closure.CornerResidualJoint.joint q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
      have hUpstreamOldArcs := @Closure.CornerResidualJoint.stopped_arc_types q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hBoundarySlotRecurrence := @Closure.CornerHeadRecurrence.frontier q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads hAttachNative hAttachSpans
        (fun M bm => (hEveryAttachment M bm).1)
      have hBlockPayment := @Closure.CornerBlockPayment.on_source q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
      have hBlockReturnCut := @Closure.CornerBlockPayment.path_cut q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
      have hBlockExchange := @Closure.CornerBlockExchange.on_source q _ dualSource (by omega : 2≤q)
        hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hBlockSubstitution := @Closure.CornerBlockSubstitution.on_source q _ dualSource (by omega : 2≤q)
        hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hBoundaryIntervalPrices := @Closure.CornerBlockInterval.joint q _ dualSource (by omega : 2≤q)
        hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hRegularBlockCounts := @Closure.CornerBlockRegular.on_source q _ dualSource (by omega : 2≤q)
        hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      by_cases hTowerBlock : Closure.CornerTowerPayment.SparseBlock dualSource attachFamily outsideCycle
      · exact False.elim ((Closure.CornerTowerPayment.excludes dualSource (by omega : 2≤q) hDualSmaller
          hDualPPos hBackwardRows hAttachBoundary hMinimumNewHeads) hTowerBlock)
      by_cases hIntervalFits : Closure.CornerBlockInterval.Fits dualSource attachFamily outsideCycle
      · exact False.elim ((Closure.CornerBlockInterval.excludes dualSource (by omega : 2≤q) hDualSmaller
          hDualPPos hBackwardRows hAttachBoundary hMinimumNewHeads) hIntervalFits)
      have hMidpointParentLayer := @Closure.SingleArcMidpointSign.return_layer q _ dualSource (by omega : 2≤q) attachFamily
      have hChargedCyclePair := @Closure.SingleArcCycleParents.paired q _ dualSource (by omega : 2≤q) attachFamily
      have hOldCycleSupply := @Closure.SingleArcCycleParents.supply q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
      have hCycleExteriorAccount := @Closure.SingleArcCyclePrices.account q _ dualSource (by omega : 2≤q) attachFamily
      have hCycleCoverExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
        @Closure.SingleArcCyclePrices.cover_progress.{0} q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc
          hDualSmaller outsideCycle packetInverse terminalPrices terminalValue
      have hSingletonExteriorWitness := @Closure.SingleArcCycleHead.singleton q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hVariableTailPrice := @Closure.SingleArcCycleBalance.flexible_bound q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hScalarCycleExit := @Closure.SingleArcCycleBalance.exterior_test q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hFixedParent := @Closure.SingleArcCommonParent.native q _ dualSource (by omega : 2≤q) attachFamily
      have hPairedCycleRepair := fun (C K : Finset ℕ)=>@Closure.CommonParentRepair.on_cycles q _ _ C K hq3
        (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
      have hParentRepairExit := fun {w p : ℕ→ℚ} wp wm wr pc=>@Closure.CommonParentRepair.progress q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily w p wp wm wr pc outsideCycle packetInverse terminalPrices terminalValue
      have hSingletonTiltObstruction := @Closure.SingleArcCommonParent.singleton q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hCommonTiltDecision := fun (C : Finset ℕ)=>@Closure.SingleArcCommonTilt.exact_test q _ _ C (by omega : 2≤q)
        (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
      have hOldHitMean := @Closure.CycleHitMass.mean q (Closure.FirstPacketBarrier.graph dualSource.D attachFamily)
        dualSource.V
      have hSecondNeighborBudgets := @Closure.SingletonSecondNeighbors.flat_ports q _ _ hq3
        (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
      have hBalancedArcBound := @Closure.SingletonSecondNeighbors.balanced_ports q _ _ hq3
        (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
      have hClosedCycleBound := @Closure.SingleArcCyclePivot.diagonal_bound q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hMidpointParentBudgetExit := @Closure.SingleArcMidpointSign.progress q _ dualSource (by omega : 2≤q)
        attachFamily outsideCycle packetInverse terminalPrices terminalValue
      have hHeirMidpointOrCycle := @Closure.SingleArcHeirMidpoint.singleton q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hHoleAncestorObstruction := @Closure.SingleArcResidualSource.both_ends q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily
      have hFlatLawOfHeirs := Closure.HeirLaw.flatLaw_of_heirOrCoheirLaw dualSource (by omega : 2≤q)
      have hSingleArcTriangleAlternatives := fun (three : q=3) =>
        @Closure.SingleArcAlternative.triangle q _ dualSource three attachFamily
      have hIntervalScalarExit := @Closure.SingleArcNeighbourWitness.progress_of_sign q _ dualSource
        (by omega : 2≤q) attachFamily outsideCycle packetInverse terminalPrices terminalValue
      have hIntervalNeighbourExit := fun (three : q=3) => @Closure.SingleArcNeighbourWitness.progress
        q _ dualSource three attachFamily outsideCycle packetInverse terminalPrices terminalValue
      have hFlatCutExit := @Closure.SharedArcFlatTransport.progress_of_failed_cut q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle packetInverse terminalPrices terminalValue
      have hFlatTensorPositive := @Closure.SharedArcFlatArithmetic.positive q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily
      have hFreshEndpointMass := @Closure.SharedArcFlatArithmetic.mass_bound q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily terminalValue
      have hSimultaneousNativeStars := Closure.SharedArcCover.simultaneous dualSource
        (by omega : 2≤q) hDualSmaller hAttachSmall hAttachBoundary hMinimumNewHeads
      have hAllFreshTailsZero := @Closure.SharedArcCover.all_tails_zero q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hTwoMissedTargets := Closure.SharedArcReachMargin.two_targets dualSource (by omega : 2≤q) hDualSmaller
      have hStrictStarMargins := @Closure.SharedArcReachMargin.strict_stars q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hAllSubthresholdMargins := Closure.SharedArcReachMargin.every_strict dualSource
        (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads
      have hStrictMultiParent := Closure.SharedArcStrictParent.parent dualSource (by omega : 2≤q) hDualSmaller
        hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges
      have hStrictDeletionProfile := Closure.SharedArcStrictParent.deletion_profile dualSource
        (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges
      have hSingleReturnCorridor := @Closure.SharedArcSingleCorridor.corridor q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hAllCompetitorReturns := Closure.SharedArcExchangeReturn.bounded_returns dualSource hDualSmaller
        hAttachBoundary (fun M bm => (hEveryAttachment M bm).1)
      have hComponentInverseBound := @Closure.SharedArcExchangeReturn.component q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
        packetInverse hPacketInverse
      have hTensorProgress := Closure.SharedArcFlatArithmetic.blocks dualSource (by omega : 2≤q)
        hDualSmaller hTerminalProgress
      have hCanonicalLoopTest := Closure.SharedArcCompression.winning_iff dualSource hDualSmaller
        hAttachBoundary ((hEveryAttachment _ hAttachBoundary).1)
      have hSinglePivotAlternative := @Closure.SharedArcPivot.alternatives q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hSinglePivotParents := @Closure.SharedArcPivot.classify_parents q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hPivotLink := @Closure.SharedArcPivotPaths.disconnected q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachNative hAttachSpans hAttachBoundary hMinimumNewHeads
      have hPivotReachMass := @Closure.SharedArcPunctureExpansion.separated_mass q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hPunctureLayer := fun k => @Closure.SharedArcIntervalPuncture.deficient_layer q _ k dualSource
        (by omega : 2≤q) hDualSmaller
      have hNoCyclicPuncture := fun k => @Closure.SharedArcIntervalPuncture.cyclic_puncture_false q _ k dualSource
        (by omega : 2≤q) hDualSmaller
      have hPunctureReachExit := fun k => @Closure.SharedArcProductReach.excludes q _ k dualSource
        (by omega : 2≤q) hDualSmaller
      have hProductPunctureExit := fun k d (hThree : 3≤q) => @Closure.SharedArcProductReach.lex_excludes.{0,0} q _ k d
        dualSource hThree hDualSmaller
      have hPivotSumExit := @Closure.SharedArcPivotLoopSums.progress q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
      have hPivotStoppedRectangle := @Closure.SharedArcPivotChoice.stopped_rectangle q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotFlatPaymentFails := @Closure.SharedArcPivotFold.original_payment_fails q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotFoldSupplier := @Closure.SharedArcPivotFold.bank_escape q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotCoverMasks := fun (three : 3≤q) => @Closure.SharedArcPivotSpread.masks q _ dualSource three
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotCleanParent := fun (three : 3≤q) => @Closure.SharedArcPivotGate.clean_parent_only q _ dualSource three
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hGateClosedPayment := fun (three : 3≤q) => @Closure.SharedArcPivotGate.paid_of_closed q _ dualSource three
      have hPivotRectangleChild := @Closure.SharedArcPivotGate.rectangle_child q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotEveryPair := fun (three : 3≤q) => @Closure.SharedArcPivotSpread.every_pair q _ dualSource three
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotWholeSide := fun (three : 3≤q) => @Closure.SharedArcPivotSpread.whole_side q _ dualSource three
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      have hPivotDegreeCaps := fun k (three : 3≤q) => @Closure.SharedArcPivotDetour.capped_false q _ k dualSource three
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
      have hNoRegularPivot := fun k (three : 3≤q) => @Closure.SharedArcPivotDetour.regular_false q _ k dualSource three
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
      have hStoppedCommonBank := @Closure.RankedMerge.stopped_bank q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachNative hAttachSpans hAttachBoundary hMinimumNewHeads
      have hStoppedTwoPrices := @Closure.RankedMerge.two_banks q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      have hPivotMinimumExit := @Closure.SharedArcPivotChoice.minimum_test q _ dualSource (by omega : 2≤q)
        hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
      have hRecursiveExit := Closure.SharedArcPivot.blocks dualSource hDualSmaller hAttachBoundary
        (fun M bm => (hEveryAttachment M bm).1) hTensorProgress
      have hBudgetExit := Closure.SharedArcFlatBudget.blocks dualSource (by omega : 2≤q) hDualSmaller hRecursiveExit
      have hGateExit := Closure.SharedArcPivotGate.blocks dualSource (by omega : 2≤q) hDualSmaller hBudgetExit
      have hTriangleIntervalExcluded := fun (three : q=3) =>
        @Closure.SingleArcNeighbourWitness.excluded q _ dualSource three attachFamily outsideCycle
          hAttachBoundary hAttachSmall (fun M bm => (hEveryAttachment M bm).1) _ _ _ hGateExit
      have hAffordableReturnBarrier := Closure.SharedArcAffordablePaths.separator dualSource
        (by omega : 2≤q) hAttachDual (fun B b => (hEveryAttachment B b).1)
      obtain ⟨turnTail,hTurnTail,turnPivot,hTurnPivot,turnHead,hTurnHead,hTurnOld,hTurnNew,
          hTurnIn,hTurnOut,hTurnMissing,hTurnExactReturn,hTurnAllPrices⟩ :=
        Closure.SharedArcAffordablePaths.boundary_turn dualSource (by omega : 2≤q)
          hAttachBoundary hAttachSmall (fun B b => (hEveryAttachment B b).1)
      have hTurnCycle : ShenCycleSuccessor.Cycle dualSource.D dualSource.V q outsideCycle := by
        classical exact (Finset.mem_filter.mp hAttachBoundary.1).2
      have hNativeTurnReturns := @Closure.ForwardMerge.arc_returns q _ _ (by omega : 2≤q)
        dualSource.free hDualSmaller (fun v => (dualSource.weights v : ℚ))
        (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
        ⟨turnTail,hTurnCycle.sub hTurnTail⟩
        ⟨turnPivot,hTurnCycle.sub hTurnPivot⟩ hTurnIn
      have hCleanInduction := Closure.SharedArcCleanRecurrence.wellFounded dualSource (by omega : 2≤q)
      have hCleanStoppedFrontier := @Closure.SharedArcCleanRecurrence.priced_frontier q _ dualSource (by omega : 2≤q) hDualSmaller
        leftPortCycle attachFamily outsideCycle hAttachBuilt hAttachNative hAttachStart hAttachSpans hAttachSmall
        hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      obtain ⟨cleanTerminal,hCleanReach,hCleanHeadReturns⟩ :=
        Closure.SharedArcCleanRecurrence.terminal_from dualSource (by omega : 2≤q) ⟨turnPivot,hTurnCycle.sub hTurnPivot⟩
      have hTerminalReturnLayers := Closure.StrictReturnLayers.covers
        (D:=dualSource.D) (w:=fun v => (dualSource.weights v : ℚ))
        (by omega : 2≤q) hDualSmaller dualSource.free
        (Finset.singleton_subset_iff.mpr cleanTerminal.property) (Finset.singleton_nonempty cleanTerminal.val)
        (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
      have hTerminalReturnCharge := fun (receiver : Nat) => Closure.StrictReturnLayers.bank_bound (a:=receiver)
        (D:=dualSource.D) (w:=fun v => (dualSource.weights v : ℚ))
        (by omega : 2≤q) hDualSmaller dualSource.free
        (Finset.singleton_subset_iff.mpr cleanTerminal.property) (Finset.singleton_nonempty cleanTerminal.val)
        (fun v _ => Nat.cast_nonneg (dualSource.weights v)) dualSource.strict
      have hPricedReturnBank := @Closure.StrictReturnLayers.paired q _ dualSource
        (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
        (fun M bm => (hEveryAttachment M bm).1)
      have hPairedReturnCuts := fun (three : 3≤q) => @Closure.StrictReturnLayers.paired_cuts q _ dualSource
        three hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
        (fun M bm => (hEveryAttachment M bm).1)
      have hTurnCycleSwitch := Closure.SharedArcCleanRecurrence.cycle_switches dualSource (by omega : 2≤q) hTurnCycle
      have hCleanTerminalPair := fun (three : 3≤q) =>
        Closure.SharedArcCleanRecurrence.terminal_pair dualSource three cleanTerminal (fun a ta => by
          obtain ⟨z,zm,tz,az,_⟩ := hCleanHeadReturns a ta
          exact ⟨z,zm,tz,az⟩)
      have hAllAttachmentGaps {B} (b : Closure.SharedArcBarrier.Boundary dualSource attachFamily B) :=
        Closure.SharedArcBudget.gap dualSource (by omega : 2≤q) hDualSmaller hAttachNative hAttachSpans b hAttachSmall ((hEveryAttachment B b).1)
      obtain ⟨attachWeights,attachValue,hAttachHigh,hAttachMass,hAttachPositive,hAttachRows,
          hChangedPositive,hChangedProper,hChangedMassFloor,hAttachGap⟩ := hAllAttachmentGaps hAttachBoundary
      obtain ⟨hEachChangedMass,hTotalChangedMass⟩ :=
        Closure.SharedArcMinimalPacket.mass_floor dualSource (by omega : 2≤q) hDualSmaller hAttachSmall
          hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1) hAttachNative hAttachSpans
          hAttachMass hAttachPositive hAttachRows
      obtain ⟨debitTail,hDebitTail,debitHead,hDebitHead,hDebitArc,hDebitNew,hDebitStrict,hDebitBudget⟩ :=
        hAttachGap attachDual hAttachDual
      have hCyclePortRectangle := Closure.FiniteHorizonHall.rectangle_on_source
        (by omega : 2≤q) hDualFree hDualSmaller hDualHigh hDualXPos hDualPPos
        hDualXMass hDualPMass hDualRows hDualColumns (fun M => (hCompleteFamily M).2)
      have hPunctureParentFlow := Closure.PunctureParentFlow.laws hDualFree hDualSmaller hDualSize
        hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
      have hParentSetCapacity := Closure.PunctureFlowCapstone.parent_sets hDualFree hDualSmaller hDualSize
        hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
      have hPunctureAbsorption := Closure.PunctureFlowCapstone.absorption_on_source hDualFree hDualSmaller
        hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
      have hOpposedExteriorCapacity {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) (ne : A≠M) :=
        Closure.OpposedExteriorCapacity.paired dualSource (by omega : 2≤q) hDualSmaller hDualSub ha hm ne
          hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
      have hCoupledArcTrajectory := Closure.CoupledArcTrajectory.on_family dualSource (by omega : 2≤q)
        hDualSmaller hDualSub hDualCard hDualXPos hDualXMass hDualHigh hDualRows hDualPMass hDualColumns
      have hPaidArcTrajectory := Closure.PaidArcTrajectory.exists_paid dualSource (by omega : 2≤q)
        hDualSmaller hDualSub hDualCard hDualXPos hDualXMass hDualHigh hDualRows
      have hResidualRepairOrbit := Closure.ResidualRepairOrbit.on_family dualSource (by omega : 2≤q)
        hDualSmaller hDualSub hDualCard hDualXPos hDualXMass hDualHigh hDualRows
      have hChargedLabelOrbit := Closure.ChargedLabelOrbit.exists_charged dualSource hDualSmaller
        hDualSub hDualCard (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
      have hRecurrentRecipient := Closure.RecurrentRecipient.orbit dualSource (by omega : 2≤q)
        hDualSmaller hDualSub hDualCard (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
      have hOpposedPairPrices {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) (ne : A≠M) :=
        Closure.OpposedPairPrices.opposed dualSource hDualSmaller hDualSub ha hm ne
          (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
      have hUniformPairingLaw {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) (ne : A≠M) :=
        Closure.PairingPressure.on_family dualSource hDualSmaller hDualSub ha hm ne
          (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
      have hDualAtomTransfer := @Closure.EqualizerTransfer.classify q _ _ dualX dualValue (by omega) hDualFree
        hDualSmaller (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
      have hDualParentBalance := @Closure.RecipientBalance.balance q _ _ dualP dualValue hDualColumns
      have hDualSurvivingParent := @Closure.RecipientBalance.surviving_parent q _ _ dualP dualValue
        (fun i hi => (hDualPPos i hi).le) hDualColumns
      have hDualCycle {A} (ha : A∈dualFamily) :
          ShenCycleSuccessor.Cycle (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V q A := by
        classical
        exact Closure.FirstPacketBarrier.retain_cycle (Finset.mem_filter.mp (hDualSub ha)).2 ha
      have hCompleteOverlapTransition {A B} (ag : A∈dualFamily) (bg : B∈dualFamily) (ne : A≠B) :=
        Closure.FlatOverlapDescent.transition (by omega : 2≤q) hDualFree hDualSmaller
          ((hCompleteFamily A).mp ag) ((hCompleteFamily B).mp bg) ne
      have hShortSplitEscape {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) {u y r z m}
          (ua : u∈A) (um : u∈M) (ya : y∈A) (rm : r∈M) (za : z∈A) (zm : z∈M)
          (ne : y≠r) (uy : Closure.FirstPacketBarrier.graph dualSource.D dualFamily u y=true)
          (ur : Closure.FirstPacketBarrier.graph dualSource.D dualFamily u r=true)
          (left : Walk (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) A y z m)
          (right : Walk (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) M r z m) :=
        Closure.ShortSplitExterior.alternatives (by omega : 2≤q) hDualFree hDualSmaller
          (hDualCycle ha) (hDualCycle hm) ua um ya rm za zm ne uy ur left right
          (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
      have hDualFanDistance {A} (ha : A∈dualFamily) (v u t : ℕ) := @Closure.CycleFanDistance.bound _ _ A q
        v u t (by omega) hDualFree
        (hDualCycle ha)
      have hMarkedReceiver := Closure.MarkedSquareFrontier.receiver weightedSource (by omega : 2≤q)
      have hMarkedLoop := @Closure.MarkedSquareFrontier.from_cycle q n weightedSource (by omega : 2≤q)
      have hFullOrbitEscape := @Closure.AllCutoffPacketEscape.from_loop q n weightedSource (by omega : 2≤q)
      have hPunctureSeed := @Closure.PuncturedDistance.minimum_seed q n weightedSource (by omega : 2≤q)
      have hTriangleMiddle := @Closure.PunctureReceiverFrontier.triangle_middle q n weightedSource (by omega : 2≤q)
      have hReceiverFrontier := @Closure.PunctureReceiverFrontier.classify q n weightedSource (by omega : 2≤q)
      have hUpstreamBall := @Closure.MandatoryTwoStep.ball_covered q n weightedSource (by omega : 2≤q)
      have hPuncturedOrbit := @Closure.TwoSidedPuncture.orbit_destination q n weightedSource (by omega : 2≤q)
      have hColumnOrbitBound := @Closure.ComparableColumnCut.orbit_bound q n weightedSource (by omega : 2≤q)
      have hColumnBlockingParent := @Closure.ComparableColumnCut.blocking_parent q n weightedSource (by omega : 2≤q)
      have hLightColumnMass := @Closure.LightColumnPacking.chain_mass q n weightedSource (by omega : 2≤q)
      have hTwoCycleDeletion := @Closure.ShortestReturnCertificate.on_model q n weightedSource (by omega : 2≤q)
      have hJointBlockingParents := @Closure.JointBlockerCycle.paid_pair_on_cycle q n weightedSource (by omega : 2≤q)
      have hConsecutiveHeadPool := @Closure.ConsecutiveBlockerPool.consecutive_pool q n weightedSource (by omega : 2≤q)
      have hPivotPotential := @Closure.BlockerHeadRouting.concentration_at q n weightedSource (by omega : 2≤q)
      have hMinimumPairEscape := @Closure.MinimumPairEscape.all_heads q n weightedSource (by omega : 2≤q)
      have hClassStep := @Closure.PairEscapeTransition.transition q n weightedSource (by omega : 2≤q)
      have hPersistentClass := @Closure.ClassPunctureRecurrence.persistent q n weightedSource (by omega : 2≤q)
      have hMarkedBarrier := @Closure.FirstPacketBarrier.first q n weightedSource (by omega : 2≤q)
      obtain ⟨packetFamily,hPacketSub,hPacketCard,hPacketFeasible,hPacketMinimal,hPacketEndpoints⟩ :=
        Closure.JointCycleFamilyBarrier.joint weightedSource (by omega : 2≤q)
      obtain ⟨packetWeight,hPacketEligible,hPacketLeastMass,hPacketBarrierRows⟩ :=
        Closure.CycleWithdrawal.simultaneous weightedSource hPacketSub hPacketFeasible
      obtain ⟨hPacketPositive,hPacketBudget,hPacketStrict⟩ := id hPacketEligible
      have hNativePaidFork := Closure.NativePaidHeadFork.alternatives weightedSource (by omega : 2≤q) hPacketSub hPacketBarrierRows
      have hUnitCycleFork := @Closure.NativePaidHeadFork.unit_cycle q n weightedSource (by omega : 2≤q)
      have hPacketOrbit {M A} (hm : M∈packetFamily) (ha : A∈packetFamily) (hne : M≠A) := Closure.PaidCycleFamilyOrbit.orbit weightedSource hPacketSub hPacketPositive hPacketBudget hPacketStrict hm ha hne
      have hPacketExit := hPacketEndpoints packetWeight hPacketPositive hPacketBudget hPacketStrict
      have hPacketOrbitBill := @Closure.PaidCycleFamilyOrbit.orbit_bill q n weightedSource packetFamily packetWeight hPacketSub hPacketStrict
      have hPacketNextCharge {A M L} (ha : A∈packetFamily) (h : Closure.JointCycleFamilyBarrier.ExitTo weightedSource packetFamily packetWeight A M L) := Closure.PaidCycleFamilyOrbit.next_charge weightedSource hPacketSub ha h
      have hPacketHeadChoices {A M} (ha : A∈packetFamily) (hm : M∈packetFamily) (hne : A≠M) := Closure.TransferHeadChoices.choices weightedSource hPacketSub hPacketPositive hPacketBudget hPacketStrict ha hm hne
      have hPacketRecurrentClass := @Closure.TransferHeadChoices.recurrent_class q n weightedSource packetFamily
      have hPacketUncompensated {A M} (ha : A∈packetFamily) (hm : M∈packetFamily) (hne : A≠M) := Closure.TransferHeadChoices.uncompensated weightedSource hPacketSub hPacketPositive hPacketBudget hPacketStrict ha hm hne
      have hPacketPhaseFork {C} (hc : C∈packetFamily) := Closure.CyclePhaseFork.forced weightedSource (by omega : 2≤q) hPacketSub ⟨packetWeight,hPacketPositive,hPacketBudget,hPacketStrict⟩ hc
      have hWeightedSupportBound := Closure.CyclePhaseFork.support_bound weightedSource (by omega : 2≤q)
      have hPacketHeadCapacity {A} (ha : A∈packetFamily) (p : ℕ) := Closure.CyclePhaseFork.head_capacity weightedSource (by omega : 2≤q) hPacketSub ha p
      have hMateWeight := @Closure.PairWithdrawal.equal_mate_weight q n weightedSource (by omega : 2≤q)
      have hPartialWithdrawal := @Closure.PairWithdrawal.minimum_bill q n weightedSource (by omega : 2≤q)
      have hShortestShift {W} (sub : W ⊆ weightedSource.V) :=
        @Closure.AnchoredShiftFlow.least_period weightedSource.D W q (by omega) (weightedSource.free.mono_set sub)
      have hShortestCrossing {W} (sub : W ⊆ weightedSource.V) :=
        @Closure.AnchoredShiftFlow.short_loop_crossing weightedSource.D W q (by omega) (weightedSource.free.mono_set sub)
      have hExteriorColumn {W} (sub : W ⊆ weightedSource.V) :=
        Closure.AnchoredExteriorColumn.short_loop_escape weightedSource (by omega) sub
      -- OPEN_FOURTH_STRIP_TOP: n = q*s for 7 ≤ s ≤ 11, and n = q*s-1 only at s = 7
      -- (rigid, see hStripRigidity/hcapped).
      obtain ⟨repairBasis,hRepairBasis,repairGo,repairSend,repairExterior,repairRaw,hRepairMark,
        hRepairChild,hAdjacentReplacement,hRepairMotion,hRawFrontier,hRepairProbs,hPaidWitness⟩ :=
        id hCoupledArcTrajectory
      obtain ⟨paidOccurrence,paidPeriod,paidRow,hPaidRow,hPaidPeriod,hPaidReturn,hPaidArcBill,hRise,hFall⟩ :=
        id hPaidWitness
      obtain ⟨slackLabel,hSlackLabelIn,hSlackLabelStrict⟩ :=
        hForcedPairSlack (repairRaw slackSeed) (hRepairChild slackSeed).1
      have hSeedMargin := Closure.SlackPairOrbit.margin (hRepairChild slackSeed).1 hSlackLabelIn hSlackLabelStrict
      have hSeedOrbit := Closure.SlackPairOrbit.from_seed repairGo repairRaw (fun s => (hRepairChild s).1)
        slackSeed hForcedPairSlack
      rcases (id hRawFrontier) with ⟨hEveryChildFlat,hConstantOmissionSize⟩ |
        ⟨rawOccurrence,rawPeriod,⟨rawColumn,hRawColumnRetained,hRawColumnSlack⟩,hRawPeriod,hRawReturn,hPositiveRawDebit⟩
      case' inl =>
        obtain ⟨hSeedTransient,slackSteps,hSeedSlackPrefix,hFirstFlatChild⟩ :=
          hSeedOrbit.resolve_left (by
            rintro ⟨i,per,z,zu,below⟩
            exact below.ne (((hEveryChildFlat ⟨_,per⟩).2 z zu).2))
        have hFirstFlatContact := Closure.SlackBoundaryBanks.on_child (by omega : 2≤q) hDualFree hDualSmaller
          (fun _ => hDualCycle) (fun s => (hRepairChild s).1) hFirstFlatChild
        have hFirstFlatMap := Closure.SlackPairOrbit.on_edge (by omega : 2≤q) hDualFree hDualSmaller
          (fun _ => hDualCycle) (fun s => (hRepairChild s).1) (hSeedSlackPrefix slackSteps le_rfl) hFirstFlatChild
        obtain ⟨repairRowLaw,hFlatRowLaw,hFlatOmittedPayments,hFlatCrossPayments,hFlatRelabel,hFlatBlockExchange⟩ :=
          Closure.FlatChildExchange.on_family (by omega : 2≤q) hDualFree hDualSmaller
            (fun a : Function.periodicPts repairGo => dualSource.V \ Closure.RawRepairAlternative.gone a.val)
            (fun a => repairRaw a.val) (fun _ => Finset.sdiff_subset)
            (fun a => (hRepairChild a.val).1.normalized) (fun a => (hEveryChildFlat a).2)
            (x:=fun i => (dualX i : ℝ)) (t:=fun i => (dualP i : ℝ)) (c:=(dualValue : ℝ))
            (by exact_mod_cast hDualHigh)
            (fun i hi => by exact_mod_cast (hDualXPos i hi).le)
            (by rw [WeightedSD.realMass_rat,hDualXMass]; norm_num)
            (by rw [WeightedSD.realMass_rat,hDualPMass]; norm_num)
            (fun i hi => by rw [WeightedSD.realRow_rat,hDualRows i hi])
            (fun i hi => by rw [WeightedSD.realCol_rat,hDualColumns i hi])
        have hFlatAdjacentExchange := Closure.FlatChildExchange.adjacent repairGo (fun a => (hRepairMark a).1)
          (fun a => (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1).sub)
          hConstantOmissionSize hFlatBlockExchange
        have hFlatStep (a : Function.periodicPts repairGo) :=
          fun e fix => Closure.FlatExchangeCycle.step hDualFree hDualSmaller
            (fun i hi => (hDualXPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            a (hRepairMark a.val).1 (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
            e fix ((hFlatAdjacentExchange a).2 e fix)
        have hFlatSize (a : Function.periodicPts repairGo) :
            (dualSource.V \ Closure.RawRepairAlternative.gone a.val).card < dualSource.V.card := by
          apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,?_⟩)
          intro eq
          have pay := (hFlatOmittedPayments a).1
          rw [eq] at pay
          simp at pay
          have high : (1:ℝ)<(dualValue:ℝ) := by exact_mod_cast hDualHigh
          linarith
        have hFlatGeometry (a : Function.periodicPts repairGo) := Closure.FlatExchangeCycle.child_geometry
          (by omega : 2≤q) hDualFree hDualSmaller Finset.sdiff_subset (hFlatSize a) (hRepairChild a.val).1
          (fun i hi => ((hEveryChildFlat a).2 i hi).2) (hFlatRowLaw a).1 (hFlatRowLaw a).2
        have hFlatSourceFrontier := Closure.FlatOrbitSaturation.frontier dualSource (by omega : 1≤q)
          repairGo (fun a => (hRepairMark a).1) (fun a => (hFlatGeometry a).1)
        have hFlatNativeCut (a : Function.periodicPts repairGo) {u v} (uv : u∈dualSource.V) (vv : v∈dualSource.V) :=
          Closure.FlatOrbitSaturation.phase_cut dualSource (by omega : 1≤q) repairGo
            (fun s => (hRepairMark s).1) (fun s => (hFlatGeometry s).1) a uv vv
        have hFlatStableLabel (a : Function.periodicPts repairGo) {u} (uv : u∈dualSource.V) :=
          Closure.FlatOrbitSaturation.stable_label dualSource (by omega : 1≤q) repairGo
            (fun s => (hRepairMark s).1) (fun s => (hFlatGeometry s).1) a uv
        have hFlatOddSource (a : Function.periodicPts repairGo) (odd : ¬Even (Function.minimalPeriod repairGo a.val)) :=
          Closure.FlatOrbitSaturation.odd_saturated repairGo (fun s => (hRepairMark s).1)
            (fun s => (hFlatGeometry s).1) a odd
        have hFlatNativeExtensions (a : Function.periodicPts repairGo) {u v}
            (uv : u∈dualSource.V \ Closure.RawRepairAlternative.gone a.val)
            (vv : v∈dualSource.V \ Closure.RawRepairAlternative.gone a.val) :=
          Closure.FlatOrbitSaturation.native_extensions dualSource (by omega : 2≤q) Finset.sdiff_subset
            (hFlatGeometry a).1 (fun i hi => ((hFlatRowLaw a).2 i hi).1)
            (fun i hi => ((hFlatRowLaw a).2 i hi).2) uv vv
        have hFlatConfined (a b : Function.periodicPts repairGo) :=
          Closure.FlatExchangeCycle.confined (by omega : 2≤q) hDualFree (hFlatGeometry a).1
            Finset.sdiff_subset (Finset.sdiff_subset : dualSource.V \ Closure.RawRepairAlternative.gone b.val ⊆ dualSource.V)
        have hFlatOrderedStep (a : Function.periodicPts repairGo) :=
          fun e fix => Closure.FlatExchangeChain.on_mark (by omega : 2≤q) hDualFree hDualSmaller
            (fun i hi => (hDualXPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).1).sub
            (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).2)
            (hRepairMark a.val) (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
            (hFlatGeometry a).1 (hFlatGeometry (Closure.CycleSlotOrbit.base repairGo a)).1 e fix
            ((hFlatAdjacentExchange a).2 e fix)
        have hFlatOffset (a : Function.periodicPts repairGo) :=
          fun e fix => Closure.FlatExchangeTriangle.offset_on_mark (by omega : 2≤q) hDualFree hDualSmaller
            (fun i hi => (hDualXPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).1)
            (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).2)
            (hRepairMark a.val) (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
            (hFlatGeometry a).1 (hFlatGeometry (Closure.CycleSlotOrbit.base repairGo a)).1 e fix
            ((hFlatAdjacentExchange a).2 e fix)
        have hFlatPacket (a : Function.periodicPts repairGo) :=
          fun e fix => Closure.FlatExchangeTriangle.packet_on_mark (by omega : 2≤q) hDualFree hDualSmaller
            (fun i hi => (hDualXPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).1)
            (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).2)
            (hRepairMark a.val) (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
            (hFlatGeometry a).1 (hFlatGeometry (Closure.CycleSlotOrbit.base repairGo a)).1 e fix
            ((hFlatAdjacentExchange a).2 e fix)
        have hFlatOtherCycle (s : Closure.PairedFamilyLoop.State dualFamily) {N} (nf : N∈dualFamily) :=
          fun packet => Closure.FlatPairedExcursion.packet_overlap
            (B:=Closure.PairedFamilyLoop.current s) (C:=Closure.PairedFamilyLoop.current (repairGo s))
            hDualFree (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).1) packet (hDualCycle nf)
        have hFlatOutsideFamily (a : Function.periodicPts repairGo) :=
          Closure.FlatPairedExcursion.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
            hDualXPos (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh) repairGo
            (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
            a.val (hEveryChildFlat a).1
        have hFlatRecursiveCut := Closure.FlatReturnLayers.on_schedule (by omega : 1≤q) hDualFree repairGo
          (fun s => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).1)
          (fun s => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).2)
          (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
        have hFlatExteriorOrder (a : Function.periodicPts repairGo) :=
          Closure.FlatMinimumExterior.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
            repairGo (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
            (fun s => (hFlatGeometry s).1) hDualXPos (fun i hi => (hDualPPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            (fun i hi => by rw [hDualPMass,hDualColumns i hi]; exact hDualHigh)
            a (hEveryChildFlat a).1
        have hFlatLongCycle (a : Function.periodicPts repairGo) :=
          Closure.FlatTightTraffic.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
            repairGo (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
            (fun s => (hFlatGeometry s).1) hDualXPos (fun i hi => (hDualPPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            (fun i hi => by rw [hDualPMass,hDualColumns i hi]; exact hDualHigh)
            a (hEveryChildFlat a).1
        have hFlatTransientReturn (a : Function.periodicPts repairGo) :=
          Closure.FlatTransientReturn.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
            repairGo (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
            (fun s => (hFlatGeometry s).1) hDualXPos (fun i hi => (hDualPPos i hi).le)
            (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
            (fun i hi => by rw [hDualPMass,hDualColumns i hi]; exact hDualHigh)
            repairRaw (fun s => (hRepairChild s).1) (fun s z hz => ((hEveryChildFlat s).2 z hz).2)
            a (hEveryChildFlat a).1
        have hFlatThreeStep := Closure.FlatExchangeTriangle.period_three hDualFree repairGo
          (fun a => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1)
          (fun a => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).2)
          (fun a => (hRepairMark a).1) (fun a => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark a))
      all_goals apply (not_or.mpr ⟨hGateExit,not_or.mpr ⟨hForwardNoMerge,hNoPair⟩⟩)
      all_goals replay_ch_families
      all_goals check_ch_exits hnoCycle
      }
    have hbelowFourth : q≤2*s-7 := cutoffReduction.upper
    by_cases hfifthClosed : 59≤s ∧ q=2*s-7
    · by_contra no
      exact registeredExclusion no .fifthFull hfifthClosed
    have hremainingCutoff : 59≤s → q≤2*s-8 := by
      clear * - hfifthClosed hbelowFourth
      omega
    by_cases hsixthClosed : 8192≤s ∧ q=2*s-8
    · by_contra no
      exact registeredExclusion no .sixthFull hsixthClosed
    have hsixthRemaining : 8192≤s → q≤2*s-9 := by
      clear * - hfifthClosed hbelowFourth hsixthClosed
      omega
    let gap := 2*s-q
    have hgap : q+gap=2*s := by
      dsimp [gap]
      clear * - hbelowFourth hq3
      omega
    have hgapPos : 1≤gap := by
      clear * - hgap hbelowFourth hq3
      omega
    by_cases hwindow : 35840*(gap+1)^2≤s
    · by_contra no
      exact registeredExclusion no .cumulative ⟨gap,hgap,by omega,hwindow⟩
    have hremainingScale : s<35840*(gap+1)^2 := Nat.lt_of_not_ge hwindow
    have hceilSlack : q*s<n+s := by
      have h := Nat.div_mul_le_self (n+s-1) s
      change q*s≤n+s-1 at h
      omega
    by_cases hbulk : n+3*gap*gap≤q*s
    · have hsGap : 3*gap≤s := by
        have prod := Nat.mul_le_mul_left (3*gap) hgapPos
        clear * - hbulk hceilSlack prod
        omega
      by_contra no
      exact registeredExclusion no .variableWindow ⟨gap,hgap,hgapPos,hsGap,hbulk⟩
    have hremainingGap : q*s<n+3*gap*gap := Nat.lt_of_not_ge hbulk
    by_cases hpaid : 64*(gap*gap)≤s ∧ n+((gap+3)/4)*gap≤q*s
    · by_contra no
      exact registeredExclusion no .paidWindow ⟨gap,hgap,by omega,hpaid⟩
    have hremainingPaid : 64*(gap*gap)≤s → q*s<n+((gap+3)/4)*gap := fun bound =>
      Nat.lt_of_not_ge (fun covers => hpaid ⟨bound,covers⟩)
    by_cases hfifthLow : 7≤s ∧ q=2*s-7 ∧ n+4≤q*s
    · by_contra no
      exact registeredExclusion no .fifthLow hfifthLow
    have hfifthRemaining : 7≤s → q=2*s-7 → q*s≤n+3 := by
      clear * - hfifthLow
      omega
    by_cases hfifthHigher : 21≤s ∧ q=2*s-7 ∧ n+3≤q*s
    · by_contra no
      exact registeredExclusion no .fifthHigher hfifthHigher
    have hfifthHigherRemaining : 21≤s → q=2*s-7 → q*s≤n+2 := by
      clear * - hfifthHigher
      omega
    by_cases hfifthTensor : 32≤s ∧ q=2*s-7 ∧ n+2≤q*s
    · by_contra no
      exact registeredExclusion no .fifthTensor hfifthTensor
    have hfifthTensorRemaining : 32≤s → q=2*s-7 → q*s≤n+1 := by
      clear * - hfifthTensor
      omega
    -- hremainingGap bounds the order deficit simultaneously at every remaining cutoff.
    by_contra hnoCycle
    have hfree := qfree_of_noShort hloop hnoCycle
    have hBlockedTightBank (triangle : q=3) :=
      ShenPuncture.FiveParent.least_degree_source
        (show QFree D (Finset.range n) 3 by simpa only [triangle] using hfree)
        ⟨0,Finset.mem_range.mpr hn⟩
        (show (Finset.range n).card ≤ 3*s by simpa only [Finset.card_range,triangle] using hcover)
        hminDegree
    obtain ⟨primeSupport,hminMass,hrigid,hprimeFree,hprimeSize,hprimeSizeFour,hprimeNonCircular,
      hphaseHoles⟩ := hprimeWitness hnoCycle
    have hparentTest := @ShenParentIntersection.distinguishing_parent _ _ _ _ primeSupport hrigid
    have hPrimeColumnExit (three : q=3) :
        ∃ v ∈ primeSupport.carrier, Closure.ColumnBlockerEscape.Unmatched D primeSupport.carrier v := by
      by_contra none
      have cols (v) (hv : v∈primeSupport.carrier) :
          ∃ b∈primeSupport.carrier, outN D primeSupport.carrier b=inN D primeSupport.carrier v := by
        by_contra no
        exact none ⟨v,hv,fun b hb eq => no ⟨b,hb,eq⟩⟩
      exact Closure.WeightedColumnEscape.no_strict (hprimeFree.mono_bound hq3)
        primeSupport.nonempty cols primeSupport.weights (three ▸ primeSupport.strict)
    have hWeightedSecondTransport := ShenSecondNeighbour.minimal_transport hminMass
      (by omega : 1 ≤ q) hprimeFree
    have hCyclicUnitPacking (triangle : q=3) :=
      ShenUnitRowPacking.source_with_packing
        (show QFree D (Finset.range n) 3 by simpa only [triangle] using hfree)
        ⟨0,Finset.mem_range.mpr hn⟩
        (show (Finset.range n).card ≤ 3*s by simpa only [Finset.card_range,triangle] using hcover)
        hminDegree
    have hpacketTest := @ShenParentIntersection.packet_deficit _ _ _ _ primeSupport hrigid
    obtain ⟨rootKernel,rootKernelSpec⟩ := ShenRootedKernel.kernel_family primeSupport.weights
      (fun x hx => loopfree hprimeFree (by omega) hx)
    have hkernelMargin := ShenRootedKernel.margin_bill (by omega : 2≤q) hprimeFree primeSupport.strict rootKernelSpec
    have hkernelExit (x) (hx : x∈primeSupport.carrier) :=
      ShenRootedKernel.boundary_omissions hminMass (by omega) hprimeFree (rootKernelSpec x hx)
    have hpairedPaths := @ShenParentIntersection.paired_itinerary _ _ _ _ primeSupport hrigid
    have hcompatible := ShenParentIntersection.compatible_all_rounds hrigid
    have hlayerHoles := ShenCenterTable.layer_holes (by omega : 2≤q) hfree hminDegree
    have htransversalSquare (m : ℕ) (hm : m+1≤q) (h3 : 3≤m+1) (layer : ℕ → Fin (m+1)) :=
      ShenTransversal.square_bound (by omega : 0<q) hfree
        (show Fintype.card (Fin (m+1))≤q by simpa using hm)
        (show 3≤Fintype.card (Fin (m+1)) by simpa using h3) hminDegree hs layer
    have hweightedTable (P : ShenCenterTable.Table q primeSupport.carrier) :=
      ShenCenterTable.two_missing_weighted (by omega) hprimeFree P primeSupport.strict
    have hpaidDonor (P : ShenCenterTable.Table q (Finset.range n)) (p : ℕ) :=
      ShenCenterTable.pinned_donor (p:=p) (by omega) hfree P (fun i hi => hminDegree _ (P.mem i hi))
    have hprimeOdd := ShenPrimeTransition.odd_heads hminMass
    have hprimeOpposite := ShenPrimeTransition.opposite_parity_rows hminMass
    have hprimeColors := ShenPrimeTransition.two_color_rows hminMass
    have hprimeResidue := @ShenPrimeTransition.remainder_row _ _ _ _ primeSupport hminMass
    have htransitionFrontier (h3 : q=3) := ShenTransitions.triangle_frontier hn hs
      (show n≤3*s by rwa [h3] at hcover) hloop hdegree
      (show ¬CH.HasDirectedCycleAtMost D n 3 by rwa [h3] at hnoCycle)
    have hinputPath (h3 : q=3) (k : ℕ) (price : (k-2)*(k-3)<2*s*(3*s+1-n)) :
        ShenTransitions.PathInCommonHeads D (Finset.range n) k := by
      obtain ⟨F,sub,_,reach⟩ := htransitionFrontier h3
      exact ShenTransitions.fan_to_input sub (reach k price).2.2
    have hlargeArc (h3 : q=3) : ∃ u∈Finset.range n,∃ v∈outN D (Finset.range n) u,
        (s+1)/2<(ShenSharedHead.commonOut D (Finset.range n) u v).card := by
      rw [h3] at hcover hnoCycle
      exact ShenSharedHead.large_arc_of_survival hn hs hcover hloop hdegree hnoCycle
    obtain ⟨source,horder,hCycleRegular,seed,hSeed,hCycleReach⟩ := hcycleSource hnoCycle
    rw [Finset.card_range] at horder
    obtain ⟨jointBank,hJointMarked,hJointShort,hSelectedParentOrder⟩ :=
      BypassBankReplay.exists_ordered_joint_mark source hCycleRegular hq3
        ((by decide : 4≤6).trans hdegreeSix) (horder.trans hcover) hNoLowerQuotaHost
    have hSeedSuccessors := ShenCycleSuccessor.successors source (by omega) hs (horder.trans hcover) hSeed
    have hPaymentImpossible {M x} (C : ShenCycleSuccessor.Cycle source.D source.V q M)
        (hx : x ∈ M) (p : ShenCycleSuccessor.Payment source M x) : False :=
      (horder.trans hcover).not_gt (ShenCycleSuccessor.order_of_payment source (by omega) hs hCycleRegular C hx p)
    obtain ⟨weightedSource, hWeightedSource⟩ := hPunctureModel hnoCycle
    obtain ⟨dualBudget,dualSource,hDualSupportSize,hDualSmaller⟩ :=
      Closure.GlobalFamilyDual.select weightedSource (by omega : 2≤q)
    have hNativeSeedLanes := Closure.TwoHeadRepairLanes.native dualSource (by omega : 3≤q) hDualSmaller
    obtain ⟨seedW,seedC,hSeedMass,hSeedStrict,hSeedPos,hSeedRows,hSeedFrontier⟩ :=
      Closure.TwoHeadRepairReplay.on_native dualSource (by omega : 3≤q) hNativeSeedLanes
    obtain ⟨selectedFamily,hSelectedSub,hSelectedCard,hSelectedFeasible,hSelectedMinimal,hSelectedEndpoints⟩ :=
      Closure.JointCycleFamilyBarrier.joint dualSource (by omega : 2≤q)
    obtain ⟨dualX,dualP,dualValue,hDualHigh,hDualXPos,hDualPPos,hDualXMass,hDualPMass,hSelectedRows,hSelectedColumns⟩ :=
      Closure.GlobalFamilyDual.on_family dualSource hDualSmaller hSelectedFeasible
    obtain ⟨dualFamily,hSelectedIn,hDualSub,hSameSelectedGraph,hCompleteFamily,slackA,hSlackA,slackB,hSlackB,hSlackDistinct,
        hSlackProper,hSlackRetained,hForcedPairSlack,hPairCertificate⟩ :=
      Closure.UniversalSlackPair.on_source dualSource (by omega : 2≤q) hDualSmaller hSelectedSub hSelectedCard
        (fun i hi => (hDualXPos i hi).le)
        (fun i hi => by rw [hDualXMass,hSelectedRows i hi]; exact hDualHigh)
    rw [←hSameSelectedGraph] at hCompleteFamily hForcedPairSlack hPairCertificate
    have hDualCard := hSelectedCard.trans (Finset.card_le_card hSelectedIn)
    have hDualRows (i) (hi : i∈dualSource.V) :
        WeightedSD.row q (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V dualX i=dualValue :=
      by rw [hSameSelectedGraph]; exact hSelectedRows i hi
    have hDualColumns (i) (hi : i∈dualSource.V) :
        WeightedSD.col q (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V dualP i=dualValue :=
      by rw [hSameSelectedGraph]; exact hSelectedColumns i hi
    let slackSeed : Closure.PairedFamilyLoop.State dualFamily :=
      ⟨(slackA,slackB),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hSlackA,hSlackB⟩,hSlackDistinct⟩⟩
    have hDualFree := Closure.PrivateArcEndpoints.graph_free dualSource dualFamily
    have hForwardRows (j) (jv : j∈dualSource.V) :
        WeightedSD.mass dualSource.V dualX <
          WeightedSD.row q (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V dualX j := by
      rw [hDualXMass,hDualRows j jv]; exact hDualHigh
    have hBackwardRows (j) (jv : j∈dualSource.V) :
        WeightedSD.mass dualSource.V dualP <
          WeightedSD.row q (fun u v => Closure.FirstPacketBarrier.graph dualSource.D dualFamily v u)
            dualSource.V dualP j := by
      change WeightedSD.mass dualSource.V dualP < WeightedSD.col q _ _ _ j
      rw [hDualPMass,hDualColumns j jv]; exact hDualHigh
    have hForwardReach (U : Finset ℕ) (us : U⊆dualSource.V) (k : ℕ) :=
      Closure.FlatPeelReach.exact_rounds (by omega : 2≤q) hDualFree hDualSmaller us
        (fun i iv=>(hDualXPos i iv).le) (by rw [hDualXMass]; exact hDualHigh) hDualRows k
    have hReverseReach (U : Finset ℕ) (us : U⊆dualSource.V) (k : ℕ) :=
      Closure.FlatPeelReach.exact_rounds (by omega : 2≤q) hDualFree.reverse hDualSmaller us
        (fun i iv=>(hDualPPos i iv).le) (by rw [hDualPMass]; exact hDualHigh) hDualColumns k
    have hForwardArcReturns := @Closure.ForwardMerge.arc_returns q _ _ (by omega : 2≤q)
      hDualFree hDualSmaller dualX hDualXPos hForwardRows
    have hBackwardArcReturns := @Closure.ForwardMerge.arc_returns q _ _ (by omega : 2≤q)
      hDualFree.reverse hDualSmaller dualP hDualPPos hBackwardRows
    have hForwardTriangle := fun (three : q=3) => @Closure.ForwardMerge.triangle_at q _ _
      three hDualFree hDualSmaller dualX hDualXPos hForwardRows
    have hBackwardTriangle := fun (three : q=3) => @Closure.ForwardMerge.triangle_at q _ _
      three hDualFree.reverse hDualSmaller dualP hDualPPos hBackwardRows
    have hForwardDecay := fun (U : Finset ℕ) (us : U⊆dualSource.V) (room : U.card+1<dualSource.V.card) =>
      Closure.ForwardMerge.repeated_decay (by omega : 2≤q) hDualFree hDualSmaller us room dualX hDualXPos hForwardRows
    have hBackwardDecay := fun (U : Finset ℕ) (us : U⊆dualSource.V) (room : U.card+1<dualSource.V.card) =>
      Closure.ForwardMerge.repeated_decay (by omega : 2≤q) hDualFree.reverse hDualSmaller us room dualP hDualPPos hBackwardRows
    have hForwardNoMerge := Closure.ForwardMerge.no_native_merge (by omega : 2≤q) dualSource.free hDualSmaller
    have hNoPair := Closure.RankedMerge.no_pair (by omega : 2≤q) dualSource.free hDualSmaller
    have hParentRecursion := @Closure.TwoReceiverIntersection.upstream_corridor q _ dualSource (by omega : 2≤q)
    have hAllNativeCorners := Closure.TwoReceiverIntersection.all_corners (by omega : 2≤q)
      dualSource.free hDualSmaller dualSource.sat (fun v => (dualSource.weights v : ℚ))
      (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
    have hAllReverseCorners := Closure.TwoReceiverIntersection.reversed_family (by omega : 2≤q)
      dualSource.free hDualSmaller dualSource.sat dualP hDualPPos hBackwardRows
    have hNativeIntersection := fun {b a : dualSource.V} (ba : dualSource.D b a=true) =>
      Closure.TwoReceiverIntersection.corridor_cut (by omega : 2≤q) dualSource.free hDualSmaller
        (a:=a) (b:=b) ba dualSource.sat (fun v => (dualSource.weights v : ℚ))
        (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
    have hForwardCovered := @Closure.RankedMerge.covered_sink q _ _ (by omega : 2≤q) hDualFree hDualSmaller
      dualX hDualXPos (dualValue-1) (sub_pos.mpr hDualHigh) (fun i iv => by
        rw [Closure.ForwardMerge.surplus,hDualRows i iv,hDualXMass])
    have hReverseCovered := @Closure.RankedMerge.covered_sink q _ _ (by omega : 2≤q) hDualFree.reverse hDualSmaller
      dualP hDualPPos (dualValue-1) (sub_pos.mpr hDualHigh) (fun i iv => by
        change dualValue-1≤WeightedSD.col q _ _ dualP i-WeightedSD.mass _ dualP
        rw [hDualColumns i iv,hDualPMass])
    obtain ⟨mergeRoot,hMergeRoot,hMinWeight⟩ := dualSource.V.exists_min_image dualSource.weights dualSource.live
    obtain ⟨mergeParent,hMergeLow,hMergeParent,hMergeCover⟩ :=
      Closure.ForwardShortcutLayers.minimum_covers dualSource (by omega : 2≤q) hDualSmaller
        ⟨mergeRoot,hMergeRoot⟩ (fun v => (dualSource.weights v : ℚ))
        (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
        (fun v hv => by exact_mod_cast hMinWeight v hv)
    have hDualSize : 2≤dualSource.V.card := by
      have := Closure.CyclePhaseFork.support_bound dualSource (by omega : 2≤q)
      omega
    obtain ⟨portScale,portBonus,hPortScale,hPortBonus,hBonusValue,portWeights,hPortWeights,hCyclePortMatching⟩ :=
      Closure.CyclePortMatching.on_family (by omega : 2≤q) hDualHigh hDualSmaller hDualFree
        hDualXPos hDualXMass hDualRows (fun M => (hCompleteFamily M).2)
    obtain ⟨portRoot,hPortRoot,⟨portParent,hPortParent⟩,hRootCollisions⟩ :=
      Closure.CyclePortCollision.collision (by omega : 2≤q) hDualHigh hDualFree hDualXPos
        hDualXMass hDualRows hPortScale hPortBonus hPortWeights
    have hParentOffRoot : portParent≠portRoot := by
      rintro rfl
      exact hDualFree portParent 1 (by omega) (by omega)
        (.step hPortRoot (mem_inN.mp hPortParent).2 (.refl _))
    obtain ⟨portRoute,hPortRoute⟩ := hCyclePortMatching portRoot hPortRoot portParent
      (Finset.mem_erase.mpr ⟨hParentOffRoot,(mem_inN.mp hPortParent).1⟩)
    obtain ⟨hLastPhaseCount,hAnyPortCollision⟩ := hRootCollisions portParent hPortParent
    obtain ⟨portLeft,portRight,hDistinctPortSlots,hLeftParent,hRightParent,hSamePortPosition⟩ :=
      hAnyPortCollision portRoute
    obtain ⟨leftPortCycle,hLeftPortCycle,hLeftOnCycle,hRootOnLeft,hHeadOnLeft⟩ :=
      (hPortRoute portLeft).2.2 hLeftParent
    obtain ⟨rightPortCycle,hRightPortCycle,hRightOnCycle,hRootOnRight,hHeadOnRight⟩ :=
      (hPortRoute portRight).2.2 hRightParent
    obtain ⟨hNativePortMiss,hNativePortDistance,hNativeBicliqueBudget⟩ :=
      Closure.CyclePortNative.on_source dualSource (by omega : 2≤q) hDualSmaller hDualHigh
        hDualXPos hDualPPos hDualXMass hDualPMass hDualRows hDualColumns
    let portGraph := Closure.FirstPacketBarrier.graph dualSource.D dualFamily
    let portU := (dualSource.V.erase portRoot).erase portParent
    let portInnerBall := BRsub.ballSet portGraph portU (outN portGraph portU portRoot) (q-2)
    have portLift (u v) (edge : portGraph u v=true) : dualSource.D u v=true := by
      obtain ⟨C,cc⟩ := Closure.FirstPacketBarrier.active.mp edge
      exact (Closure.MarkedCyclePeeling.mem_col.mp cc).2.2.2
    have portTwo := @Closure.CommonParentHeadRepair.two_rows q portGraph dualSource.D dualSource.V dualX
      portLift (fun K ks O os heads two live => by
        rw [hDualXMass]
        exact (hNativeBicliqueBudget K ks O os heads).1 two live)
      ⟨portParent,(mem_inN.mp hPortParent).1⟩
    obtain ⟨portInner,hPortInner,hPortInnerToParent,hPortInnerMiss,hPortInnerLeast,hPortRecursiveRepair⟩ :=
      Closure.CommonParentHeadRepair.live_run (by omega : 3≤q) hDualFree hDualSmaller dualX hDualXPos
        (by rw [hDualXMass]; exact hDualHigh) hDualRows
        (b:=⟨portParent,(mem_inN.mp hPortParent).1⟩) (a:=⟨portRoot,hPortRoot⟩) (mem_inN.mp hPortParent).2 portTwo
    have hPortTerminal (j : ℕ) (ju : j∈portU) (ja : portGraph j portRoot=true)
        (jb : portGraph j portParent=true) (k : ℕ) (kk : k∈outN portGraph portU portInner) :
        ∃T⊆portU,T.card+1=q ∧ Closure.CommonParentHeadRepair.IndependentHeads portGraph portInnerBall T ∧
          k∈T ∧ Closure.CommonParentHeadRepair.IndependentHeads portGraph
            (portInnerBall.filter (fun r=>portGraph r k=false)) (T.erase k) ∧
          ∃v,Relation.ReflTransGen (Closure.CommonParentHeadRepair.Step q portGraph portU
            (outN portGraph portU portRoot)) ({k},dualX) (T,v) ∧
            Closure.CommonParentEndpointReplay.Fork q portGraph dualSource.V portU
              (outN portGraph portU portRoot) portInnerBall T dualX v ∧
              Closure.EndpointPrivateRows.Tests q portGraph portU (outN portGraph portU portRoot) portInnerBall T v := by
      obtain ⟨_,_,budget,_,go⟩ := hPortRecursiveRepair j ju ja jb
      obtain ⟨l,z,T,v,_,_,_,link,path,ts,count⟩ := go k kk
      exact ⟨T,ts,count,Closure.CommonParentHeadRepair.trace_minor hPortInner (mem_outN.mp kk).2 link path,
        (Closure.CommonParentHeadRepair.avoiding_minor link path).1,
        (Closure.CommonParentHeadRepair.avoiding_minor link path).2,v,path.head link,
        Closure.EndpointPrivateRows.selected (by omega : 3≤q) hDualFree hDualSmaller dualX hDualXPos
          (by rw [hDualXMass]; exact hDualHigh) hDualRows (b:=⟨portParent,(mem_inN.mp hPortParent).1⟩)
          (a:=⟨portRoot,hPortRoot⟩) (mem_inN.mp hPortParent).2 ju hPortInner kk budget link path count⟩
    by_cases hPortFailure : ∃j∈portU,portGraph j portRoot=true ∧ portGraph j portParent=true ∧
        ((∃r∈portInnerBall,(q:ℚ)*WeightedSD.mass (outN portGraph portU r) dualX≤
            dualValue-WeightedSD.mass dualSource.V dualX+dualX j) ∨
         ∃k∈outN portGraph portU portInner,¬∃T⊆portU,T.card+1=q ∧
           Closure.CommonParentHeadRepair.IndependentHeads portGraph portInnerBall T ∧ k∈T ∧
           Closure.CommonParentHeadRepair.IndependentHeads portGraph
             (portInnerBall.filter (fun r=>portGraph r k=false)) (T.erase k) ∧
           ∃v,Relation.ReflTransGen (Closure.CommonParentHeadRepair.Step q portGraph portU
             (outN portGraph portU portRoot)) ({k},dualX) (T,v) ∧
             Closure.CommonParentEndpointReplay.Fork q portGraph dualSource.V portU
               (outN portGraph portU portRoot) portInnerBall T dualX v ∧
               Closure.EndpointPrivateRows.Tests q portGraph portU (outN portGraph portU portRoot) portInnerBall T v)
    · obtain ⟨j,ju,ja,jb,fail⟩ := hPortFailure
      rcases fail with ⟨r,rr,low⟩ | ⟨k,kk,deficient⟩
      · exact False.elim (((hPortRecursiveRepair j ju ja jb).2.2.1 r rr).not_ge low)
      · exact False.elim (deficient (hPortTerminal j ju ja jb k kk))
    have hPortLastLayer (i : ↥(ShenReturnCut.slots (dualSource.V.erase portRoot) (Closure.CyclePortMatching.demand portWeights portBonus portParent)))
        (par : Closure.FirstPacketBarrier.graph dualSource.D dualFamily i.val.1 portRoot=true) :=
      hNativePortDistance portRoot hPortRoot (portRoute i).val.1
        (Finset.mem_erase.mp (ShenReturnCut.mem_slots_iff.mp (portRoute i).property).1).2
        i.val.1 (hPortRoute i).2.1 par (hPortRoute i).1
    have hLeftLastLayer := hPortLastLayer portLeft hLeftParent
    have hRightLastLayer := hPortLastLayer portRight hRightParent
    obtain ⟨branchCycle,entry,exitLabel,firstParent,secondParent,firstExit,secondExit,
        sharedLength,entryHead,exitParent,nativeWeights,reverseWeights,entryBonus,exitBonus,
        segmentValue,hEntryBonus,hExitBonus,hSegmentValue,hNativeScale,hReverseScale,
        hSharedSection,hEntryBooking,hExitBooking,hAfterEntry,hBeforeExit⟩ :=
      Closure.CoupledSegmentPorts.on_cycle dualSource (by omega : 2≤q) hDualSmaller
        (C:=leftPortCycle) (by classical exact (Finset.mem_filter.mp (hDualSub hLeftPortCycle)).2)
    have hSegmentReturns := hSharedSection.table (by omega : 2≤q) dualSource.free
    have hSegmentShortcut := hSharedSection.shortcut (by omega : 2≤q) dualSource.free
    have hNativeCycleRoute {A B} (af : A∈Closure.FirstPacketBarrier.family dualSource)
        (bf : B∈Closure.FirstPacketBarrier.family dualSource) :=
      Closure.NativeCycleConnectivity.connected dualSource (by omega : 2≤q) af bf
    have hRouteToSlack := hNativeCycleRoute (hDualSub hLeftPortCycle) (hDualSub hSlackA)
    obtain ⟨thirdCycle,hThirdNative,hThirdOffLeft,hThirdOffBranch,hThirdAdjacent⟩ :=
      Closure.SharedArcInduction.third_cycle dualSource (by omega : 2≤q)
        hSharedSection.cycle₁ hSharedSection.cycle₂ hSharedSection.start
    obtain ⟨attachFamily,hAttachBuilt,hAttachNative,hAttachStart,hAttachSpans,hAttachSmall,
        ⟨attachDual,hAttachDual⟩,hSomeAttachment,hEveryAttachment⟩ :=
      Closure.SharedArcBarrier.on_source dualSource (by omega : 2≤q) hDualSmaller (hDualSub hLeftPortCycle)
    obtain ⟨outsideCycle,hAttachBoundary,hMinimumNewHeads,terminalPrices,terminalValue,hTerminalHigh,
        hTerminalPositive,hTerminalNormalized,hTerminalColumns,hTerminalComparison⟩ :=
      Closure.SharedArcPacketDescent.terminal dualSource (by omega : 2≤q) hDualSmaller hSomeAttachment
        (fun M b => (hEveryAttachment M b).1)
    have hPayExcept {e} (he : e∈Closure.SharedArcBarrier.targets dualSource.D dualSource.V attachFamily outsideCycle) :=
      Closure.SharedArcMinimalPacket.omit_one dualSource (by omega : 2≤q) hDualSmaller hAttachSmall
        hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1) he
    obtain ⟨packetInverse,hPacketInverse,hPacketCharges⟩ :=
      Closure.SharedArcMinimalPacket.charges dualSource (by omega : 2≤q) hDualSmaller hAttachSmall
        hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
    let packetGraph := Closure.FirstPacketBarrier.graph dualSource.D (insert outsideCycle attachFamily)
    have hPacketReachBudget (U : Finset ℕ) := @Closure.ReachInversePrices.column_budget q packetGraph dualSource.V U
      packetInverse (by omega : 2≤q) (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
      (hEveryAttachment _ hAttachBoundary).1 hPacketInverse
    have hPacketReturnChoice := @Closure.ReachInversePrices.alternate q packetGraph dualSource.V packetInverse
      (by omega : 2≤q) (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
      (hEveryAttachment _ hAttachBoundary).1 hPacketInverse
    by_cases hUnderpaidReturn : Closure.ReachInversePrices.Underpaid (q:=q) packetGraph dualSource.V packetInverse ∨
        Closure.ReachInversePrices.Underpaid (q:=q) (fun i j=>packetGraph j i) dualSource.V packetInverse.transpose
    · exact False.elim ((Closure.ReachInversePrices.excludes (by omega : 2≤q)
        (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
        (hEveryAttachment _ hAttachBoundary).1 hPacketInverse) hUnderpaidReturn)
    have hExactPacketParent := Closure.SharedArcPacketReturns.exact_parent dualSource (by omega : 2≤q)
      hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges
    have hDeletionObstruction := @Closure.SharedArcPacketReturns.zero_and_strict q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      packetInverse hPacketInverse hPacketCharges
    have hPricedAttachmentExit := Closure.SharedArcPacketReturns.blocks_exit dualSource (by omega : 2≤q)
      hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges (fun M b => (hEveryAttachment M b).1)
    have hTerminalProgress := Closure.SharedArcPacketDescent.blocks_progress (p:=terminalPrices) (c:=terminalValue)
      dualSource hPricedAttachmentExit (by
        intro M b count weak v vv
        obtain ⟨_,_,_,_,_,_,_,_,_,plateau⟩ := hTerminalComparison M b count
        exact ((plateau weak).2 v vv).1)
    have hTerminalSquareFloor := @Closure.SharedArcTailExchange.terminal_floor q _ dualSource
      (by omega : 2≤q) attachFamily outsideCycle hAttachBoundary terminalPrices terminalValue hTerminalColumns
      (fun repair => hTerminalProgress (Or.inr repair))
    have hFreshArcTransport := @Closure.SharedArcComponentExchange.transport q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
    have hFreshArcSeparation := @Closure.SharedArcComponentExchange.separate q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
    have hFreshDistanceRectangle := @Closure.SharedArcComponentExchange.distance_rectangle q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
    have hAnyNativeParentFloor := @Closure.SharedArcComponentExchange.all_parents q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M b => (hEveryAttachment M b).1)
      terminalPrices terminalValue hTerminalColumns (fun repair => hTerminalProgress (Or.inr repair))
    have hExactFlatDynamics := Closure.SharedArcFlatChain.at_terminal dualSource (by omega : 2≤q)
      hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges hTerminalHigh (by
        intro M bm count
        obtain ⟨x,_,d,le,_,xm,rows,_⟩ := hTerminalComparison M bm count
        exact ⟨x,d,le,xm,rows⟩)
    have hSingleArcProfile := @Closure.SingleArcReturnProfile.at_singleton q _ dualSource
      (by omega : 1≤q) attachFamily
    have hSecondNativeArc := @Closure.SingleArcReturnProfile.second_arc q _ dualSource
      (by omega : 1≤q) attachFamily
    have hSingleArcCriterion := @Closure.SingleArcAlternative.singleton_iff q _ dualSource (by omega : 2≤q) attachFamily
    have hDoubleEndpointExchange := @Closure.SingleArcDoubleExchange.native q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily
    have hPunctureSignExit := @Closure.SingleArcPunctureSign.progress q _ dualSource
      (by omega : 2≤q) attachFamily outsideCycle packetInverse terminalPrices terminalValue
    have hBalancedSwitchExit := @Closure.SingleArcPunctureSign.progress_of_switch q _ dualSource
      (by omega : 2≤q) attachFamily outsideCycle packetInverse terminalPrices terminalValue
    have hPunctureShortReturns := @Closure.SingleArcPunctureSign.returns q _ dualSource (by omega : 2≤q) attachFamily
    have hWalkCertificate := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.PunctureWalkCertificate.certificate q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hWalkSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.PunctureWalkCertificate.sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hWalkColumnMoments := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.PunctureWalkCertificate.sign_or_fit q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hWalkColumnCuts := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.PunctureWalkCertificate.common_column q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hOneStepWalkColumn := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.canonical q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc
    have hParentMergeExpansion := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.expansion q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc
    have hCoveredParentSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.cover_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hThinParentSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.thin_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hHeadCoverSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.head_cover_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hCoveredParentsSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.covered_parents_sign q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hFixedMergeSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.fixed_merge_iff q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hEndpointMergeExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.OneStepColumnMerge.endpoint_progress q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hEndpointLayerSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.EndpointLayerWitness.singleton q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hEndpointLayerExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.EndpointLayerWitness.progress q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hReturnRowPayment := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.EndpointLayerWitness.return_payment q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hMissedSetPrices := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.ReturnRowPrices.missed_set_prices q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hCountedReturnPayment := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.ReturnRowPrices.counted_return q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hReturnReserve := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.ReturnRowPrices.return_reserve q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hFlatReturnMass := fun {p : ℕ→ℚ} pc =>
      @Closure.ReturnRowPrices.singleton_return_mass q _ dualSource (by omega : 2≤q) attachFamily p pc
    have hTwoStepEscape := fun {w p : ℕ→ℚ} wp wm wr pc (three : 3≤q) =>
      @Closure.PunctureWalkCertificate.two_step_escape q _ dualSource attachFamily w p wp wm wr pc three hDualSmaller
    have hOrdinaryPuncturePrices := @Closure.SingleArcPunctureSign.ordinary_prices q _ dualSource hDualSmaller
    have hPuncturePricePressure := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.SingleArcPunctureSign.price_pressure q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hPunctureThresholdCycle := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.SingleArcPunctureSign.threshold_cycle q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hPunctureComparisonSign := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.SingleArcPunctureSign.comparison_rectangle q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc hDualSmaller
    have hSingleArcPrime := @Closure.SingleArcModuleBoundary.at_singleton q _ dualSource attachFamily
    have hFlatModuleExclusion := @Closure.SingleArcModuleBoundary.on_flat q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hStrictFlatMerges := @Closure.StrictFlatSubsetMerge.native q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hStrictHostMerges := @Closure.StrictFlatSubsetMerge.host q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hEndpointMergeReserve := @Closure.StrictFlatSubsetMerge.endpoint_reserve q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily
    have hTensorWeightedMerges := @Closure.SingleArcTensorMerge.all_cuts q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hTensorMergeExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.SingleArcTensorMerge.progress q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily w p wp wm wr pc
        outsideCycle packetInverse terminalPrices terminalValue
    have hUpstreamOldFeed := @Closure.CornerResidualJoint.joint q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
    have hUpstreamOldArcs := @Closure.CornerResidualJoint.stopped_arc_types q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hBoundarySlotRecurrence := @Closure.CornerHeadRecurrence.frontier q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads hAttachNative hAttachSpans
      (fun M bm => (hEveryAttachment M bm).1)
    have hBlockPayment := @Closure.CornerBlockPayment.on_source q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
    have hBlockReturnCut := @Closure.CornerBlockPayment.path_cut q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
    have hBlockExchange := @Closure.CornerBlockExchange.on_source q _ dualSource (by omega : 2≤q)
      hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hBlockSubstitution := @Closure.CornerBlockSubstitution.on_source q _ dualSource (by omega : 2≤q)
      hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hBoundaryIntervalPrices := @Closure.CornerBlockInterval.joint q _ dualSource (by omega : 2≤q)
      hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hRegularBlockCounts := @Closure.CornerBlockRegular.on_source q _ dualSource (by omega : 2≤q)
      hDualSmaller dualFamily dualP hDualPPos hBackwardRows attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    by_cases hTowerBlock : Closure.CornerTowerPayment.SparseBlock dualSource attachFamily outsideCycle
    · exact False.elim ((Closure.CornerTowerPayment.excludes dualSource (by omega : 2≤q) hDualSmaller
        hDualPPos hBackwardRows hAttachBoundary hMinimumNewHeads) hTowerBlock)
    by_cases hIntervalFits : Closure.CornerBlockInterval.Fits dualSource attachFamily outsideCycle
    · exact False.elim ((Closure.CornerBlockInterval.excludes dualSource (by omega : 2≤q) hDualSmaller
        hDualPPos hBackwardRows hAttachBoundary hMinimumNewHeads) hIntervalFits)
    have hMidpointParentLayer := @Closure.SingleArcMidpointSign.return_layer q _ dualSource (by omega : 2≤q) attachFamily
    have hChargedCyclePair := @Closure.SingleArcCycleParents.paired q _ dualSource (by omega : 2≤q) attachFamily
    have hOldCycleSupply := @Closure.SingleArcCycleParents.supply q _ dualSource (by omega : 2≤q) hDualSmaller attachFamily
    have hCycleExteriorAccount := @Closure.SingleArcCyclePrices.account q _ dualSource (by omega : 2≤q) attachFamily
    have hCycleCoverExit := fun {w p : ℕ→ℚ} wp wm wr pc =>
      @Closure.SingleArcCyclePrices.cover_progress.{0} q _ dualSource (by omega : 2≤q) attachFamily w p wp wm wr pc
        hDualSmaller outsideCycle packetInverse terminalPrices terminalValue
    have hSingletonExteriorWitness := @Closure.SingleArcCycleHead.singleton q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hVariableTailPrice := @Closure.SingleArcCycleBalance.flexible_bound q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hScalarCycleExit := @Closure.SingleArcCycleBalance.exterior_test q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hFixedParent := @Closure.SingleArcCommonParent.native q _ dualSource (by omega : 2≤q) attachFamily
    have hPairedCycleRepair := fun (C K : Finset ℕ)=>@Closure.CommonParentRepair.on_cycles q _ _ C K hq3
      (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
    have hParentRepairExit := fun {w p : ℕ→ℚ} wp wm wr pc=>@Closure.CommonParentRepair.progress q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily w p wp wm wr pc outsideCycle packetInverse terminalPrices terminalValue
    have hSingletonTiltObstruction := @Closure.SingleArcCommonParent.singleton q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hCommonTiltDecision := fun (C : Finset ℕ)=>@Closure.SingleArcCommonTilt.exact_test q _ _ C (by omega : 2≤q)
      (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
    have hOldHitMean := @Closure.CycleHitMass.mean q (Closure.FirstPacketBarrier.graph dualSource.D attachFamily)
      dualSource.V
    have hSecondNeighborBudgets := @Closure.SingletonSecondNeighbors.flat_ports q _ _ hq3
      (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
    have hBalancedArcBound := @Closure.SingletonSecondNeighbors.balanced_ports q _ _ hq3
      (Closure.PrivateArcEndpoints.graph_free dualSource attachFamily)
    have hClosedCycleBound := @Closure.SingleArcCyclePivot.diagonal_bound q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hMidpointParentBudgetExit := @Closure.SingleArcMidpointSign.progress q _ dualSource (by omega : 2≤q)
      attachFamily outsideCycle packetInverse terminalPrices terminalValue
    have hHeirMidpointOrCycle := @Closure.SingleArcHeirMidpoint.singleton q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hHoleAncestorObstruction := @Closure.SingleArcResidualSource.both_ends q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily
    have hFlatLawOfHeirs := Closure.HeirLaw.flatLaw_of_heirOrCoheirLaw dualSource (by omega : 2≤q)
    have hSingleArcTriangleAlternatives := fun (three : q=3) =>
      @Closure.SingleArcAlternative.triangle q _ dualSource three attachFamily
    have hIntervalScalarExit := @Closure.SingleArcNeighbourWitness.progress_of_sign q _ dualSource
      (by omega : 2≤q) attachFamily outsideCycle packetInverse terminalPrices terminalValue
    have hIntervalNeighbourExit := fun (three : q=3) => @Closure.SingleArcNeighbourWitness.progress
      q _ dualSource three attachFamily outsideCycle packetInverse terminalPrices terminalValue
    have hFlatCutExit := @Closure.SharedArcFlatTransport.progress_of_failed_cut q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle packetInverse terminalPrices terminalValue
    have hFlatTensorPositive := @Closure.SharedArcFlatArithmetic.positive q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily
    have hFreshEndpointMass := @Closure.SharedArcFlatArithmetic.mass_bound q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily terminalValue
    have hSimultaneousNativeStars := Closure.SharedArcCover.simultaneous dualSource
      (by omega : 2≤q) hDualSmaller hAttachSmall hAttachBoundary hMinimumNewHeads
    have hAllFreshTailsZero := @Closure.SharedArcCover.all_tails_zero q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hTwoMissedTargets := Closure.SharedArcReachMargin.two_targets dualSource (by omega : 2≤q) hDualSmaller
    have hStrictStarMargins := @Closure.SharedArcReachMargin.strict_stars q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hAllSubthresholdMargins := Closure.SharedArcReachMargin.every_strict dualSource
      (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads
    have hStrictMultiParent := Closure.SharedArcStrictParent.parent dualSource (by omega : 2≤q) hDualSmaller
      hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges
    have hStrictDeletionProfile := Closure.SharedArcStrictParent.deletion_profile dualSource
      (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads hPacketInverse hPacketCharges
    have hSingleReturnCorridor := @Closure.SharedArcSingleCorridor.corridor q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hAllCompetitorReturns := Closure.SharedArcExchangeReturn.bounded_returns dualSource hDualSmaller
      hAttachBoundary (fun M bm => (hEveryAttachment M bm).1)
    have hComponentInverseBound := @Closure.SharedArcExchangeReturn.component q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
      packetInverse hPacketInverse
    have hTensorProgress := Closure.SharedArcFlatArithmetic.blocks dualSource (by omega : 2≤q)
      hDualSmaller hTerminalProgress
    have hCanonicalLoopTest := Closure.SharedArcCompression.winning_iff dualSource hDualSmaller
      hAttachBoundary ((hEveryAttachment _ hAttachBoundary).1)
    have hSinglePivotAlternative := @Closure.SharedArcPivot.alternatives q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hSinglePivotParents := @Closure.SharedArcPivot.classify_parents q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hPivotLink := @Closure.SharedArcPivotPaths.disconnected q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachNative hAttachSpans hAttachBoundary hMinimumNewHeads
    have hPivotReachMass := @Closure.SharedArcPunctureExpansion.separated_mass q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hPunctureLayer := fun k => @Closure.SharedArcIntervalPuncture.deficient_layer q _ k dualSource
      (by omega : 2≤q) hDualSmaller
    have hNoCyclicPuncture := fun k => @Closure.SharedArcIntervalPuncture.cyclic_puncture_false q _ k dualSource
      (by omega : 2≤q) hDualSmaller
    have hPunctureReachExit := fun k => @Closure.SharedArcProductReach.excludes q _ k dualSource
      (by omega : 2≤q) hDualSmaller
    have hProductPunctureExit := fun k d (hThree : 3≤q) => @Closure.SharedArcProductReach.lex_excludes.{0,0} q _ k d
      dualSource hThree hDualSmaller
    have hPivotSumExit := @Closure.SharedArcPivotLoopSums.progress q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
    have hPivotStoppedRectangle := @Closure.SharedArcPivotChoice.stopped_rectangle q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotFlatPaymentFails := @Closure.SharedArcPivotFold.original_payment_fails q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotFoldSupplier := @Closure.SharedArcPivotFold.bank_escape q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotCoverMasks := fun (three : 3≤q) => @Closure.SharedArcPivotSpread.masks q _ dualSource three
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotCleanParent := fun (three : 3≤q) => @Closure.SharedArcPivotGate.clean_parent_only q _ dualSource three
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hGateClosedPayment := fun (three : 3≤q) => @Closure.SharedArcPivotGate.paid_of_closed q _ dualSource three
    have hPivotRectangleChild := @Closure.SharedArcPivotGate.rectangle_child q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotEveryPair := fun (three : 3≤q) => @Closure.SharedArcPivotSpread.every_pair q _ dualSource three
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotWholeSide := fun (three : 3≤q) => @Closure.SharedArcPivotSpread.whole_side q _ dualSource three
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    have hPivotDegreeCaps := fun k (three : 3≤q) => @Closure.SharedArcPivotDetour.capped_false q _ k dualSource three
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
    have hNoRegularPivot := fun k (three : 3≤q) => @Closure.SharedArcPivotDetour.regular_false q _ k dualSource three
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
    have hStoppedCommonBank := @Closure.RankedMerge.stopped_bank q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachNative hAttachSpans hAttachBoundary hMinimumNewHeads
    have hStoppedTwoPrices := @Closure.RankedMerge.two_banks q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    have hPivotMinimumExit := @Closure.SharedArcPivotChoice.minimum_test q _ dualSource (by omega : 2≤q)
      hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1)
    have hRecursiveExit := Closure.SharedArcPivot.blocks dualSource hDualSmaller hAttachBoundary
      (fun M bm => (hEveryAttachment M bm).1) hTensorProgress
    have hBudgetExit := Closure.SharedArcFlatBudget.blocks dualSource (by omega : 2≤q) hDualSmaller hRecursiveExit
    have hGateExit := Closure.SharedArcPivotGate.blocks dualSource (by omega : 2≤q) hDualSmaller hBudgetExit
    have hTriangleIntervalExcluded := fun (three : q=3) =>
      @Closure.SingleArcNeighbourWitness.excluded q _ dualSource three attachFamily outsideCycle
        hAttachBoundary hAttachSmall (fun M bm => (hEveryAttachment M bm).1) _ _ _ hGateExit
    have hAffordableReturnBarrier := Closure.SharedArcAffordablePaths.separator dualSource
      (by omega : 2≤q) hAttachDual (fun B b => (hEveryAttachment B b).1)
    obtain ⟨turnTail,hTurnTail,turnPivot,hTurnPivot,turnHead,hTurnHead,hTurnOld,hTurnNew,
        hTurnIn,hTurnOut,hTurnMissing,hTurnExactReturn,hTurnAllPrices⟩ :=
      Closure.SharedArcAffordablePaths.boundary_turn dualSource (by omega : 2≤q)
        hAttachBoundary hAttachSmall (fun B b => (hEveryAttachment B b).1)
    have hTurnCycle : ShenCycleSuccessor.Cycle dualSource.D dualSource.V q outsideCycle := by
      classical exact (Finset.mem_filter.mp hAttachBoundary.1).2
    have hNativeTurnReturns := @Closure.ForwardMerge.arc_returns q _ _ (by omega : 2≤q)
      dualSource.free hDualSmaller (fun v => (dualSource.weights v : ℚ))
      (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
      ⟨turnTail,hTurnCycle.sub hTurnTail⟩
      ⟨turnPivot,hTurnCycle.sub hTurnPivot⟩ hTurnIn
    have hCleanInduction := Closure.SharedArcCleanRecurrence.wellFounded dualSource (by omega : 2≤q)
    have hCleanStoppedFrontier := @Closure.SharedArcCleanRecurrence.priced_frontier q _ dualSource (by omega : 2≤q) hDualSmaller
      leftPortCycle attachFamily outsideCycle hAttachBuilt hAttachNative hAttachStart hAttachSpans hAttachSmall
      hAttachBoundary hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1)
    obtain ⟨cleanTerminal,hCleanReach,hCleanHeadReturns⟩ :=
      Closure.SharedArcCleanRecurrence.terminal_from dualSource (by omega : 2≤q) ⟨turnPivot,hTurnCycle.sub hTurnPivot⟩
    have hTerminalReturnLayers := Closure.StrictReturnLayers.covers
      (D:=dualSource.D) (w:=fun v => (dualSource.weights v : ℚ))
      (by omega : 2≤q) hDualSmaller dualSource.free
      (Finset.singleton_subset_iff.mpr cleanTerminal.property) (Finset.singleton_nonempty cleanTerminal.val)
      (fun v hv => by exact_mod_cast dualSource.positive v hv) dualSource.strict
    have hTerminalReturnCharge := fun (receiver : Nat) => Closure.StrictReturnLayers.bank_bound (a:=receiver)
      (D:=dualSource.D) (w:=fun v => (dualSource.weights v : ℚ))
      (by omega : 2≤q) hDualSmaller dualSource.free
      (Finset.singleton_subset_iff.mpr cleanTerminal.property) (Finset.singleton_nonempty cleanTerminal.val)
      (fun v _ => Nat.cast_nonneg (dualSource.weights v)) dualSource.strict
    have hPricedReturnBank := @Closure.StrictReturnLayers.paired q _ dualSource
      (by omega : 2≤q) hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      (fun M bm => (hEveryAttachment M bm).1)
    have hPairedReturnCuts := fun (three : 3≤q) => @Closure.StrictReturnLayers.paired_cuts q _ dualSource
      three hDualSmaller attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
      (fun M bm => (hEveryAttachment M bm).1)
    have hTurnCycleSwitch := Closure.SharedArcCleanRecurrence.cycle_switches dualSource (by omega : 2≤q) hTurnCycle
    have hCleanTerminalPair := fun (three : 3≤q) =>
      Closure.SharedArcCleanRecurrence.terminal_pair dualSource three cleanTerminal (fun a ta => by
        obtain ⟨z,zm,tz,az,_⟩ := hCleanHeadReturns a ta
        exact ⟨z,zm,tz,az⟩)
    have hAllAttachmentGaps {B} (b : Closure.SharedArcBarrier.Boundary dualSource attachFamily B) :=
      Closure.SharedArcBudget.gap dualSource (by omega : 2≤q) hDualSmaller hAttachNative hAttachSpans b hAttachSmall ((hEveryAttachment B b).1)
    obtain ⟨attachWeights,attachValue,hAttachHigh,hAttachMass,hAttachPositive,hAttachRows,
        hChangedPositive,hChangedProper,hChangedMassFloor,hAttachGap⟩ := hAllAttachmentGaps hAttachBoundary
    obtain ⟨hEachChangedMass,hTotalChangedMass⟩ :=
      Closure.SharedArcMinimalPacket.mass_floor dualSource (by omega : 2≤q) hDualSmaller hAttachSmall
        hAttachBoundary hMinimumNewHeads ((hEveryAttachment _ hAttachBoundary).1) hAttachNative hAttachSpans
        hAttachMass hAttachPositive hAttachRows
    obtain ⟨debitTail,hDebitTail,debitHead,hDebitHead,hDebitArc,hDebitNew,hDebitStrict,hDebitBudget⟩ :=
      hAttachGap attachDual hAttachDual
    have hCyclePortRectangle := Closure.FiniteHorizonHall.rectangle_on_source
      (by omega : 2≤q) hDualFree hDualSmaller hDualHigh hDualXPos hDualPPos
      hDualXMass hDualPMass hDualRows hDualColumns (fun M => (hCompleteFamily M).2)
    have hPunctureParentFlow := Closure.PunctureParentFlow.laws hDualFree hDualSmaller hDualSize
      hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
    have hParentSetCapacity := Closure.PunctureFlowCapstone.parent_sets hDualFree hDualSmaller hDualSize
      hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
    have hPunctureAbsorption := Closure.PunctureFlowCapstone.absorption_on_source hDualFree hDualSmaller
      hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
    have hOpposedExteriorCapacity {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) (ne : A≠M) :=
      Closure.OpposedExteriorCapacity.paired dualSource (by omega : 2≤q) hDualSmaller hDualSub ha hm ne
        hDualHigh hDualXPos hDualXMass hDualPMass hDualRows hDualColumns
    have hCoupledArcTrajectory := Closure.CoupledArcTrajectory.on_family dualSource (by omega : 2≤q)
      hDualSmaller hDualSub hDualCard hDualXPos hDualXMass hDualHigh hDualRows hDualPMass hDualColumns
    have hPaidArcTrajectory := Closure.PaidArcTrajectory.exists_paid dualSource (by omega : 2≤q)
      hDualSmaller hDualSub hDualCard hDualXPos hDualXMass hDualHigh hDualRows
    have hResidualRepairOrbit := Closure.ResidualRepairOrbit.on_family dualSource (by omega : 2≤q)
      hDualSmaller hDualSub hDualCard hDualXPos hDualXMass hDualHigh hDualRows
    have hChargedLabelOrbit := Closure.ChargedLabelOrbit.exists_charged dualSource hDualSmaller
      hDualSub hDualCard (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
    have hRecurrentRecipient := Closure.RecurrentRecipient.orbit dualSource (by omega : 2≤q)
      hDualSmaller hDualSub hDualCard (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
    have hOpposedPairPrices {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) (ne : A≠M) :=
      Closure.OpposedPairPrices.opposed dualSource hDualSmaller hDualSub ha hm ne
        (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
    have hUniformPairingLaw {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) (ne : A≠M) :=
      Closure.PairingPressure.on_family dualSource hDualSmaller hDualSub ha hm ne
        (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
    have hDualAtomTransfer := @Closure.EqualizerTransfer.classify q _ _ dualX dualValue (by omega) hDualFree
      hDualSmaller (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
    have hDualParentBalance := @Closure.RecipientBalance.balance q _ _ dualP dualValue hDualColumns
    have hDualSurvivingParent := @Closure.RecipientBalance.surviving_parent q _ _ dualP dualValue
      (fun i hi => (hDualPPos i hi).le) hDualColumns
    have hDualCycle {A} (ha : A∈dualFamily) :
        ShenCycleSuccessor.Cycle (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V q A := by
      classical
      exact Closure.FirstPacketBarrier.retain_cycle (Finset.mem_filter.mp (hDualSub ha)).2 ha
    have hCompleteOverlapTransition {A B} (ag : A∈dualFamily) (bg : B∈dualFamily) (ne : A≠B) :=
      Closure.FlatOverlapDescent.transition (by omega : 2≤q) hDualFree hDualSmaller
        ((hCompleteFamily A).mp ag) ((hCompleteFamily B).mp bg) ne
    have hShortSplitEscape {A M} (ha : A∈dualFamily) (hm : M∈dualFamily) {u y r z m}
        (ua : u∈A) (um : u∈M) (ya : y∈A) (rm : r∈M) (za : z∈A) (zm : z∈M)
        (ne : y≠r) (uy : Closure.FirstPacketBarrier.graph dualSource.D dualFamily u y=true)
        (ur : Closure.FirstPacketBarrier.graph dualSource.D dualFamily u r=true)
        (left : Walk (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) A y z m)
        (right : Walk (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) M r z m) :=
      Closure.ShortSplitExterior.alternatives (by omega : 2≤q) hDualFree hDualSmaller
        (hDualCycle ha) (hDualCycle hm) ua um ya rm za zm ne uy ur left right
        (fun i hi => (hDualXPos i hi).le) (hDualXMass ▸ hDualHigh) hDualRows
    have hDualFanDistance {A} (ha : A∈dualFamily) (v u t : ℕ) := @Closure.CycleFanDistance.bound _ _ A q
      v u t (by omega) hDualFree
      (hDualCycle ha)
    have hMarkedReceiver := Closure.MarkedSquareFrontier.receiver weightedSource (by omega : 2≤q)
    have hMarkedLoop := @Closure.MarkedSquareFrontier.from_cycle q n weightedSource (by omega : 2≤q)
    have hFullOrbitEscape := @Closure.AllCutoffPacketEscape.from_loop q n weightedSource (by omega : 2≤q)
    have hPunctureSeed := @Closure.PuncturedDistance.minimum_seed q n weightedSource (by omega : 2≤q)
    have hTriangleMiddle := @Closure.PunctureReceiverFrontier.triangle_middle q n weightedSource (by omega : 2≤q)
    have hReceiverFrontier := @Closure.PunctureReceiverFrontier.classify q n weightedSource (by omega : 2≤q)
    have hUpstreamBall := @Closure.MandatoryTwoStep.ball_covered q n weightedSource (by omega : 2≤q)
    have hPuncturedOrbit := @Closure.TwoSidedPuncture.orbit_destination q n weightedSource (by omega : 2≤q)
    have hColumnOrbitBound := @Closure.ComparableColumnCut.orbit_bound q n weightedSource (by omega : 2≤q)
    have hColumnBlockingParent := @Closure.ComparableColumnCut.blocking_parent q n weightedSource (by omega : 2≤q)
    have hLightColumnMass := @Closure.LightColumnPacking.chain_mass q n weightedSource (by omega : 2≤q)
    have hTwoCycleDeletion := @Closure.ShortestReturnCertificate.on_model q n weightedSource (by omega : 2≤q)
    have hJointBlockingParents := @Closure.JointBlockerCycle.paid_pair_on_cycle q n weightedSource (by omega : 2≤q)
    have hConsecutiveHeadPool := @Closure.ConsecutiveBlockerPool.consecutive_pool q n weightedSource (by omega : 2≤q)
    have hPivotPotential := @Closure.BlockerHeadRouting.concentration_at q n weightedSource (by omega : 2≤q)
    have hMinimumPairEscape := @Closure.MinimumPairEscape.all_heads q n weightedSource (by omega : 2≤q)
    have hClassStep := @Closure.PairEscapeTransition.transition q n weightedSource (by omega : 2≤q)
    have hPersistentClass := @Closure.ClassPunctureRecurrence.persistent q n weightedSource (by omega : 2≤q)
    have hMarkedBarrier := @Closure.FirstPacketBarrier.first q n weightedSource (by omega : 2≤q)
    obtain ⟨packetFamily,hPacketSub,hPacketCard,hPacketFeasible,hPacketMinimal,hPacketEndpoints⟩ :=
      Closure.JointCycleFamilyBarrier.joint weightedSource (by omega : 2≤q)
    obtain ⟨packetWeight,hPacketEligible,hPacketLeastMass,hPacketBarrierRows⟩ :=
      Closure.CycleWithdrawal.simultaneous weightedSource hPacketSub hPacketFeasible
    obtain ⟨hPacketPositive,hPacketBudget,hPacketStrict⟩ := id hPacketEligible
    have hNativePaidFork := Closure.NativePaidHeadFork.alternatives weightedSource (by omega : 2≤q) hPacketSub hPacketBarrierRows
    have hUnitCycleFork := @Closure.NativePaidHeadFork.unit_cycle q n weightedSource (by omega : 2≤q)
    have hPacketOrbit {M A} (hm : M∈packetFamily) (ha : A∈packetFamily) (hne : M≠A) := Closure.PaidCycleFamilyOrbit.orbit weightedSource hPacketSub hPacketPositive hPacketBudget hPacketStrict hm ha hne
    have hPacketExit := hPacketEndpoints packetWeight hPacketPositive hPacketBudget hPacketStrict
    have hPacketOrbitBill := @Closure.PaidCycleFamilyOrbit.orbit_bill q n weightedSource packetFamily packetWeight hPacketSub hPacketStrict
    have hPacketNextCharge {A M L} (ha : A∈packetFamily) (h : Closure.JointCycleFamilyBarrier.ExitTo weightedSource packetFamily packetWeight A M L) := Closure.PaidCycleFamilyOrbit.next_charge weightedSource hPacketSub ha h
    have hPacketHeadChoices {A M} (ha : A∈packetFamily) (hm : M∈packetFamily) (hne : A≠M) := Closure.TransferHeadChoices.choices weightedSource hPacketSub hPacketPositive hPacketBudget hPacketStrict ha hm hne
    have hPacketRecurrentClass := @Closure.TransferHeadChoices.recurrent_class q n weightedSource packetFamily
    have hPacketUncompensated {A M} (ha : A∈packetFamily) (hm : M∈packetFamily) (hne : A≠M) := Closure.TransferHeadChoices.uncompensated weightedSource hPacketSub hPacketPositive hPacketBudget hPacketStrict ha hm hne
    have hPacketPhaseFork {C} (hc : C∈packetFamily) := Closure.CyclePhaseFork.forced weightedSource (by omega : 2≤q) hPacketSub ⟨packetWeight,hPacketPositive,hPacketBudget,hPacketStrict⟩ hc
    have hWeightedSupportBound := Closure.CyclePhaseFork.support_bound weightedSource (by omega : 2≤q)
    have hPacketHeadCapacity {A} (ha : A∈packetFamily) (p : ℕ) := Closure.CyclePhaseFork.head_capacity weightedSource (by omega : 2≤q) hPacketSub ha p
    have hMateWeight := @Closure.PairWithdrawal.equal_mate_weight q n weightedSource (by omega : 2≤q)
    have hPartialWithdrawal := @Closure.PairWithdrawal.minimum_bill q n weightedSource (by omega : 2≤q)
    have hShortestShift {W} (sub : W ⊆ weightedSource.V) :=
      @Closure.AnchoredShiftFlow.least_period weightedSource.D W q (by omega) (weightedSource.free.mono_set sub)
    have hShortestCrossing {W} (sub : W ⊆ weightedSource.V) :=
      @Closure.AnchoredShiftFlow.short_loop_crossing weightedSource.D W q (by omega) (weightedSource.free.mono_set sub)
    have hExteriorColumn {W} (sub : W ⊆ weightedSource.V) :=
      Closure.AnchoredExteriorColumn.short_loop_escape weightedSource (by omega) sub
    have hTriangleOrbitEscape := Closure.MinimumOrbitEscape.model_law weightedSource
    have hTriangleRoleCoverage := Closure.TriangleReachableRoles.coverage_for_capstone weightedSource
    have hTriangleMarkPropagation := Closure.TriangleReachableRoles.propagation_for_capstone weightedSource
    by_cases hMarkedPayment : q=3 ∧ Closure.MarkedRolePayment.Supply weightedSource.D weightedSource.V weightedSource.weights
    · exact ((Closure.MarkedRolePayment.for_capstone weightedSource hMarkedPayment.1) hMarkedPayment.2).elim
    have hprofile := source.profile_obstruction
    obtain ⟨A,terminal⟩ := ShenReturnCut.from_host (D:=source.D) source.nonempty (horder.trans hcover)
    have inner := terminal.second_cut source.free (by omega) source.degree
    have schedule := terminal.itinerary (by omega : 1≤q)
    have hendpoint (u v k : ℕ) (room : k+2≤q) (hv : v∈source.V) (arc : source.D u v=true) :=
      ShenSharedHead.endpoint_table source.free room hv arc
    have htriangleBank (h3 : q=3) := ShenSharedHead.cyclic_bank
      (source.free.mono_bound hq3) source.degree source.nonempty hs
      (show source.V.card≤3*s by rw [h3] at hcover; omega)
    have hoverlap (i j l : ℕ) (hp : i+j≤q) (hl : l≤q) :=
      ShenLabelledReach.overlap_capacity source.free hp hl
    have hpairs (i j l : ℕ) (hp : i+j≤q) (hi : i≤l) (hj : j≤l) :=
      ShenNearTotal.pair_budget source.free hp hi hj
    obtain ⟨repairBasis,hRepairBasis,repairGo,repairSend,repairExterior,repairRaw,hRepairMark,
      hRepairChild,hAdjacentReplacement,hRepairMotion,hRawFrontier,hRepairProbs,hPaidWitness⟩ :=
      id hCoupledArcTrajectory
    obtain ⟨paidOccurrence,paidPeriod,paidRow,hPaidRow,hPaidPeriod,hPaidReturn,hPaidArcBill,hRise,hFall⟩ :=
      id hPaidWitness
    obtain ⟨slackLabel,hSlackLabelIn,hSlackLabelStrict⟩ :=
      hForcedPairSlack (repairRaw slackSeed) (hRepairChild slackSeed).1
    have hSeedMargin := Closure.SlackPairOrbit.margin (hRepairChild slackSeed).1 hSlackLabelIn hSlackLabelStrict
    have hSeedOrbit := Closure.SlackPairOrbit.from_seed repairGo repairRaw (fun s => (hRepairChild s).1)
      slackSeed hForcedPairSlack
    rcases (id hRawFrontier) with ⟨hEveryChildFlat,hConstantOmissionSize⟩ |
      ⟨rawOccurrence,rawPeriod,⟨rawColumn,hRawColumnRetained,hRawColumnSlack⟩,hRawPeriod,hRawReturn,hPositiveRawDebit⟩
    case' inl =>
      obtain ⟨hSeedTransient,slackSteps,hSeedSlackPrefix,hFirstFlatChild⟩ :=
        hSeedOrbit.resolve_left (by
          rintro ⟨i,per,z,zu,below⟩
          exact below.ne (((hEveryChildFlat ⟨_,per⟩).2 z zu).2))
      have hFirstFlatContact := Closure.SlackBoundaryBanks.on_child (by omega : 2≤q) hDualFree hDualSmaller
        (fun _ => hDualCycle) (fun s => (hRepairChild s).1) hFirstFlatChild
      have hFirstFlatMap := Closure.SlackPairOrbit.on_edge (by omega : 2≤q) hDualFree hDualSmaller
        (fun _ => hDualCycle) (fun s => (hRepairChild s).1) (hSeedSlackPrefix slackSteps le_rfl) hFirstFlatChild
      obtain ⟨repairRowLaw,hFlatRowLaw,hFlatOmittedPayments,hFlatCrossPayments,hFlatRelabel,hFlatBlockExchange⟩ :=
        Closure.FlatChildExchange.on_family (by omega : 2≤q) hDualFree hDualSmaller
          (fun a : Function.periodicPts repairGo => dualSource.V \ Closure.RawRepairAlternative.gone a.val)
          (fun a => repairRaw a.val) (fun _ => Finset.sdiff_subset)
          (fun a => (hRepairChild a.val).1.normalized) (fun a => (hEveryChildFlat a).2)
          (x:=fun i => (dualX i : ℝ)) (t:=fun i => (dualP i : ℝ)) (c:=(dualValue : ℝ))
          (by exact_mod_cast hDualHigh)
          (fun i hi => by exact_mod_cast (hDualXPos i hi).le)
          (by rw [WeightedSD.realMass_rat,hDualXMass]; norm_num)
          (by rw [WeightedSD.realMass_rat,hDualPMass]; norm_num)
          (fun i hi => by rw [WeightedSD.realRow_rat,hDualRows i hi])
          (fun i hi => by rw [WeightedSD.realCol_rat,hDualColumns i hi])
      have hFlatAdjacentExchange := Closure.FlatChildExchange.adjacent repairGo (fun a => (hRepairMark a).1)
        (fun a => (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1).sub)
        hConstantOmissionSize hFlatBlockExchange
      have hFlatStep (a : Function.periodicPts repairGo) :=
        fun e fix => Closure.FlatExchangeCycle.step hDualFree hDualSmaller
          (fun i hi => (hDualXPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          a (hRepairMark a.val).1 (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
          e fix ((hFlatAdjacentExchange a).2 e fix)
      have hFlatSize (a : Function.periodicPts repairGo) :
          (dualSource.V \ Closure.RawRepairAlternative.gone a.val).card < dualSource.V.card := by
        apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,?_⟩)
        intro eq
        have pay := (hFlatOmittedPayments a).1
        rw [eq] at pay
        simp at pay
        have high : (1:ℝ)<(dualValue:ℝ) := by exact_mod_cast hDualHigh
        linarith
      have hFlatGeometry (a : Function.periodicPts repairGo) := Closure.FlatExchangeCycle.child_geometry
        (by omega : 2≤q) hDualFree hDualSmaller Finset.sdiff_subset (hFlatSize a) (hRepairChild a.val).1
        (fun i hi => ((hEveryChildFlat a).2 i hi).2) (hFlatRowLaw a).1 (hFlatRowLaw a).2
      have hFlatSourceFrontier := Closure.FlatOrbitSaturation.frontier dualSource (by omega : 1≤q)
        repairGo (fun a => (hRepairMark a).1) (fun a => (hFlatGeometry a).1)
      have hFlatNativeCut (a : Function.periodicPts repairGo) {u v} (uv : u∈dualSource.V) (vv : v∈dualSource.V) :=
        Closure.FlatOrbitSaturation.phase_cut dualSource (by omega : 1≤q) repairGo
          (fun s => (hRepairMark s).1) (fun s => (hFlatGeometry s).1) a uv vv
      have hFlatStableLabel (a : Function.periodicPts repairGo) {u} (uv : u∈dualSource.V) :=
        Closure.FlatOrbitSaturation.stable_label dualSource (by omega : 1≤q) repairGo
          (fun s => (hRepairMark s).1) (fun s => (hFlatGeometry s).1) a uv
      have hFlatOddSource (a : Function.periodicPts repairGo) (odd : ¬Even (Function.minimalPeriod repairGo a.val)) :=
        Closure.FlatOrbitSaturation.odd_saturated repairGo (fun s => (hRepairMark s).1)
          (fun s => (hFlatGeometry s).1) a odd
      have hFlatNativeExtensions (a : Function.periodicPts repairGo) {u v}
          (uv : u∈dualSource.V \ Closure.RawRepairAlternative.gone a.val)
          (vv : v∈dualSource.V \ Closure.RawRepairAlternative.gone a.val) :=
        Closure.FlatOrbitSaturation.native_extensions dualSource (by omega : 2≤q) Finset.sdiff_subset
          (hFlatGeometry a).1 (fun i hi => ((hFlatRowLaw a).2 i hi).1)
          (fun i hi => ((hFlatRowLaw a).2 i hi).2) uv vv
      have hFlatConfined (a b : Function.periodicPts repairGo) :=
        Closure.FlatExchangeCycle.confined (by omega : 2≤q) hDualFree (hFlatGeometry a).1
          Finset.sdiff_subset (Finset.sdiff_subset : dualSource.V \ Closure.RawRepairAlternative.gone b.val ⊆ dualSource.V)
      have hFlatOrderedStep (a : Function.periodicPts repairGo) :=
        fun e fix => Closure.FlatExchangeChain.on_mark (by omega : 2≤q) hDualFree hDualSmaller
          (fun i hi => (hDualXPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).1).sub
          (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).2)
          (hRepairMark a.val) (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
          (hFlatGeometry a).1 (hFlatGeometry (Closure.CycleSlotOrbit.base repairGo a)).1 e fix
          ((hFlatAdjacentExchange a).2 e fix)
      have hFlatOffset (a : Function.periodicPts repairGo) :=
        fun e fix => Closure.FlatExchangeTriangle.offset_on_mark (by omega : 2≤q) hDualFree hDualSmaller
          (fun i hi => (hDualXPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).1)
          (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).2)
          (hRepairMark a.val) (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
          (hFlatGeometry a).1 (hFlatGeometry (Closure.CycleSlotOrbit.base repairGo a)).1 e fix
          ((hFlatAdjacentExchange a).2 e fix)
      have hFlatPacket (a : Function.periodicPts repairGo) :=
        fun e fix => Closure.FlatExchangeTriangle.packet_on_mark (by omega : 2≤q) hDualFree hDualSmaller
          (fun i hi => (hDualXPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).1)
          (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.val.property).1).2)
          (hRepairMark a.val) (hConstantOmissionSize a (Closure.CycleSlotOrbit.base repairGo a))
          (hFlatGeometry a).1 (hFlatGeometry (Closure.CycleSlotOrbit.base repairGo a)).1 e fix
          ((hFlatAdjacentExchange a).2 e fix)
      have hFlatOtherCycle (s : Closure.PairedFamilyLoop.State dualFamily) {N} (nf : N∈dualFamily) :=
        fun packet => Closure.FlatPairedExcursion.packet_overlap
          (B:=Closure.PairedFamilyLoop.current s) (C:=Closure.PairedFamilyLoop.current (repairGo s))
          hDualFree (hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).1) packet (hDualCycle nf)
      have hFlatOutsideFamily (a : Function.periodicPts repairGo) :=
        Closure.FlatPairedExcursion.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
          hDualXPos (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh) repairGo
          (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
          a.val (hEveryChildFlat a).1
      have hFlatRecursiveCut := Closure.FlatReturnLayers.on_schedule (by omega : 1≤q) hDualFree repairGo
        (fun s => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).1)
        (fun s => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).2)
        (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
      have hFlatExteriorOrder (a : Function.periodicPts repairGo) :=
        Closure.FlatMinimumExterior.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
          repairGo (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
          (fun s => (hFlatGeometry s).1) hDualXPos (fun i hi => (hDualPPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          (fun i hi => by rw [hDualPMass,hDualColumns i hi]; exact hDualHigh)
          a (hEveryChildFlat a).1
      have hFlatLongCycle (a : Function.periodicPts repairGo) :=
        Closure.FlatTightTraffic.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
          repairGo (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
          (fun s => (hFlatGeometry s).1) hDualXPos (fun i hi => (hDualPPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          (fun i hi => by rw [hDualPMass,hDualColumns i hi]; exact hDualHigh)
          a (hEveryChildFlat a).1
      have hFlatTransientReturn (a : Function.periodicPts repairGo) :=
        Closure.FlatTransientReturn.on_schedule (by omega : 2≤q) hDualFree hDualSmaller (fun _ => hDualCycle)
          repairGo (fun s => (hRepairMark s).1) (fun s => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark s))
          (fun s => (hFlatGeometry s).1) hDualXPos (fun i hi => (hDualPPos i hi).le)
          (fun i hi => by rw [hDualXMass,hDualRows i hi]; exact hDualHigh)
          (fun i hi => by rw [hDualPMass,hDualColumns i hi]; exact hDualHigh)
          repairRaw (fun s => (hRepairChild s).1) (fun s z hz => ((hEveryChildFlat s).2 z hz).2)
          a (hEveryChildFlat a).1
      have hFlatThreeStep := Closure.FlatExchangeTriangle.period_three hDualFree repairGo
        (fun a => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1)
        (fun a => hDualCycle (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).2)
        (fun a => (hRepairMark a).1) (fun a => Closure.FlatExchangeTriangle.marked_of_mark (hRepairMark a))

    all_goals apply (not_or.mpr ⟨hGateExit,not_or.mpr ⟨hForwardNoMerge,hNoPair⟩⟩)
    all_goals have hInputAtLeastEight : 8≤s := degreeFrontier.floor
    all_goals have hAboveDegreeSeven : 7*q+s<n+7 := degreeFrontier.pastSeven
    all_goals have hDegreeSevenGone : s≠7 := Nat.ne_of_gt hInputAtLeastEight
    all_goals have hEightOrder := degreeFrontier.eightOrder
    all_goals have hTightCoverBudget := degreeFrontier.coverBudget
    all_goals have hNo38DegreeNine := degreeFrontier.excludes_nine_38
    all_goals have hReducedOrder := cutoffReduction.upper
    all_goals have hReducedParity := cutoffReduction.parity
    all_goals have hOneLossOrder (degreeBand : s≤2*q) : (q/2)*(2*s-1)<n := lt_of_not_ge (fun fit=>hNoOneLossChild ⟨degreeBand,fit⟩)
    all_goals drain_ch_witnesses
    all_goals obtain ⟨nativeReverse,hNativeReversePos,hNativeReverseMass,hNativeReverseCols⟩ := Closure.NativeReturnAccounts.recover dualSource hDualSmaller hSeedMass hSeedRows
    all_goals have hOmittedArcBudget := Closure.CrossValueOmissions.on_family hSeedMass hNativeReverseMass hDualXMass hDualPMass hSeedPos hNativeReversePos hDualXPos hDualPPos hSeedRows hNativeReverseCols hDualRows hDualColumns hDualHigh
    all_goals have hStrictNativeAllocation : Closure.OmittedCycleProgress.Flat q dualSource.D dualSource.V seedW nativeReverse seedC := ⟨hSeedStrict,hSeedPos,hNativeReversePos,hSeedMass,hNativeReverseMass,hSeedRows,hNativeReverseCols⟩
    all_goals let restoreStage : Closure.OmittedCycleProgress.Stage dualSource := ⟨dualFamily,dualX,dualP,dualValue,hDualSub,hCompleteFamily,⟨hDualHigh,hDualXPos,hDualPPos,hDualXMass,hDualPMass,hDualRows,hDualColumns⟩⟩
    all_goals have hNativeOmittedArcCount (added : (Closure.CrossValueOmissions.lost dualSource.D (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V).Nonempty) := Closure.OmittedCycleProgress.descent (by omega : 2≤q) dualSource.free (Closure.PrivateArcEndpoints.graph_free dualSource dualFamily) hDualSmaller (fun _ _ _ _ h=>Closure.CrossValueOmissions.selected_sub h) restoreStage.flat hStrictNativeAllocation added
    all_goals have hPricedOmittedCycle {M : Finset ℕ} (cm : ShenCycleSuccessor.Cycle dualSource.D dualSource.V q M) (off : M∉dualFamily) := Closure.OmittedCycleProgress.priced_cycle dualSource (by omega : 2≤q) hDualSmaller hStrictNativeAllocation restoreStage cm off
    all_goals have hCycleRestoration (marked : Finset (ℕ×ℕ)) := Closure.OmittedCycleProgress.cover_arcs dualSource (by omega : 2≤q) hDualSmaller restoreStage marked
    all_goals have hNoRestorationLoop (wanted : Closure.MarkedCyclePeeling.Family) := Closure.OmittedCycleProgress.well_founded dualSource wanted
    all_goals obtain ⟨gateStart,hGateStartFamily,hGateStartGraph,hGateStartPrices,hGateStartValue⟩ := Closure.RestorationAtGate.start dualSource (by omega : 2≤q) hDualSmaller (Finset.insert_subset hAttachBoundary.1 hAttachNative) (hEveryAttachment outsideCycle hAttachBoundary).1 hTerminalHigh hTerminalPositive hTerminalNormalized hTerminalColumns
    all_goals have hGateStartInverse : FiniteCutInverse.CommonInverse (WeightedSD.realMatrix q (Closure.FirstPacketBarrier.graph dualSource.D gateStart.cycles) dualSource.V) packetInverse := by rw [hGateStartGraph]; exact hPacketInverse
    all_goals have hOriginalLastArc (wanted : Closure.MarkedCyclePeeling.Family) (native : wanted⊆Closure.FirstPacketBarrier.family dualSource) := Closure.LastArcPriceTransport.at_gate dualSource (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads (fun M bm=>(hEveryAttachment M bm).1) gateStart hGateStartGraph hGateStartPrices hGateStartValue hPacketInverse wanted native
    all_goals have hOriginalPacketFork (wanted : Closure.MarkedCyclePeeling.Family) (native : wanted⊆Closure.FirstPacketBarrier.family dualSource) := Closure.LastArcCompetitor.final_step dualSource (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads (fun M bm=>(hEveryAttachment M bm).1) gateStart hGateStartGraph hGateStartPrices hGateStartValue hPacketInverse wanted native
    all_goals have hCollisionPayment := Closure.LastArcMergePayment.at_gate dualSource (by omega : 2≤q) hDualSmaller hAttachBoundary hMinimumNewHeads (hEveryAttachment outsideCycle hAttachBoundary).1
    all_goals have hCollisionMenu := Closure.LastArcReturnMenu.on_model dualSource (by omega : 3≤q) (insert outsideCycle attachFamily)
    all_goals have hHeadDeposit := Closure.LastArcHeadDeposit.on_model dualSource (by omega : 2≤q) attachFamily
    all_goals have hMenuPayment := Closure.LastArcMenuPayment.on_model dualSource (by omega : 3≤q) attachFamily
    all_goals have hClosedFamily := Closure.AttachmentLaws.closed_family dualSource hAttachSmall (fun B b=>(hEveryAttachment B b).1)
    all_goals have hDoublyFed := Closure.AttachmentLaws.doubly_fed_all dualSource (by omega : 2≤q) (fun B b=>(hEveryAttachment B b).1)
    all_goals obtain ⟨boundaryReceiver,hBoundaryReceiver,hReceiverOutside,firstFeeder,hFirstFeeder,secondFeeder,hSecondFeeder,hFeedersDistinct,hFirstFeedArc,hSecondFeedArc,hFeederCycles,hFeederSeparation⟩ := Closure.BoundaryReceiverWitness.on_boundary dualSource (by omega : 2≤q) hAttachNative hAttachBoundary (hDoublyFed outsideCycle hAttachBoundary)
    all_goals
      have hFeederPrivateHeadTrace := Closure.FeederPrivateHeadDescent.at_boundary_feeders
        dualSource (by omega : 2 ≤ q) hDualSmaller hSeedRows hNativeReversePos
        (by rw [hNativeReverseMass]; exact hSeedStrict) hNativeReverseCols
        hAttachBoundary hFirstFeeder hSecondFeeder hFirstFeedArc hSecondFeedArc
      have hPrivateFeederCycle : ShenCycleSuccessor.Cycle dualSource.D dualSource.V q outsideCycle :=
        by classical exact (Finset.mem_filter.mp hAttachBoundary.1).2
      have hPrivateFeederVertices := And.intro
        (hPrivateFeederCycle.sub hFirstFeeder) (hPrivateFeederCycle.sub hSecondFeeder)
      have hFeederCyclePeriod := Closure.FeederPrivateHeadDescent.on_marked_cycle
        dualSource (by omega : 2 ≤ q) hDualSmaller hSeedPos hSeedRows hNativeReversePos
        (by rw [hNativeReverseMass]; exact hSeedStrict) hNativeReverseCols hPrivateFeederCycle
        hFirstFeeder hSecondFeeder hFeedersDistinct
      have hFeederCoprimeSpill (cop : Nat.Coprime
          (Closure.MandatoryExcursion.span dualSource.D dualSource.V q firstFeeder secondFeeder) (q+1)) :=
        Closure.FeederPrivateHeadDescent.coprime_spill dualSource (by omega : 2 ≤ q) hDualSmaller
          hSeedPos hSeedRows hNativeReversePos (by rw [hNativeReverseMass]; exact hSeedStrict)
          hNativeReverseCols hPrivateFeederCycle hFirstFeeder hSecondFeeder hFeedersDistinct
          (fun eq => hReceiverOutside (eq.symm ▸ hBoundaryReceiver)) cop
      have hJoinedFeederCoverage (cop : Nat.Coprime
          (Closure.MandatoryExcursion.span dualSource.D dualSource.V q firstFeeder secondFeeder) (q+1)) :=
        Closure.FeederPrivateHeadDescent.marked_spans dualSource (by omega : 2 ≤ q) hDualSmaller
          hNativeReversePos (by rw [hNativeReverseMass]; exact hSeedStrict) hNativeReverseCols
          hPrivateFeederCycle hFirstFeeder hSecondFeeder hFeedersDistinct cop
      obtain ⟨feederReverseBudget,feederReverseSource,hFeederReverseGraph,hFeederReverseCarrier,hFeederBothDirections⟩ :=
        Closure.FeederPrivateHeadDescent.at_receiver dualSource (by omega : 2 ≤ q) hDualSmaller
          hSeedPos (by rw [hSeedMass]; exact hSeedStrict) hSeedRows hNativeReversePos
          (by rw [hNativeReverseMass]; exact hSeedStrict) hNativeReverseCols
          hPrivateFeederVertices.1 hPrivateFeederVertices.2 hBoundaryReceiver
          (Closure.CrossValueOmissions.selected_sub hFirstFeedArc)
          (Closure.CrossValueOmissions.selected_sub hSecondFeedArc)
      have hFeederActualGateFlat : Closure.OmittedCycleProgress.Flat q
          (Closure.FirstPacketBarrier.graph dualSource.D (insert outsideCycle attachFamily))
          dualSource.V gateStart.x terminalPrices terminalValue := by
        have law := gateStart.flat
        rwa [hGateStartGraph,hGateStartPrices,hGateStartValue] at law
      have hFeederReplayOnAttachment := Closure.FeederStrictReplay.at_original
        (by omega : 2 ≤ q) (Closure.PrivateArcEndpoints.graph_free dualSource _) hDualSmaller
        hFeederActualGateFlat hPrivateFeederVertices.1 hPrivateFeederVertices.2 hBoundaryReceiver
        hFirstFeedArc hSecondFeedArc
      have hFeederAttachmentFork := hFeederBothDirections.imp_right (fun other =>
        other.imp_right (fun reg => Closure.FeederRetainedIncidence.at_attachment
          (by omega : 2 ≤ q) dualSource.free hDualSmaller hBoundaryReceiver
          (fun _ _ _ _ edge => Closure.CrossValueOmissions.selected_sub edge)
          hFeederActualGateFlat reg.1 reg.2.1 (reg.2.2 boundaryReceiver hBoundaryReceiver)))
      have hFeederDegreeSignature (ell : ℕ) (prime : ell.Prime) (divides : ell ∣ q)
          (diff : seedW firstFeeder ≠ seedW secondFeeder) :=
        letI : Fact ell.Prime := ⟨prime⟩
        Closure.FeederPrivateHeadDescent.same_pair_signature dualSource (by omega : 2 ≤ q) hDualSmaller
          divides hSeedPos hSeedRows hNativeReversePos (by rw [hNativeReverseMass]; exact hSeedStrict)
          hNativeReverseCols hPrivateFeederVertices.1 hPrivateFeederVertices.2 diff
      have hFeederRememberedSet (ell : ℕ) (prime : ell.Prime) (divides : ell ∣ q)
          (diff : seedW firstFeeder ≠ seedW secondFeeder) :=
        letI : Fact ell.Prime := ⟨prime⟩
        Closure.FeederPrivateHeadDescent.remembered_set dualSource (by omega : 2 ≤ q) hDualSmaller
          hSeedRows hNativeReversePos (by rw [hNativeReverseMass]; exact hSeedStrict) hNativeReverseCols
          divides hPrivateFeederVertices.1 hPrivateFeederVertices.2 diff
      have hTwoFeederBills (ell : ℕ) (prime : ell.Prime) (divides : ell ∣ q)
          (diff : seedW firstFeeder ≠ seedW secondFeeder) :=
        letI : Fact ell.Prime := ⟨prime⟩
        Closure.FeederPrivateHeadDescent.two_labels dualSource (by omega : 2 ≤ q) hDualSmaller
          hSeedRows hNativeReversePos (by rw [hNativeReverseMass]; exact hSeedStrict) hNativeReverseCols
          divides hPrivateFeederVertices.1 hPrivateFeederVertices.2 diff
    all_goals obtain ⟨firstFeederCycle,hFirstFeederCycle,secondFeederCycle,hSecondFeederCycle,hFeederCyclesDistinct,hFirstOnCycle,hReceiverOnFirst,hSecondOnCycle,hReceiverOnSecond⟩ := hFeederCycles
    all_goals have hDisjointBoundaryParts := hFeederSeparation firstFeederCycle hFirstFeederCycle secondFeederCycle hSecondFeederCycle hFirstOnCycle hReceiverOnFirst hSecondOnCycle hReceiverOnSecond
    all_goals obtain ⟨leftLossSuccessor,hLeftLossSuccessor,hLeftLossArc,hLeftLossTargets⟩ := Closure.ReceiverRetry.uniform_loss_targets dualSource (by omega : 2≤q) hAttachNative hFirstFeederCycle hMinimumNewHeads hFirstOnCycle hReceiverOnFirst (Closure.CrossValueOmissions.selected_sub hFirstFeedArc)
    all_goals obtain ⟨rightLossSuccessor,hRightLossSuccessor,hRightLossArc,hRightLossTargets⟩ := Closure.ReceiverRetry.uniform_loss_targets dualSource (by omega : 2≤q) hAttachNative hSecondFeederCycle hMinimumNewHeads hSecondOnCycle hReceiverOnSecond (Closure.CrossValueOmissions.selected_sub hSecondFeedArc)
    all_goals have hFirstPricedBank := Closure.ReceiverRetry.priced_bank dualSource (by omega : 2≤q) hAttachNative hFirstFeederCycle hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1) hAttachDual hFirstOnCycle hReceiverOnFirst hLeftLossSuccessor (Closure.CrossValueOmissions.selected_sub hFirstFeedArc) hLeftLossArc
    all_goals have hSecondPricedBank := Closure.ReceiverRetry.priced_bank dualSource (by omega : 2≤q) hAttachNative hSecondFeederCycle hMinimumNewHeads (fun M bm => (hEveryAttachment M bm).1) hAttachDual hSecondOnCycle hReceiverOnSecond hRightLossSuccessor (Closure.CrossValueOmissions.selected_sub hSecondFeedArc) hRightLossArc
    all_goals have hReceiverMixture := Closure.ReceiverMixture.receiver_mixture dualSource (by omega : 2≤q) (by classical exact (Finset.mem_filter.mp hAttachBoundary.1).2) (by classical exact (Finset.mem_filter.mp (hAttachNative hFirstFeederCycle)).2) (by classical exact (Finset.mem_filter.mp (hAttachNative hSecondFeederCycle)).2) hDisjointBoundaryParts (hEveryAttachment outsideCycle hAttachBoundary).1
    all_goals have hNormalizeReceiver (K : Finset ℕ) (seed : Closure.ReceiverRetry.Supports dualSource.D attachFamily outsideCycle boundaryReceiver K) := Closure.ReceiverRetry.on_boundary dualSource (by omega : 2≤q) hAttachNative hAttachSmall (fun M bm => (hEveryAttachment M bm).1) hAttachBoundary hMinimumNewHeads hReceiverOutside seed
    all_goals obtain ⟨leftReceiverSupport,hLeftRetryPath,hLeftReceiverSupport,hLeftRetryStop, ⟨leftReceiverBlocker,hLeftReceiverBlocker,hLeftReceiverOver⟩,hLeftRetryColumns⟩ := hNormalizeReceiver firstFeederCycle ⟨hFirstFeederCycle,hReceiverOnFirst,firstFeeder,hFirstFeeder,hFirstOnCycle,Closure.CrossValueOmissions.selected_sub hFirstFeedArc⟩
    all_goals obtain ⟨rightReceiverSupport,hRightRetryPath,hRightReceiverSupport,hRightRetryStop, ⟨rightReceiverBlocker,hRightReceiverBlocker,hRightReceiverOver⟩,hRightRetryColumns⟩ := hNormalizeReceiver secondFeederCycle ⟨hSecondFeederCycle,hReceiverOnSecond,secondFeeder,hSecondFeeder,hSecondOnCycle,Closure.CrossValueOmissions.selected_sub hSecondFeedArc⟩
    all_goals have hReceiverMerge (same : leftReceiverSupport = rightReceiverSupport) := Closure.ReceiverRetry.merge_corridor dualSource (by omega : 2≤q) hAttachNative (by classical exact (Finset.mem_filter.mp hAttachBoundary.1).2) (A:=firstFeederCycle) (B:=secondFeederCycle) (z:=boundaryReceiver) ⟨hFirstFeederCycle,hReceiverOnFirst,firstFeeder,hFirstFeeder,hFirstOnCycle,Closure.CrossValueOmissions.selected_sub hFirstFeedArc⟩ ⟨hSecondFeederCycle,hReceiverOnSecond,secondFeeder,hSecondFeeder,hSecondOnCycle,Closure.CrossValueOmissions.selected_sub hSecondFeedArc⟩ hFirstFeeder hSecondFeeder hFeedersDistinct hFirstOnCycle hSecondOnCycle (Closure.CrossValueOmissions.selected_sub hFirstFeedArc) (Closure.CrossValueOmissions.selected_sub hSecondFeedArc) hLeftRetryPath (same.symm ▸ hRightRetryPath)
    all_goals have hJointReceiverBank (same : leftReceiverSupport = rightReceiverSupport) := Closure.ReceiverRetry.bank_after_merge dualSource (by omega : 2≤q) hAttachNative (by classical exact (Finset.mem_filter.mp hAttachBoundary.1).2) (A:=firstFeederCycle) (B:=secondFeederCycle) (z:=boundaryReceiver) ⟨hFirstFeederCycle,hReceiverOnFirst,firstFeeder,hFirstFeeder,hFirstOnCycle,Closure.CrossValueOmissions.selected_sub hFirstFeedArc⟩ ⟨hSecondFeederCycle,hReceiverOnSecond,secondFeeder,hSecondFeeder,hSecondOnCycle,Closure.CrossValueOmissions.selected_sub hSecondFeedArc⟩ hReceiverOutside hFirstFeeder hSecondFeeder hFeedersDistinct hFirstOnCycle hSecondOnCycle (Closure.CrossValueOmissions.selected_sub hFirstFeedArc) (Closure.CrossValueOmissions.selected_sub hSecondFeedArc) hLeftLossSuccessor hLeftLossArc hLeftRetryPath (same.symm ▸ hRightRetryPath) hLeftReceiverSupport
    all_goals have hReceiverDeletionBound (T : Finset ℕ) (inside : T ⊆ outsideCycle) := Closure.BoundaryReceiverWitness.lost_parents dualSource (by omega : 2≤q) hAttachNative (by classical exact (Finset.mem_filter.mp hAttachBoundary.1).2) inside boundaryReceiver
    all_goals have hReceiverRefund (T : Finset ℕ) (charged : T ⊆ inN (Closure.FirstPacketBarrier.graph dualSource.D attachFamily) dualSource.V boundaryReceiver) := Closure.BoundaryReceiverWitness.cut_attach_price dualSource hAttachNative hReceiverOutside charged attachDual
    all_goals have hLeastSwap := @Closure.AttachmentLaws.least_swap q _ dualSource (by omega : 2≤q) attachFamily outsideCycle hAttachBoundary hMinimumNewHeads
    all_goals obtain ⟨attachCap,hAttachCapHigh,hAttachCapBound,hAttachCapAttained⟩ := Closure.AttachmentLaws.price_cap dualSource (hEveryAttachment outsideCycle hAttachBoundary).1 hAttachDual
    all_goals have hTwoHit := fun K (ks : K⊆dualSource.V) big paid => Closure.DepositTrace.two_hit dualSource attachDual hAttachDual (hEveryAttachment outsideCycle hAttachBoundary).1 hAttachCapHigh.le hAttachCapBound (K:=K) ks big paid
    all_goals have hBlockingTrace := fun v (vv : v∈dualSource.V) vpaid => Closure.DepositTrace.trace_dichotomy dualSource (by omega : 1≤q) (by classical exact (Finset.mem_filter.mp hAttachBoundary.1).2) attachDual hAttachDual (hEveryAttachment outsideCycle hAttachBoundary).1 hAttachCapHigh.le hAttachCapBound hAttachCapAttained vv vpaid
    all_goals have hOriginalExitMenu (u v : dualSource.V) (uv : dualSource.D u v=true) := @Closure.LastArcGatePayment.menu_at_arc q _ (insert outsideCycle attachFamily) dualSource u v uv
    all_goals have hGateRestoration (marked : Finset (ℕ×ℕ)) := Closure.OmittedCycleProgress.cover_arcs dualSource (by omega : 2≤q) hDualSmaller gateStart marked
    all_goals rcases hSeedFrontier with ⟨seedVertex,hSeedVertex,hSeedHeavy⟩ | ⟨seedPair,hSeedMiss⟩ | ⟨seedPair,hSeedCovered⟩
    all_goals ch_on_fact missed of Closure.TwoHeadRepairReplay.Missing => have hFirstMissAt := Closure.TwoHeadForcedMiss.first_miss missed
    all_goals ch_on_fact report of FreshMenuExitRules.Report => obtain ⟨freshMenu,hFreshInside,freshRow,hFreshInner,freshHead,hFreshInMenu,hFreshIncidence,hFreshOtherMiss,hFreshKept,hFreshMenuSize,hFreshRounds,hFreshKeepLost,hFreshCommonCount,hFreshMassFloor,hFreshMassCap,hFreshMenuShort,hFreshOutsideNeeded,hFreshTotalShort,hFreshExactDeficit,hFreshRankedHeavy,hFreshRankedReach,hFreshRankedRowPrices,hFreshRankedBillIff,hFreshRankedBlock,freshCycle,hFreshCycle,hFreshRowOnCycle,hFreshHeadOnCycle,hFreshCyclePayment⟩ := report.witness
    all_goals if_ch_fact hFreshCycle => have hFreshBoundaryTest := FreshMenuExitRules.actual_attachment (inv:=packetInverse) (prices:=terminalPrices) (value:=terminalValue) hNativeCutoff hDualSmaller hAttachBoundary (fun M hM=>(hEveryAttachment M hM).1) hFreshCycle
    all_goals if_ch_fact hFreshRankedBlock => obtain ⟨freshMinimum,hFreshMinimumIn,hFreshMinimumLeast,hFreshMinimumBill,hFreshMinimumTurn⟩ := hFreshRankedBlock
    all_goals if_ch_fact hSeedMiss => obtain ⟨seedKeep,seedDrop,hSeedOrientation,seedTerminal,seedPrices,hSeedTrace,hSeedKeep,hSeedCount,hSeedChecks,seedUncovered,hSeedUncovered,hSeedMisses,seedFresh,hSeedArc,hSeedFresh,hSeedFreshReplay,hSeedExteriorTests⟩ := Closure.TwoHeadRepairReplay.missed_label hSeedMiss
    all_goals if_ch_fact hSeedOrientation => obtain ⟨hFirstDroppedParent,hFirstKeptParent⟩ := Closure.MissedFreshCut.first_parents dualSource (by omega : 2≤q) seedPair hSeedOrientation
    all_goals if_ch_fact hFirstDroppedParent => obtain ⟨hFirstMinimalChecks,hFirstCommonCut,hFirstStableCut,hFirstMissedRows⟩ := Closure.MissedFreshCut.on_model dualSource (by omega : 3≤q) hDualSmaller hSeedStrict hSeedRows hSeedPos seedPair.diffuse seedPair.av hFirstDroppedParent hFirstKeptParent hSeedKeep hSeedCount hSeedChecks
    all_goals if_ch_fact hFirstDroppedParent => have hFirstSparseReverse (few : (inN dualSource.D dualSource.V seedPair.a).card<q) := Closure.SparseParentDual.obstruction (by omega : 2≤q) hDualHigh (fun i hi=>(hDualPPos i hi).le) seedPair.av (hDualColumns _ seedPair.av) few
    all_goals if_ch_fact hFirstDroppedParent => have hFirstNativeParent := Closure.NativeReturnAccounts.parent_bound (by omega : 2≤q) hSeedStrict seedPair.av (Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0<q) (Closure.MissedFreshCut.native_degree (by omega : 2≤q) hSeedStrict hSeedRows seedPair.diffuse seedPair.av))) hNativeReversePos hNativeReverseCols
    all_goals if_ch_fact hFirstMissedRows => obtain ⟨⟨hFirstFreshCount,hFirstDisjoint,hFirstStrictCut,hFirstFullRow⟩,hFirstInnerCount,hFirstInnerBill,hFirstInnerLive,hFirstTwoParentChoices,hFirstLiveOrRestart⟩ := hFirstMissedRows seedUncovered hSeedUncovered hSeedMisses
    all_goals if_ch_fact hSeedCovered => have hSeedNativeBlockers := Closure.TwoHeadRepairReplay.covered_labels (by omega : 3≤q) dualSource.free hDualSmaller hSeedCovered
    all_goals if_ch_fact hSeedCovered => have hSeedInnerAncestorRoom := Closure.TwoHeadAncestorReplay.inner_room (by omega : 3≤q) dualSource.free hDualSmaller hSeedMass hSeedCovered
    all_goals if_ch_fact hSeedCovered => have hSeedExteriorNeeded (D P : Finset ℕ) (hd : outN dualSource.D dualSource.V seedPair.a⊆D) (dr : D⊆Closure.LabelledLeakageCapacity.region q dualSource.D dualSource.V seedPair.a) (outside : P⊆dualSource.V\Closure.LabelledLeakageCapacity.region q dualSource.D dualSource.V seedPair.a) := Closure.TwoHeadAncestorReplay.exterior_needed (by omega : 3≤q) dualSource.free hDualSmaller hSeedMass hSeedCovered hd dr outside
    all_goals if_ch_fact hSeedCovered => have hSeedReturnMenu (P : Finset ℕ) (inside : P⊆dualSource.V) {b d : ℕ} (start : b∈P) (path : Walk dualSource.D dualSource.V seedPair.a b d) (room : d+1+P.card≤q) := Closure.TwoHeadAncestorReplay.short_menu dualSource.free hSeedCovered inside start path room
    all_goals ch_on_fact cover of Closure.TwoHeadRepairReplay.Covered => have hSeedSwappedBound := Closure.TwoHeadRepairReplay.covered_swapped (by omega : 3≤q) cover
    all_goals if_ch_fact hSeedCovered => obtain ⟨newSeedRoot,hNewSeedRoot,hDifferentSeedRoot,hAllSeedReturns,newSeedRow,hNewSeedRow,hNewSeedBill,hNewSeedLive,newSeedPrice,hNewSeedFirst,hNewSeedRuns⟩ := Closure.TwoHeadForcedMiss.refine_reroot dualSource (by omega : 3≤q) hDualSmaller hSeedRows hSeedPos hSeedStrict (Closure.TwoHeadRepairReroot.reroot dualSource (by omega : 3≤q) hDualSmaller hSeedMass hSeedStrict hSeedPos hSeedRows hSeedCovered)
    all_goals if_ch_fact hSeedCovered => obtain ⟨hSeedLeftChild,hSeedRightChild,hSeedTwoExits,hSeedSharedRoot,hSeedOverlap⟩ := hSeedCovered
    all_goals if_ch_fact hNewSeedLive => obtain ⟨newSeedHead,hNewSeedHead⟩ := hNewSeedLive
    all_goals if_ch_fact hNewSeedRuns => obtain ⟨hNewSeedHeadParent,hNewSeedCutsByReturn⟩ := hNewSeedRuns newSeedHead hNewSeedHead
    all_goals if_ch_fact hNewSeedHeadParent => obtain ⟨newSeedReturn,hNewSeedReturnIn,hNewSeedReturnArc⟩ := hAllSeedReturns newSeedHead hNewSeedHeadParent
    all_goals if_ch_fact hNewSeedReturnArc => obtain ⟨newSeedCut,hNewSeedParent,hNewSeedDifferent,hNewSeedCutMissesReturn,hNewSeedCut,hNewSeedMissed⟩ := hNewSeedCutsByReturn newSeedReturn hNewSeedReturnIn hNewSeedReturnArc
    all_goals if_ch_fact hNewSeedMissed => have hRerootMissAt : Closure.TwoHeadForcedMiss.MissAt q dualSource.D dualSource.V seedW := ⟨newSeedRoot,hNewSeedRoot,newSeedHead,newSeedCut,newSeedPrice,hNewSeedDifferent.symm,hNewSeedFirst newSeedHead hNewSeedHead,hNewSeedMissed⟩
    all_goals if_ch_fact hNewSeedMissed => obtain ⟨againHeads,againPrices,hAgainPath,hAgainSeed,hAgainCount,hAgainChecks,againRow,hAgainRow,hAgainMiss,againFresh,hAgainArc,hAgainFresh,hAgainReplay,hAgainExteriorTests⟩ := hNewSeedMissed
    all_goals if_ch_fact hAgainChecks => have hAgainLocation := Closure.TwoHeadForcedMiss.terminal_location dualSource (by omega : 3≤q) hNewSeedRoot hNewSeedHeadParent hAgainSeed hAgainCount hAgainChecks
    all_goals if_ch_fact hAgainChecks => obtain ⟨hAgainMinimalChecks,hAgainCommonCut,hAgainStableCut,hAgainMissedRows⟩ := Closure.MissedFreshCut.on_model dualSource (by omega : 3≤q) hDualSmaller hSeedStrict hSeedRows hSeedPos seedPair.diffuse hNewSeedRoot hNewSeedParent hNewSeedHeadParent hAgainSeed hAgainCount hAgainChecks
    all_goals if_ch_fact hAgainMissedRows => obtain ⟨⟨hAgainFreshCount,hAgainDisjoint,hAgainStrictCut,hAgainFullRow⟩,hAgainInnerCount,hAgainInnerBill,hAgainInnerLive,hAgainTwoParentChoices,hAgainLiveOrRestart⟩ := hAgainMissedRows againRow hAgainRow hAgainMiss
    all_goals if_ch_fact hAgainLiveOrRestart => have hAgainLiveOrReplayed := hAgainLiveOrRestart.imp_right (Closure.MissedFreshCut.replay_restart dualSource (by omega : 3≤q) hDualSmaller hSeedStrict hSeedRows hSeedPos seedPair.diffuse hNewSeedRoot hAgainRow hAllSeedReturns)
    all_goals if_ch_fact hNewSeedCutMissesReturn => have hPunctureWithdrawal (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.MissedFreshCut.withdrawal_on_returns dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot hp hNewSeedDifferent.symm hNewSeedParent hAllSeedReturns hNewSeedReturnIn hNewSeedReturnArc hSeedPos (hSeedMass ▸ hSeedStrict) hSeedRows
    all_goals if_ch_fact hNewSeedCutMissesReturn => have hParentDeposit (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.ParentReturnDeposit.two_parents dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot hp hAllSeedReturns hNewSeedReturnIn hNewSeedReturnArc hSeedPos (hSeedMass ▸ hSeedStrict) hSeedRows
    all_goals if_ch_fact hNewSeedCutMissesReturn => have hReturnPivot (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.TwoParentReturnPivot.native dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot hp hNewSeedReturnIn hNewSeedReturnArc hSeedPos (hSeedMass ▸ hSeedStrict) hSeedRows
    all_goals if_ch_fact hNewSeedCutMissesReturn => obtain ⟨newSeedOtherReturn,hOtherSeedReturnIn,hOtherSeedReturnArc⟩ := hAllSeedReturns newSeedCut hNewSeedParent
    all_goals if_ch_fact hOtherSeedReturnArc => have hOpposedBanks (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.TwoParentOpposedBanks.paired dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot hp hAllSeedReturns hNewSeedReturnIn hNewSeedReturnArc hOtherSeedReturnIn hOtherSeedReturnArc hSeedPos hSeedMass (hSeedMass ▸ hSeedStrict) hSeedRows seedPair.diffuse
    all_goals if_ch_fact hOtherSeedReturnArc => have hAgainSparseReverse (few : (inN dualSource.D dualSource.V newSeedRoot).card<q) := Closure.SparseParentDual.obstruction (by omega : 2≤q) hDualHigh (fun i hi=>(hDualPPos i hi).le) hNewSeedRoot (hDualColumns _ hNewSeedRoot) few
    all_goals if_ch_fact hOtherSeedReturnArc => have hTwoParentReverse (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.SparseParentDual.pair (by omega : 3≤q) hDualHigh (fun i hi=>(hDualPPos i hi).le) hNewSeedRoot (hDualColumns _ hNewSeedRoot) hp
    all_goals if_ch_fact hOtherSeedReturnArc => have hAgainNativeParent := Closure.NativeReturnAccounts.parent_bound (by omega : 2≤q) hSeedStrict hNewSeedRoot (Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0<q) (Closure.MissedFreshCut.native_degree (by omega : 2≤q) hSeedStrict hSeedRows seedPair.diffuse hNewSeedRoot))) hNativeReversePos hNativeReverseCols
    all_goals if_ch_fact hOtherSeedReturnArc => have hNativeTwoParentColumn (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.NativeReturnAccounts.at_pair hp hNewSeedDifferent.symm (hNativeReverseCols _ hNewSeedRoot)
    all_goals if_ch_fact hOtherSeedReturnArc => have hNativeBankCapacity (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) {T : Finset ℕ} (within : T⊆outN dualSource.D (Closure.LabelledLeakageCapacity.region q dualSource.D dualSource.V newSeedRoot) newSeedHead) (nonempty : T.Nonempty) := Closure.TwoParentReturnCapacity.native_return_gap dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot hp hAllSeedReturns hSeedPos hSeedMass (hSeedMass ▸ hSeedStrict) hSeedRows seedPair.diffuse hNativeReversePos hNativeReverseCols within nonempty
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherBankCapacity (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) {T : Finset ℕ} (within : T⊆outN dualSource.D (Closure.LabelledLeakageCapacity.region q dualSource.D dualSource.V newSeedRoot) newSeedCut) (nonempty : T.Nonempty) := Closure.TwoParentReturnCapacity.native_return_gap dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot (hp.trans (Finset.pair_comm _ _)) hAllSeedReturns hSeedPos hSeedMass (hSeedMass ▸ hSeedStrict) hSeedRows seedPair.diffuse hNativeReversePos hNativeReverseCols within nonempty
    all_goals if_ch_fact hOtherSeedReturnArc => have hReturnSponsorCase (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.ReturnSponsorMass.native dualSource (by omega : 3≤q) hDualSmaller hNewSeedRoot hp hAllSeedReturns hNewSeedReturnIn hNewSeedReturnArc hSeedPos hSeedMass (hSeedMass ▸ hSeedStrict) hSeedRows seedPair.diffuse hNativeReversePos hNativeReverseCols
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherSponsorCase (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.ReturnSponsorMass.native dualSource (by omega : 3≤q) hDualSmaller hNewSeedRoot (hp.trans (Finset.pair_comm _ _)) hAllSeedReturns hOtherSeedReturnIn hOtherSeedReturnArc hSeedPos hSeedMass (hSeedMass ▸ hSeedStrict) hSeedRows seedPair.diffuse hNativeReversePos hNativeReverseCols
    all_goals if_ch_fact hOtherSeedReturnArc => have hKeptSeedTargetReach := Closure.ReturnTargetReach.native (y:=newSeedCut) dualSource (by omega : 3≤q) hNewSeedRoot (mem_inN.mp hNewSeedHeadParent).1 hNewSeedReturnIn hNewSeedReturnArc hSeedStrict hSeedRows seedPair.diffuse
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherSeedTargetReach := Closure.ReturnTargetReach.native (y:=newSeedHead) dualSource (by omega : 3≤q) hNewSeedRoot (mem_inN.mp hNewSeedParent).1 hOtherSeedReturnIn hOtherSeedReturnArc hSeedStrict hSeedRows seedPair.diffuse
    all_goals if_ch_fact hKeptSeedTargetReach => have hKeptCountsAtParent := Closure.ReturnTargetReach.at_parent (mem_inN.mp hNewSeedHeadParent).1 hKeptSeedTargetReach
    all_goals if_ch_fact hOtherSeedTargetReach => have hOtherCountsAtParent := Closure.ReturnTargetReach.at_parent (mem_inN.mp hNewSeedParent).1 hOtherSeedTargetReach
    all_goals if_ch_fact hKeptSeedTargetReach => have hKeptSelectedCycles := Closure.ReturnTargetCycles.native (y:=newSeedCut) dualSource (by omega : 3≤q) hNewSeedRoot (mem_inN.mp hNewSeedHeadParent).1 hNewSeedReturnIn hNewSeedReturnArc hSeedStrict hSeedRows seedPair.diffuse hDualSub hCompleteFamily
    all_goals if_ch_fact hOtherSeedTargetReach => have hOtherSelectedCycles := Closure.ReturnTargetCycles.native (y:=newSeedHead) dualSource (by omega : 3≤q) hNewSeedRoot (mem_inN.mp hNewSeedParent).1 hOtherSeedReturnIn hOtherSeedReturnArc hSeedStrict hSeedRows seedPair.diffuse hDualSub hCompleteFamily
    all_goals if_ch_fact hOtherSeedReturnArc => have hJointRestoredReturns := hCycleRestoration ({(newSeedHead,newSeedReturn),(newSeedCut,newSeedOtherReturn)} : Finset (ℕ×ℕ))
    all_goals if_ch_fact hOtherSeedReturnArc => have hPricedMarkedLast := hOriginalLastArc (({(newSeedHead,newSeedReturn),(newSeedCut,newSeedOtherReturn)} : Finset (ℕ×ℕ)).biUnion (fun e=>Closure.MarkedCyclePeeling.col dualSource.D (Closure.FirstPacketBarrier.family dualSource) e)) (fun _ h=>by obtain ⟨_,_,c⟩:=Finset.mem_biUnion.mp h; exact (Closure.MarkedCyclePeeling.mem_col.mp c).1)
    all_goals if_ch_fact hOtherSeedReturnArc => have hActualMarkedPacketFork := hOriginalPacketFork (({(newSeedHead,newSeedReturn),(newSeedCut,newSeedOtherReturn)} : Finset (ℕ×ℕ)).biUnion (fun e=>Closure.MarkedCyclePeeling.col dualSource.D (Closure.FirstPacketBarrier.family dualSource) e)) (fun _ h=>by obtain ⟨_,_,c⟩:=Finset.mem_biUnion.mp h; exact (Closure.MarkedCyclePeeling.mem_col.mp c).1)
    all_goals if_ch_fact hOtherSeedReturnArc => have hJointRestoredAtGate := hGateRestoration ({(newSeedHead,newSeedReturn),(newSeedCut,newSeedOtherReturn)} : Finset (ℕ×ℕ))
    all_goals if_ch_fact hOtherSeedReturnArc => have hKeptLostDepth {z : ℕ} {M : Finset ℕ} := @Closure.ReturnCycleOmissions.on_cycle q dualSource.D dualSource.V dualFamily newSeedHead newSeedReturn z M (by omega : 2≤q) dualSource.free hCompleteFamily
    all_goals if_ch_fact hOtherSeedReturnArc => have hKeptSelectedLayerCost := Closure.ReturnCycleOmissions.total_budget (p:=newSeedHead) dualSource.free (fun i iv=>(hDualPPos i iv).le) (fun i iv=>(hSeedPos i iv).le) hOmittedArcBudget.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hKeptSelectedLastTwo := Closure.ReturnSuffixCover.last_two (by omega : 3≤q) dualSource.free (mem_inN.mp hNewSeedHeadParent).1 (Finset.filter_subset (fun u=>newSeedHead∉BRq2.ball (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V u 2) dualSource.V) (fun _ hu=>(Finset.mem_filter.mp hu).2) (fun i iv=>(hDualPPos i iv).le) (fun i iv=>(hSeedPos i iv).le) hOmittedArcBudget.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hKeptNativeLayerCost := Closure.ReturnCycleOmissions.total_budget (p:=newSeedHead) dualSource.free (fun i iv=>(hNativeReversePos i iv).le) (fun i iv=>(hDualXPos i iv).le) hOmittedArcBudget.2.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hKeptNativeLastTwo := Closure.ReturnSuffixCover.last_two (by omega : 3≤q) dualSource.free (mem_inN.mp hNewSeedHeadParent).1 (Finset.filter_subset (fun u=>newSeedHead∉BRq2.ball (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V u 2) dualSource.V) (fun _ hu=>(Finset.mem_filter.mp hu).2) (fun i iv=>(hNativeReversePos i iv).le) (fun i iv=>(hDualXPos i iv).le) hOmittedArcBudget.2.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherLostDepth {z : ℕ} {M : Finset ℕ} := @Closure.ReturnCycleOmissions.on_cycle q dualSource.D dualSource.V dualFamily newSeedCut newSeedOtherReturn z M (by omega : 2≤q) dualSource.free hCompleteFamily
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherSelectedLayerCost := Closure.ReturnCycleOmissions.total_budget (p:=newSeedCut) dualSource.free (fun i iv=>(hDualPPos i iv).le) (fun i iv=>(hSeedPos i iv).le) hOmittedArcBudget.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherSelectedLastTwo := Closure.ReturnSuffixCover.last_two (by omega : 3≤q) dualSource.free (mem_inN.mp hNewSeedParent).1 (Finset.filter_subset (fun u=>newSeedCut∉BRq2.ball (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V u 2) dualSource.V) (fun _ hu=>(Finset.mem_filter.mp hu).2) (fun i iv=>(hDualPPos i iv).le) (fun i iv=>(hSeedPos i iv).le) hOmittedArcBudget.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherNativeLayerCost := Closure.ReturnCycleOmissions.total_budget (p:=newSeedCut) dualSource.free (fun i iv=>(hNativeReversePos i iv).le) (fun i iv=>(hDualXPos i iv).le) hOmittedArcBudget.2.1
    all_goals if_ch_fact hOtherSeedReturnArc => have hOtherNativeLastTwo := Closure.ReturnSuffixCover.last_two (by omega : 3≤q) dualSource.free (mem_inN.mp hNewSeedParent).1 (Finset.filter_subset (fun u=>newSeedCut∉BRq2.ball (Closure.FirstPacketBarrier.graph dualSource.D dualFamily) dualSource.V u 2) dualSource.V) (fun _ hu=>(Finset.mem_filter.mp hu).2) (fun i iv=>(hNativeReversePos i iv).le) (fun i iv=>(hDualXPos i iv).le) hOmittedArcBudget.2.1
    all_goals if_ch_fact hOtherSeedTargetReach => have hFirstReturnAntichain (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.ReturnIncidenceAntichain.sponsored (by omega : 3≤q) dualSource.free dualSource.sat dualSource.separated hNewSeedRoot hp seedW seedPair.diffuse
    all_goals if_ch_fact hOtherSeedTargetReach => have hOtherReturnAntichain (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.ReturnIncidenceAntichain.sponsored (by omega : 3≤q) dualSource.free dualSource.sat dualSource.separated hNewSeedRoot (hp.trans (Finset.pair_comm _ _)) seedW seedPair.diffuse
    all_goals if_ch_fact hOtherSeedReturnArc => have hCommonHeadWithdrawal (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) (u : ℕ) := Closure.TwoParentOldWeight.native_withdrawal (u:=u) dualSource (by omega : 2≤q) hDualSmaller hNewSeedRoot hp hNewSeedReturnIn hNewSeedReturnArc hSeedPos (hSeedMass ▸ hSeedStrict) hSeedRows
    all_goals if_ch_fact hParentDeposit => have hSplitDeficit (hp : inN dualSource.D dualSource.V newSeedRoot={newSeedHead,newSeedCut}) := Closure.ParentReturnDeposit.split_deficit dualSource (by omega : 3≤q) hNewSeedRoot hp hNewSeedDifferent.symm (hSeedPos _ hNewSeedRoot) hSeedRows (hParentDeposit hp).1
    all_goals replay_ch_families
    all_goals check_ch_exits hnoCycle

end LeanCH.BR.ShenExtensionCapstone
