import checkpoints.shen_extension.CommonTensorClosure
import checkpoints.shen_extension.PunctureFrontier
import checkpoints.shen_extension.GlobalFamilyDual
import checkpoints.shen_extension.EndpointPrivateRows
import checkpoints.shen_extension.LastArcCompetitor
import checkpoints.shen_extension.LastArcMenuPayment
import checkpoints.shen_extension.AttachmentLaws
import checkpoints.shen_extension.CHRootExclusions

namespace LeanCH.BR.CHRuleCatalog
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open Finset BRq2 BRq3 BR45 WeightedSD Closure.ShortestCycleWeights

structure Input where
  n : ℕ
  s : ℕ
  D : CH.Digraph

def cutoff (c : Input) := CH.ceilDiv c.n c.s

def RemainingOrders (c : Input) : Prop :=
  let n := c.n
  let s := c.s
  let q := cutoff c
  3≤q ∧ 6≤s ∧
    ((q=2*s-6 ∧ 7≤s ∧ s≤11 ∧ (n=q*s ∨ s=7 ∧ n+1=q*s)) ∨
      (q≤2*s-7 ∧ (59≤s → q≤2*s-8) ∧ (8192≤s → q≤2*s-9)))

structure Bad (c : Input) : Prop where
  order : 0<c.n
  degree_pos : 0<c.s
  loopless : CH.Loopless c.D c.n
  degree : CH.MinOutdegreeAtLeast c.D c.n c.s
  missing : ¬CH.HasDirectedCycleAtMost c.D c.n (cutoff c)

/-- A literal CH child supplies its own degree/order data and a cycle pullback.
Weighted states have a different type and use CommonParentReplay instead. -/
structure Child (p c : Input) : Prop where
  order : 0<c.n
  degree_pos : 0<c.s
  loopless : CH.Loopless c.D c.n
  degree : CH.MinOutdegreeAtLeast c.D c.n c.s
  pullback : CH.HasDirectedCycleAtMost c.D c.n (cutoff c) →
    CH.HasDirectedCycleAtMost p.D p.n (cutoff p)

theorem bad_child {p c} (b : Bad p) (e : Child p c) : Bad c :=
  ⟨e.order,e.degree_pos,e.loopless,e.degree,fun hit=>b.missing (e.pullback hit)⟩

theorem bad_descendant {p c} (b : Bad p) (path : Relation.ReflTransGen Child p c) : Bad c := by
  induction path with
  | refl => exact b
  | tail _ e ih => exact bad_child ih e

/-- An existing reach transformation is an entry to the full root catalog again
whenever the transformed graph meets its own CH degree bound. -/
theorem reach_child {p : Input} (b : Bad p) (s k : ℕ) (radius potential : ℕ→ℕ)
    (hs : 0<s) (hk : 0<k) (eq : CH.ceilDiv p.n s=k) (bounds : ∀x∈range p.n,radius x≤cutoff p)
    (degree : CH.MinOutdegreeAtLeast (ShenReachTransition.nextGraph p.D (range p.n)
      (cutoff p) k radius potential) p.n s) :
    Child p ⟨p.n,s,ShenReachTransition.nextGraph p.D (range p.n) (cutoff p) k radius potential⟩ := by
  refine ⟨b.order,hs,ShenReachTransition.next_loopless p.D p.n (cutoff p) k radius potential,degree,?_⟩
  intro hit
  dsimp [cutoff] at hit
  rw [eq] at hit
  exact ShenReachTransition.pullback b.loopless bounds hk hit

/-- Reapply the terminal rule on every actual repair trace in an arc restriction
of the selected least source. All weights and head labels remain arguments. -/
def EndpointRuns {q m} (X : Model q m) : Prop :=
  ∀E : CH.Digraph,(∀i j,E i j=true → X.D i j=true) →
  ∀U⊆X.V,U.card+1<X.V.card → ∀H⊆U,H.Nonempty →
  ∀w : ℕ→ℚ,(∀x∈X.V,0<w x) → mass U w<q*mass H w →
  ∀i∈BRsub.ballSet E U H (q-2),∀k∈outN E U i,∀l z T v,
    Closure.CommonParentHeadRepair.Step q E U H ({k},w) (insert l {k},z) →
    Relation.ReflTransGen (Closure.CommonParentHeadRepair.Step q E U H) (insert l {k},z) (T,v) →
    T.card+1=q → (∀r∈BRsub.ballSet E U H (q-2),(outN E U r).Nonempty) →
    Closure.CommonParentEndpointReplay.Fork q E X.V U H (BRsub.ballSet E U H (q-2)) T w v ∧
      Closure.EndpointPrivateRows.Tests q E U H (BRsub.ballSet E U H (q-2)) T v

/-- Each family is a proposition about one fixed arbitrary original input.
Universal carriers denote all induced subgraphs; existential sources keep their witnesses bundled. -/
inductive Family where
  | counterexample | inputBounds | forwardFree | reverseFree | forwardInduced | reverseInduced
  | smallInduced | replayChildren | shenWindow | shenExcluded | punctureSource | leastSource | pairExcluded | contradiction
  | guard (g : CHRootExclusions.Gate) | excluded (g : CHRootExclusions.Gate)
  | descendantExclusions
  | remainingOrders | endpointChildren | nativeSeedLanes | nativeSeedFrontier | nativeSeedReroot | nativeForcedMiss | nativeFreshCuts | nativeTargetReach | cycleRestorations | lastArcExchange | originalPacketCompetitor
  | collisionPayment | attachmentLaws
  deriving DecidableEq, Repr, Inhabited

private def collisionLaws {q n : ℕ} (X : Model q n) : Prop :=
  Closure.TwoHeadForcedMiss.Outcome X ∧ Closure.MissedFreshCut.OnModel X ∧ Closure.ReturnTargetReach.OnModel X ∧
  Closure.OmittedCycleProgress.OnModel X ∧ Closure.LastArcGatePayment.OnModel X ∧ Closure.LastArcCompetitor.OnModel X ∧
  Closure.LastArcMergePayment.OnModel X ∧ Closure.LastArcReturnMenu.OnModel X ∧
  (∀ F, Closure.LastArcHeadDeposit.OnFamily X F) ∧ ∀ F, Closure.LastArcMenuPayment.OnFamily X F

def Meaning (c : Input) : Family → Prop
  | .counterexample => Bad c
  | .inputBounds => Bad c ∧ 2≤cutoff c ∧ c.n≤cutoff c*c.s
  | .forwardFree => QFree c.D (range c.n) (cutoff c)
  | .reverseFree => QFree (fun i j => c.D j i) (range c.n) (cutoff c)
  | .forwardInduced => ∀U⊆range c.n,QFree c.D U (cutoff c)
  | .reverseInduced => ∀U⊆range c.n,QFree (fun i j => c.D j i) U (cutoff c)
  | .shenWindow => 2*c.s-4≤cutoff c
  | .shenExcluded => ¬2*c.s-4≤cutoff c
  | .punctureSource => 2≤cutoff c ∧ ∃X : Model (cutoff c) c.n,Closure.PunctureFrontier.Conditions X
  | .leastSource => 2≤cutoff c ∧ ∃ m, ∃ X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card
  | .pairExcluded => ∃ m, ∃ X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧
      ¬Closure.RankedMerge.PairPays (cutoff c) X.D X.V
  | .smallInduced => ∀U⊆range c.n,U.card≤cutoff c+2 →
      SmallRow (cutoff c) c.D U ∧ SmallRow (cutoff c) (fun i j=>c.D j i) U
  | .replayChildren => ∃ m,∃ X : Model (cutoff c) m, ∀U⊆X.V,U.card+1<X.V.card →
      ∀H : Finset ℕ,H.Nonempty → ∀R s t,Closure.CommonParentReplay.Valid (cutoff c) X.D H R U s →
      Relation.ReflTransGen (Closure.CommonParentReplay.Edge (cutoff c) X.D H) s t →
      Closure.CommonParentReplay.Checks (cutoff c) X.D H R U t
  | .contradiction => False
  | .guard g => CHRootExclusions.Holds c.n c.s (cutoff c) c.D g
  | .excluded g => ¬CHRootExclusions.Holds c.n c.s (cutoff c) c.D g
  | .descendantExclusions => ∀d,Relation.ReflTransGen Child c d → ∀g,
      ¬CHRootExclusions.Holds d.n d.s (cutoff d) d.D g
  | .endpointChildren => ∃m,∃X : Model (cutoff c) m,EndpointRuns X
  | .nativeSeedLanes => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧ Closure.TwoHeadRepairLanes.NativeResult X
  | .nativeSeedFrontier => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧ Closure.TwoHeadRepairReplay.Outcome X
  | .nativeSeedReroot => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧ Closure.TwoHeadRepairReroot.Result X
  | .nativeForcedMiss => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧ Closure.TwoHeadForcedMiss.Outcome X
  | .nativeFreshCuts => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧
      Closure.TwoHeadForcedMiss.Outcome X ∧ Closure.MissedFreshCut.OnModel X
  | .nativeTargetReach => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧
      Closure.TwoHeadForcedMiss.Outcome X ∧ Closure.MissedFreshCut.OnModel X ∧ Closure.ReturnTargetReach.OnModel X
  | .cycleRestorations => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧
      Closure.TwoHeadForcedMiss.Outcome X ∧ Closure.MissedFreshCut.OnModel X ∧ Closure.ReturnTargetReach.OnModel X ∧
      Closure.OmittedCycleProgress.OnModel X
  | .lastArcExchange => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧
      Closure.TwoHeadForcedMiss.Outcome X ∧ Closure.MissedFreshCut.OnModel X ∧ Closure.ReturnTargetReach.OnModel X ∧
      Closure.OmittedCycleProgress.OnModel X ∧ Closure.LastArcGatePayment.OnModel X
  | .originalPacketCompetitor => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,SmallerSmallRow (cutoff c) X.V.card ∧
      Closure.TwoHeadForcedMiss.Outcome X ∧ Closure.MissedFreshCut.OnModel X ∧ Closure.ReturnTargetReach.OnModel X ∧
      Closure.OmittedCycleProgress.OnModel X ∧ Closure.LastArcGatePayment.OnModel X ∧ Closure.LastArcCompetitor.OnModel X
  | .collisionPayment => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,
      SmallerSmallRow (cutoff c) X.V.card ∧ collisionLaws X
  | .attachmentLaws => 3≤cutoff c ∧ ∃m,∃X : Model (cutoff c) m,
      SmallerSmallRow (cutoff c) X.V.card ∧ collisionLaws X ∧ Closure.AttachmentLaws.OnModel X
  | .remainingOrders => RemainingOrders c

structure Rule where
  name : String
  source : Family
  target : Family
  extra : List Family
  sound : ∀ c,Meaning c source → (∀p∈extra,Meaning c p) → Meaning c target

private def unary (label : String) (a b : Family) (f : ∀c,Meaning c a → Meaning c b) : Rule :=
  ⟨label,a,b,[],fun c h _=>f c h⟩

private def ordersRule : Rule :=
  ⟨"derive the two surviving numeric regions",.inputBounds,.remainingOrders,
   [.shenExcluded,.excluded .lowDegree,.excluded .degreeSix,.excluded .thirdStrip,
    .excluded .fourthLow,.excluded .fourthFull,.excluded .fourthBelow,.excluded .fifthFull,
    .excluded .sixthFull],fun c ⟨b,hq,ord⟩ extra=>by
    obtain ⟨n,s,D⟩ := c
    let q := cutoff (Input.mk n s D)
    have get (g) (mem : Family.excluded g∈[.shenExcluded,.excluded .lowDegree,.excluded .degreeSix,
        .excluded .thirdStrip,.excluded .fourthLow,.excluded .fourthFull,.excluded .fourthBelow,
        .excluded .fifthFull,.excluded .sixthFull]) : ¬CHRootExclusions.Holds n s q D g := extra (.excluded g) mem
    have win : ¬2*s-4≤q := extra .shenExcluded (by decide)
    have low := get .lowDegree (by decide)
    have six := get .degreeSix (by decide)
    have third := get .thirdStrip (by decide)
    have fl := get .fourthLow (by decide)
    have ff := get .fourthFull (by decide)
    have fb := get .fourthBelow (by decide)
    have fifth := get .fifthFull (by decide)
    have sixth := get .sixthFull (by decide)
    simp only [CHRootExclusions.Holds] at low six third fl ff fb fifth sixth
    have h3 : 3≤q := by
      by_contra! h
      obtain eq : q=2 := by change 2≤q at hq; omega
      have br : Compose.Boundary.BoundaryRegular 2 s := by
        apply br_of_ball (by decide)
        intro E V free reg u uv
        simp only [Nat.reduceSub,Nat.mul_one]
        have B : ball E V u 1=insert u (outN E V u) := by
          ext v; simp only [mem_ball_one uv,outN,Finset.mem_insert,Finset.mem_filter]
        rw [B,Finset.card_insert_of_notMem (fun hit => loopfree free (by decide) uv (mem_outN.mp hit).2),reg u uv]
      change n≤q*s at ord
      apply b.missing
      change CH.HasDirectedCycleAtMost D n q
      rw [eq] at ord ⊢
      exact Compose.Boundary.ch_of_boundaryRegular b.degree_pos br b.order ord b.loopless b.degree
    change n≤q*s at ord
    change 3≤q ∧ 6≤s ∧ ((q=2*s-6 ∧ 7≤s ∧ s≤11 ∧ (n=q*s ∨ s=7 ∧ n+1=q*s)) ∨
      (q≤2*s-7 ∧ (59≤s → q≤2*s-8) ∧ (8192≤s → q≤2*s-9)))
    refine ⟨h3,by omega,?_⟩
    by_cases four : q=2*s-6
    · exact Or.inl ⟨four,by omega,by omega,by omega⟩
    · exact Or.inr ⟨by omega,by omega,by omega⟩⟩

private theorem input_bounds (c : Input) (b : Bad c) : Meaning c .inputBounds := by
  have hs := b.degree_pos
  have hn := b.order
  have ord : c.n≤cutoff c*c.s := by
    have hmod := Nat.mod_lt (c.n+c.s-1) hs
    have hdiv := Nat.mod_add_div (c.n+c.s-1) c.s
    rw [Nat.mul_comm c.s] at hdiv
    dsimp [cutoff,CH.ceilDiv]
    omega
  refine ⟨b,?_,ord⟩
  by_contra! low
  have eq : cutoff c=1 := by
    rcases Nat.eq_zero_or_pos (cutoff c) with hz|hp
    · rw [hz] at ord; omega
    · omega
  have br : Compose.Boundary.BoundaryRegular 1 c.s := by
    apply br_of_ball (by decide)
    intro D V hf ho u hu
    change 1≤(ball D V u 0).card
    exact card_pos.mpr ⟨u,self_mem_ball hu⟩
  apply b.missing
  rw [eq] at ord ⊢
  exact Compose.Boundary.ch_of_boundaryRegular hs br hn ord b.loopless b.degree

/-- Add a rule by supplying its actual Lean implication. This is the default selection. -/
def rules : List Rule := [
  unary "CH input arithmetic" .counterexample .inputBounds (input_bounds),
  unary "absence of a short cycle" .counterexample .forwardFree (fun _ b=>qfree_of_noShort b.loopless b.missing),
  unary "reverse all arcs" .forwardFree .reverseFree (fun _ h=>QFree.reverse h),
  unary "reverse all arcs" .reverseFree .forwardFree (fun _ h=>QFree.reverse h),
  unary "take every induced carrier" .forwardFree .forwardInduced (fun _ h _ sub=>QFree.mono_set sub h),
  unary "take every induced carrier" .reverseFree .reverseInduced (fun _ h _ sub=>QFree.mono_set sub h),
  unary "reverse all arcs" .forwardInduced .reverseInduced (fun _ h U sub=>(h U sub).reverse),
  unary "reverse all arcs" .reverseInduced .forwardInduced (fun _ h U sub=>(h U sub).reverse),
  unary "take every induced carrier" .forwardInduced .forwardInduced (fun _ h U sub=>h U sub),
  unary "take every induced carrier" .reverseInduced .reverseInduced (fun _ h U sub=>h U sub),
  unary "exclude the Shen two-strip window" .inputBounds .shenExcluded (fun c ⟨b,hq,ord⟩ win=>
    b.missing (ShenFirstStrip.cycle_in_two_strip_window b.degree_pos (by omega) win b.order ord b.loopless b.degree)),
  unary "normalize to a puncture source" .inputBounds .punctureSource (fun _ ⟨b,hq,ord⟩=>
    ⟨hq,Closure.PunctureFrontier.from_input hq b.order ord b.loopless b.degree b.missing⟩),
  unary "select a least weighted source" .punctureSource .leastSource (fun _ ⟨hq,X,_⟩=>by
    obtain ⟨m,Y,_,small⟩ := Closure.GlobalFamilyDual.select X hq
    exact ⟨hq,m,Y,small⟩),
  unary "test the paired merge on that source" .leastSource .pairExcluded (fun _ ⟨hq,m,X,small⟩=>
    ⟨m,X,small,Closure.RankedMerge.no_pair hq X.free small⟩), 
  ⟨"small-row test on both orientations",.forwardInduced,.smallInduced,[.inputBounds,.reverseInduced],
    fun c forward extra U sub card => by
      have hb := extra .inputBounds (by decide)
      have rev := extra .reverseInduced (by decide)
      exact ⟨smallRow_of_card_le_add_two hb.2.1 (forward U sub) card,
        smallRow_of_card_le_add_two hb.2.1 (rev U sub) card⟩⟩,
  unary "retry exterior cuts and head repairs on every reachable weighted child" .leastSource .replayChildren
    (fun _ ⟨hq,m,X,small⟩ => ⟨m,X,fun _ us room _ hl _ _ _ start path =>
      Closure.CommonParentReplay.replay hq (X.free.mono_set us) small room hl start path⟩),
  ⟨"close in the Shen window",.shenWindow,.contradiction,[.shenExcluded],
    fun _ win extra=>(extra .shenExcluded (by decide)) win⟩ ] ++
  (CHRootExclusions.gates.flatMap fun g =>
    [unary ("exclude " ++ reprStr g) .inputBounds (.excluded g) (fun _ ⟨b,hq,ord⟩ =>
      CHRootExclusions.excludes b.order b.degree_pos hq ord b.loopless b.degree b.missing g),
     ⟨"close " ++ reprStr g, .guard g, .contradiction, [.excluded g],
       fun _ witness hs => (hs (.excluded g) (by simp)) witness⟩]) ++
  [unary "retry all root exclusions on every certified CH descendant" .counterexample .descendantExclusions
    (fun _ b d path g=>by
      have bd := bad_descendant b path
      have f := input_bounds d bd
      exact CHRootExclusions.excludes bd.order bd.degree_pos f.2.1 f.2.2 bd.loopless bd.degree bd.missing g),
   ordersRule,
   unary "test every q−1-head terminal trace on the least source" .leastSource .endpointChildren
    (fun _ ⟨hq,m,X,small⟩=>by
      refine ⟨m,X,?_⟩
      intro E sub U us room H hs hl w pos heavy i ir k kk l z T v first path count live
      exact Closure.EndpointPrivateRows.on_trace hq (qfree_sub sub X.free) us small room hs hl
        pos heavy ir kk first path count live),
   ⟨"start opposed native repairs from one paying row",.leastSource,.nativeSeedLanes,[.remainingOrders],
     fun _ ⟨_,m,X,small⟩ extra=>by
       have q3 := (extra .remainingOrders (by decide)).1
       exact ⟨q3,m,X,small,Closure.TwoHeadRepairLanes.native X q3 small⟩⟩,
   unary "replay both labelled repairs and compare their endpoints" .nativeSeedLanes .nativeSeedFrontier
     (fun _ ⟨q3,m,X,small,lanes⟩=>⟨q3,m,X,small,Closure.TwoHeadRepairReplay.on_native X q3 lanes⟩),
   unary "reroot every double cover and replay at a root without a dead parent" .nativeSeedFrontier .nativeSeedReroot
     (fun _ ⟨q3,m,X,small,out⟩=>⟨q3,m,X,small,Closure.TwoHeadRepairReroot.on_frontier X q3 small out⟩),
   unary "retain both seeds and replay the reroot cut on a parent distinguished by the return" .nativeSeedReroot .nativeForcedMiss
     (fun _ ⟨q3,m,X,small,prior⟩=>⟨q3,m,X,small,Closure.TwoHeadForcedMiss.on_frontier X q3 small prior⟩),
   unary "replay fresh cuts to their common carrier and count the surviving inner heads" .nativeForcedMiss .nativeFreshCuts
     (fun _ ⟨q3,m,X,small,prior⟩=>⟨q3,m,X,small,prior,Closure.MissedFreshCut.on_model X q3 small⟩),
   unary "carry distinct neutral targets through the actual return and replay later row quotas" .nativeFreshCuts .nativeTargetReach
     (fun _ ⟨q3,m,X,small,old,cuts⟩=>⟨q3,m,X,small,old,cuts,Closure.ReturnTargetReach.on_model X q3⟩),
   unary "restore missing marked cycles to one selected graph until every designated arc column is complete" .nativeTargetReach .cycleRestorations
     (fun _ ⟨q3,m,X,small,old,cuts,reach⟩=>⟨q3,m,X,small,old,cuts,reach,Closure.OmittedCycleProgress.on_model X (by omega) small⟩),
   unary "reprice the final restored arc at the original attachment and test an exchange on its original labels" .cycleRestorations .lastArcExchange
     (fun _ ⟨q3,m,X,small,old,cuts,reach,restore⟩=>⟨q3,m,X,small,old,cuts,reach,restore,Closure.LastArcGatePayment.on_model X (by omega) small⟩),
   unary "find an original boundary cycle that keeps the packet or exchanges one identified arc" .lastArcExchange .originalPacketCompetitor
     (fun _ ⟨q3,m,X,small,old,cuts,reach,restore,price⟩=>⟨q3,m,X,small,old,cuts,reach,restore,price,Closure.LastArcCompetitor.on_model X (by omega) small⟩),
   unary "exclude a full packet and pay from a common return menu when it covers the expensive columns" .originalPacketCompetitor .collisionPayment
     (fun _ ⟨q3,m,X,small,old,cuts,reach,restore,price,fork⟩=>
       ⟨q3,m,X,small,old,cuts,reach,restore,price,fork,Closure.LastArcMergePayment.on_model X (by omega) small,
        Closure.LastArcReturnMenu.on_model X q3,Closure.LastArcHeadDeposit.on_model X (by omega),
        Closure.LastArcMenuPayment.on_model X q3⟩),
   unary "close all-old cycles and locate a double receiver for every failed attachment"
     .collisionPayment .attachmentLaws
     (fun _ ⟨q3,m,X,small,laws⟩ =>
       ⟨q3,m,X,small,laws,Closure.AttachmentLaws.on_model X (by omega)⟩)]

structure Event where
  atFamily : Family
  rule : String
  outcome : String
  target : Family
  deriving Repr

structure Report where
  seen : List Family
  pending : List Family
  log : List Event

private def visit (catalog : List Rule) (f : Family) (r : Report) : Report :=
  catalog.foldl (fun acc entry =>
    if ¬(f∈entry.source::entry.extra ∧ entry.source∈acc.seen ∧ ∀p∈entry.extra,p∈acc.seen) then
      { acc with log := ⟨f,entry.name,"premise absent or other input family",entry.target⟩::acc.log }
    else if entry.target∈acc.seen then
      { acc with log := ⟨f,entry.name,"already reached",entry.target⟩::acc.log }
    else
      ⟨entry.target::acc.seen,acc.pending++[entry.target],⟨f,entry.name,"reached",entry.target⟩::acc.log⟩) r

private def drain (catalog : List Rule) : ℕ → Report → Report
  | 0,r => r
  | fuel+1,r => match r.pending with
    | [] => r
    | f::fs => drain catalog fuel (visit catalog f {r with pending:=fs})

def runFrom (catalog : List Rule) (seeds : List Family) (fuel : ℕ := catalog.length + seeds.length) : Report :=
  drain catalog fuel ⟨seeds,seeds,[]⟩

def run (catalog : List Rule) (fuel : ℕ := catalog.length + 1) : Report :=
  runFrom catalog [.counterexample] fuel

private def Holds (c : Input) (r : Report) : Prop :=
  (∀f∈r.seen,Meaning c f) ∧ ∀f∈r.pending,Meaning c f

private theorem visit_sound {c r f} (cat : List Rule) (h : Holds c r) :
    Holds c (visit cat f r) := by
  unfold visit
  induction cat generalizing r with
  | nil => exact h
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · rename_i eq
      have ready := Classical.not_not.mp eq
      have hit : Meaning c e.target := e.sound c (h.1 _ ready.2.1) (fun p hp => h.1 _ (ready.2.2 p hp))
      split
      · exact h
      · constructor
        · intro v hv
          rcases List.mem_cons.mp hv with rfl|old
          · exact hit
          · exact h.1 _ old
        · intro v hv
          rcases List.mem_append.mp hv with old|new
          · exact h.2 _ old
          · exact (List.mem_singleton.mp new) ▸ hit

private theorem drain_sound {c} (cat : List Rule) (fuel) (r) (h : Holds c r) :
    Holds c (drain cat fuel r) := by
  induction fuel generalizing r with
  | zero => exact h
  | succ n ih =>
    cases pq : r.pending with
    | nil => simpa [drain,pq] using h
    | cons f fs =>
      rw [drain,pq]
      apply ih
      apply visit_sound
      · exact ⟨h.1,fun y hy=>h.2 y (pq ▸ List.mem_cons_of_mem _ hy)⟩

/-- Every supplied fact must hold on the same original input. -/
theorem runFrom_sound (c : Input) (seeds : List Family) (start : ∀f∈seeds,Meaning c f)
    (cat : List Rule) (fuel : ℕ) : ∀f∈(runFrom cat seeds fuel).seen,Meaning c f :=
  (drain_sound cat fuel _ ⟨start,start⟩).1

/-- Machine-produced discoveries are sound for the actual hypothetical CH input. -/
theorem run_sound (c : Input) (bad : Bad c) (cat : List Rule) (fuel : ℕ) :
    ∀f∈(run cat fuel).seen,Meaning c f := by
  apply runFrom_sound
  intro f hf
  obtain rfl := List.mem_singleton.mp hf
  exact bad

/-- A fixed point can leave the literal contradiction family unreached. -/
def Report.closed (r : Report) (catalog : List Rule) : Bool :=
  r.pending.isEmpty && catalog.all (fun e =>
    !(r.seen.contains e.source && e.extra.all r.seen.contains) || r.seen.contains e.target)

theorem replay_at_descendant {p c} (b : Bad p) (path : Relation.ReflTransGen Child p c)
    (catalog : List Rule) : ∀f∈(run catalog).seen,Meaning c f :=
  run_sound c (bad_descendant b path) catalog _

theorem default_finished : (run rules).closed rules=true ∧ Family.contradiction∉(run rules).seen := by decide

theorem attachment_laws_reached : Family.attachmentLaws ∈ (run rules).seen := by decide

private theorem gates_reached : CHRootExclusions.gates.all
    (fun g => (run rules).seen.contains (.excluded g)) = true := by decide

theorem exclusion_from_run (c : Input) (b : Bad c) (g : CHRootExclusions.Gate) :
    ¬CHRootExclusions.Holds c.n c.s (cutoff c) c.D g := by
  apply run_sound c b rules _ (.excluded g)
  have member : g∈CHRootExclusions.gates := by cases g <;> decide
  simpa using List.all_eq_true.mp gates_reached g member

theorem remaining_from_run (c : Input) (b : Bad c) : RemainingOrders c :=
  run_sound c b rules (rules.length+1) .remainingOrders (by decide)

#print axioms remaining_from_run
#print axioms replay_at_descendant
#print axioms exclusion_from_run

theorem shen_window_closes (c : Input) (b : Bad c) (win : Meaning c .shenWindow) : False := by
  let seeds : List Family := [.counterexample,.shenWindow]
  apply runFrom_sound c seeds (fun f hf=>by
    change f∈[Family.counterexample,Family.shenWindow] at hf
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl
    · exact b
    · exact win) rules 32 Family.contradiction
  decide

-- Reordering the catalog must still wake the multi-premise rules.
example : (run rules.reverse).closed rules.reverse=true ∧ Family.smallInduced∈(run rules.reverse).seen := by decide

#print axioms run_sound
#print axioms shen_window_closes
end LeanCH.BR.CHRuleCatalog
