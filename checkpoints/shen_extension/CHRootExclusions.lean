import checkpoints.shen_extension.CommonTensorClosure
import checkpoints.shen_extension.DotTwoPassShellTransport_20261117
import checkpoints.shen_extension.DotFourthStripClosure_20261118
import checkpoints.shen_extension.FourthStripFlat
import checkpoints.shen_extension.FifthStripMixedClone
import checkpoints.shen_extension.SixthStripTraffic
import checkpoints.shen_extension.CumulativeDeficitTensor
import checkpoints.shen_extension.CutReturnIncidence
import checkpoints.shen_extension.TransitionGraph
import checkpoints.shen_extension.ReachTransition
import checkpoints.shen_extension.PunctureFrontier
import checkpoints.shen_extension.SingletonSecondNeighbors
import checkpoints.shen_extension.FiveParentEndpoint
import checkpoints.shen_extension.CenterTableTransition
import checkpoints.shen_extension.WeightedColumnEscape
import LeanCH.BR.BRq5All
import LeanCH.BR.BR96
import LeanCH.BR.Triangle24

namespace LeanCH.BR.CHRootExclusions
open BRq2 BRq3 BR45 ShenFirstStrip

inductive Gate where
  | regularCore
  | bankLaw
  | reachTree
  | circle
  | splitTree
  | oneUnmatched
  | centerTable
  | buffer
  | halfBall
  | triangle24
  | nonedgeRatio
  | pressure
  | pairTest
  | markedFan
  | sharedHeads
  | bankCap
  | localBank
  | lowDegree
  | degreeSix
  | thirdStrip
  | fourthLow
  | fourthFull
  | fourthBelow
  | fifthFull
  | sixthFull
  | fifthLow
  | fifthHigher
  | fifthTensor
  | cumulative
  | variableWindow
  | paidWindow
  deriving DecidableEq, Repr, Inhabited

def gates : List Gate := [.regularCore, .bankLaw, .reachTree, .circle, .splitTree, .oneUnmatched, .centerTable, .buffer, .halfBall, .triangle24, .nonedgeRatio, .pressure, .pairTest, .markedFan, .sharedHeads, .bankCap, .localBank, .lowDegree, .degreeSix, .thirdStrip, .fourthLow, .fourthFull, .fourthBelow, .fifthFull, .sixthFull, .fifthLow, .fifthHigher, .fifthTensor, .cumulative, .variableWindow, .paidWindow]

def Holds (n s q : ℕ) (D : CH.Digraph) : Gate → Prop
  | .regularCore => ∃U⊆Finset.range n,U.Nonempty ∧ ∃d : ℕ,(d=3 ∨ d=4 ∨ d=5) ∧
      U.card≤3*d ∧ (∀i∈U,(outN D U i).card=d) ∧ (∀i∈U,(inN D U i).card=d)
  | .bankLaw => q=3 ∧ ShenPuncture.BankLaw s
  | .reachTree => ShenReachTransition.Closes n q D
  | .circle => ShenCircle.Decomposed q D (Finset.range n)
  | .splitTree => Closure.WeightedSplitInduction.Tree q D (fun _ => 1) (Finset.range n)
  | .oneUnmatched => q=3 ∧ ¬ ∃ u∈Finset.range n, ∃ v∈Finset.range n,
      Closure.ColumnBlockerEscape.Unmatched D (Finset.range n) u ∧
      Closure.ColumnBlockerEscape.Unmatched D (Finset.range n) v ∧
      outN D (Finset.range n) u≠outN D (Finset.range n) v
  | .centerTable => ∃ P : ShenCenterTable.Table q (Finset.range n),
      (∀ i<q, (P.pool i).card ≤ s) ∧ (P.misses D).card ≤ 1
  | .buffer => ∃ (P : ShenCenterTable.Table q (Finset.range n)) (p : ℕ),
      (∀ i<q, (P.pool i).card≤s) ∧ (P.misses D).card=2 ∧ p∈P.misses D ∧
      (∀ i<q, P.center i≠p) ∧ ∀ a<q, P.center a∈P.misses D →
        P.center a∈DotFullReturnCut.donors D (Finset.range n) q p (P.center (P.label p)) →
        s<(outN D (Finset.range n) (P.center a)).card ∨ (P.pool ((a+1)%q)).card<s
  | .halfBall => ∀ u∈Finset.range n, let V := Finset.range n
      let B := (ball D V u ((q-1)/2)).erase u
      QFree D B B.card ∨ ((B.card≤2*q ∨ QFree D B ((B.card+1)/2)) ∧
        ∀ x∈B,∀ y∈B,x≠y → (ShenSharedHead.commonOut D V x y).card+1<s)
  | .triangle24 => q=3 ∧ n≤24
  | .nonedgeRatio => q=3 ∧ 3*(n-1)*(n-1)≤6*(n-1)*s+7*s*s
  | .pressure => q=3 ∧ ∃ m≤s,(2*m-s)*(s-1)<2*m*(3*s+1-n) ∧
      ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u,(ShenSharedHead.commonOut D (Finset.range n) u v).card≤m
  | .pairTest => q=3 ∧ ∃ (F : CH.Digraph) (k : ℕ),(∀ x y,F x y=true → D x y=true) ∧
      OutEq s F (Finset.range n) ∧ ShenSharedHead.CheapPairOnEachActiveArc F (Finset.range n) k ∧
      (k-2)*(k-3)<2*s*(3*s+1-n)
  | .markedFan => q=3 ∧ ∃ (F : CH.Digraph) (k : ℕ),(∀ x y,F x y=true → D x y=true) ∧
      OutEq s F (Finset.range n) ∧ (k-2)*(k-3)<2*s*(3*s+1-n) ∧
      ¬ShenTransitions.MarkedFan F (Finset.range n) s k
  | .sharedHeads => q=3 ∧ ∃ F : CH.Digraph, (∀ x y,F x y=true → D x y=true) ∧
      OutEq s F (Finset.range n) ∧ (let g := 3*s+1-n; let V := Finset.range n
      2*ShenSharedHead.sharedMissing F V<n*s*(g*g+3*g) ∨
        ∃ k,2*ShenSharedHead.sharedMissing F V+k*k*ShenSharedHead.activeCount F V<
          (2*k+3)*ShenSharedHead.edges F V (ShenSharedHead.residual F V))
  | .bankCap => q=3 ∧ ∃ b≤6,(b-4)*(b-4)+b+1<s ∧
      ∀ x∈Finset.range n,∀ y∈outN D (Finset.range n) x,(ShenSharedHead.commonOut D (Finset.range n) x y).card≤b
  | .localBank => q=3 ∧ ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u,
      let T := ShenSharedHead.commonOut D (Finset.range n) u v
      QFree D T T.card
  | .lowDegree => s≤5
  | .degreeSix => s=6 ∧ 6≤q
  | .thirdStrip => q=2*s-5
  | .fourthLow => q=2*s-6 ∧ n+2≤q*s
  | .fourthFull => q=2*s-6 ∧ 12≤s
  | .fourthBelow => q=2*s-6 ∧ 8≤s ∧ n<q*s
  | .fifthFull => 59≤s ∧ q=2*s-7
  | .sixthFull => 8192≤s ∧ q=2*s-8
  | .fifthLow => 7≤s ∧ q=2*s-7 ∧ n+4≤q*s
  | .fifthHigher => 21≤s ∧ q=2*s-7 ∧ n+3≤q*s
  | .fifthTensor => 32≤s ∧ q=2*s-7 ∧ n+2≤q*s
  | .cumulative => ∃g, q+g=2*s ∧ 2≤g ∧ 35840*(g+1)^2≤s
  | .variableWindow => ∃g, q+g=2*s ∧ 1≤g ∧ 3*g≤s ∧ n+3*g*g≤q*s
  | .paidWindow => ∃g, q+g=2*s ∧ 2≤g ∧ 64*(g*g)≤s ∧ n+((g+3)/4)*g≤q*s

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

theorem excludes {n s q D} (hn : 0<n) (hs : 0<s) (hq2 : 2≤q) (hcover : n≤q*s)
    (hloop : CH.Loopless D n) (hdegree : CH.MinOutdegreeAtLeast D n s)
    (missing : ¬CH.HasDirectedCycleAtMost D n q) (g : Gate) : ¬Holds n s q D g := by
  have hq : 0<q := by omega
  have hq3 : 3≤q := by
    by_contra! low
    obtain rfl : q=2 := by omega
    exact missing (Compose.Boundary.ch_of_boundaryRegular hs (cutoff_two s) hn hcover hloop hdegree)
  have hminDegree (x) (hx : x∈Finset.range n) := Compose.FloorSix.out_card hdegree (Finset.mem_range.mp hx)
  have lowImpossible : ¬ (s≤5) := by
    intro hsmall
    apply missing
    rcases (by omega : s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5) with rfl|rfl|rfl|rfl|rfl
    · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BR45.br_q_one q hq) hn hcover hloop hdegree
    · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq2.br_q_two q hq) hn hcover hloop hdegree
    · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq3.br_q_three q hq) hn hcover hloop hdegree
    · by_cases hq4 : 4≤q
      · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq4.br_q_four q hq4) hn hcover hloop hdegree
      · have he : q=3 := by omega
        rw [he] at hcover ⊢
        exact Compose.Boundary.ch_of_boundaryRegular (by decide) BR34.br_four hn hcover hloop hdegree
    · exact Compose.Boundary.ch_of_boundaryRegular (by decide) (BRq5.br_q_five q hq) hn hcover hloop hdegree
  have hdegreeSix : 6≤s := by omega
  have hsixLow : s=6 → q≤5 := by
    rintro rfl
    by_contra! high
    exact missing (BRq6.ch_six_high_cutoff high hn hcover hloop hdegree)
  cases g with
  | regularCore =>
    simp only [Holds]
    intro hSmallRegularCore
    apply missing
    by_contra no
    obtain ⟨U,sub,live,d,small,budget,outD,inD⟩ := hSmallRegularCore
    have bound := Closure.SingletonSecondNeighbors.regular_order hq3 (qfree_of_noShort hloop no)
      sub live small outD inD
    omega
  | bankLaw =>
    simp only [Holds]
    intro hbankLaw
    apply missing
    rw [hbankLaw.1]
    exact ShenPuncture.capstone_of_bankLaw hn (by simpa only [hbankLaw.1] using hcover)
      hloop hdegree hbankLaw.2
  | reachTree =>
    simp only [Holds]
    intro hchain
    apply missing
    exact hchain.cycle hn hloop
  | circle =>
    simp only [Holds]
    intro htree
    apply missing
    exact ShenCircle.cycle_of_decomposition (by omega) hn hcover hloop hdegree htree
  | splitTree =>
    simp only [Holds]
    intro splitTree
    apply missing
    exact Closure.WeightedSplitInduction.cycle (by omega) hn hcover hloop hdegree splitTree
  | oneUnmatched =>
    simp only [Holds]
    intro hOneUnmatchedType
    apply missing
    by_contra no
    exact hOneUnmatchedType.2 (Closure.ColumnBlockerEscape.distinct_unmatched ((qfree_of_noShort hloop no).mono_bound hq3) ⟨0,Finset.mem_range.mpr hn⟩ hminDegree (by simpa only [Finset.card_range,hOneUnmatchedType.1] using hcover))
  | centerTable =>
    simp only [Holds]
    intro htable
    apply missing
    obtain ⟨P,caps,one⟩ := htable
    by_contra no
    have two := ShenCenterTable.two_missing (by omega) (qfree_of_noShort hloop no) P
      (fun i hi => hminDegree _ (P.mem i hi)) caps
    omega
  | buffer =>
    simp only [Holds]
    intro hbuffer
    apply missing
    obtain ⟨P,p,caps,two,miss,outside,buffer⟩ := hbuffer
    exact ShenCenterTable.cycle_of_buffered_centers (by omega) hloop hdegree P caps two miss outside buffer
  | halfBall =>
    simp only [Holds]
    intro hhalf
    apply missing
    exact ShenReturnCut.cycle_of_half_ball_rectangles (by omega) hn hcover hloop hdegree hhalf
  | triangle24 =>
    simp only [Holds]
    intro h24
    apply missing
    rw [h24.1] at hcover ⊢
    exact Triangle24.triangle_le_24 n s hn h24.2 hcover D hloop hdegree
  | nonedgeRatio =>
    simp only [Holds]
    intro htri
    apply missing
    rw [htri.1] at hcover ⊢
    have order : s*n≤(n-1)*s+s := by
      rw [← Nat.succ_mul,show (n-1).succ=n by omega,Nat.mul_comm s n]
    let a := n-1
    let h := 3*s-a
    have coeff : a+h=3*s := by dsimp only [h,a]; omega
    have poly := congrArg (fun z : ℕ => z*z+2*a*z) coeff
    have given : 3*a*a≤6*a*s+7*s*s := htri.2
    have quadratic : 2*s*s≤4*a*h+h*h := by nlinarith only [given,poly]
    exact ShenSharedHead.cycle_of_nonedge_ratio hs coeff quadratic hn hs order hloop hdegree
  | pressure =>
    simp only [Holds]
    intro hpressure
    apply missing
    obtain ⟨h3,m,ms,price,cap⟩ := hpressure
    rw [h3] at hcover ⊢
    exact ShenSharedHead.cycle_of_arc_pressure hn hs hcover ms price hloop hdegree cap
  | pairTest =>
    simp only [Holds]
    intro hpairTest
    apply missing
    obtain ⟨h3,F,k,sub,reg,test,price⟩ := hpairTest
    rw [h3] at hcover ⊢
    exact ShenSharedHead.cycle_of_pair_test hn hcover hloop sub reg test price
  | markedFan =>
    simp only [Holds]
    intro hnoFan
    apply missing
    obtain ⟨h3,F,k,sub,reg,price,absent⟩ := hnoFan
    rw [h3] at hcover ⊢
    by_contra no
    exact absent (ShenTransitions.trim_frontier hn hs hcover hloop no sub reg price).2.2
  | sharedHeads =>
    simp only [Holds]
    intro hshared
    apply missing
    obtain ⟨h3,F,sub,reg,small⟩ := hshared
    rw [h3] at hcover ⊢
    by_contra no
    have gap : (Finset.range n).card+(3*s+1-n)=3*s+1 := by rw [Finset.card_range]; omega
    have free := qfree_sub sub (qfree_of_noShort hloop no)
    rcases small with low|⟨k,low⟩
    · have lower := ShenSharedHead.shared_missing_lower free reg gap
      rw [Finset.card_range] at lower
      exact (Nat.not_lt_of_ge lower) low
    · exact (Nat.not_lt_of_ge (ShenSharedHead.active_reuse_budget free reg k)) low
  | bankCap =>
    simp only [Holds]
    intro hbankCap
    apply missing
    obtain ⟨h3,b,small,price,cap⟩ := hbankCap
    rw [h3] at hcover ⊢
    exact ShenReturnCut.triangle_of_arc_cap hn hs hcover hloop hdegree small price cap
  | localBank =>
    simp only [Holds]
    intro hlocal
    apply missing
    rw [hlocal.1] at hcover ⊢
    exact ShenSharedHead.cycle_of_acyclic_banks hn hs hcover hloop hdegree hlocal.2
  | lowDegree =>
    simp only [Holds]
    exact lowImpossible
  | degreeSix =>
    simp only [Holds]
    intro hsix
    apply missing
    obtain ⟨rfl,hcut⟩ := hsix
    exact BRq6.ch_six_high_cutoff hcut hn hcover hloop hdegree
  | thirdStrip =>
    simp only [Holds]
    intro hnextStrip
    apply missing
    by_contra hnoCycle
    obtain ⟨a,ha⟩ : ∃ a, s=a+6 := ⟨s-6,by omega⟩
    have hq' : q=2*a+7 := by omega
    have hf : QFree D (Finset.range n) (2*a+7) := by
      rw [← hq']
      exact qfree_of_noShort hloop hnoCycle
    have hmin : ∀ v ∈ Finset.range n, a+6≤(outN D (Finset.range n) v).card := by
      intro v hv
      rw [← ha]
      exact Compose.FloorSix.out_card hdegree (Finset.mem_range.mp hv)
    have hnear := ShenThirdStrip.order_to_top hf hmin ⟨0,Finset.mem_range.mpr hn⟩
    rw [Finset.card_range] at hnear
    have hnearBoundary : q*s≤n := by rw [hq',ha]; exact hnear
    have htopOrder : n=q*s := by omega
    have hdegreeSeven : 7≤s := by omega
    have htop : (Finset.range n).card=(2*a+7)*(a+6) := by
      rw [Finset.card_range,htopOrder,hq',ha]
    exact DotTwoPassShellTransport.third_strip_upper_false (by omega) hf hmin
      ⟨0,Finset.mem_range.mpr hn⟩ htop
  | fourthLow =>
    simp only [Holds]
    intro hfourthLow
    apply missing
    exact ShenFourthStrip.cycle_fourth_strip_below_two (by omega) hfourthLow.1 hn
      hfourthLow.2 hloop hdegree
  | fourthFull =>
    simp only [Holds]
    intro guard
    apply missing
    exact DotFourthStripClosure.cycle_fourth_strip_closed guard.2 guard.1 hn hcover hloop hdegree
  | fourthBelow =>
    simp only [Holds]
    intro guard
    apply missing
    exact ShenFourthStrip.cycle_fourth_strip_below_top guard.2.1 guard.1 hn guard.2.2 hloop hdegree
  | fifthFull =>
    simp only [Holds]
    intro hfifthClosed
    apply missing
    exact ShenFifthStrip.cycle_fifth_strip_closed hfifthClosed.1 hfifthClosed.2 hn hcover hloop hdegree
  | sixthFull =>
    simp only [Holds]
    intro hsixthClosed
    apply missing
    exact ShenSixthTraffic.cycle_sixth_strip_closed hsixthClosed.1 hsixthClosed.2 hn hcover hloop hdegree
  | fifthLow =>
    simp only [Holds]
    intro hfifthLow
    apply missing
    exact ShenFifthStrip.cycle_below_three hfifthLow.1 hfifthLow.2.1 hn
      hfifthLow.2.2 hloop hdegree
  | fifthHigher =>
    simp only [Holds]
    intro hfifthHigher
    apply missing
    exact ShenFifthStrip.cycle_below_two hfifthHigher.1 hfifthHigher.2.1 hn
      hfifthHigher.2.2 hloop hdegree
  | fifthTensor =>
    simp only [Holds]
    intro hfifthTensor
    apply missing
    exact ShenFifthStrip.cycle_below_one hfifthTensor.1 hfifthTensor.2.1 hn
      hfifthTensor.2.2 hloop hdegree
  | cumulative =>
    simp only [Holds]
    rintro ⟨g,eq,pos,fit⟩
    exact missing (ShenCumulativeDeficit.cycle_in_window eq pos fit hn hcover hloop hdegree)
  | variableWindow =>
    simp only [Holds]
    rintro ⟨g,eq,pos,fit,ord⟩
    exact missing (ShenVariableCutoff.cycle_in_variable_window eq pos fit hn ord hloop hdegree)
  | paidWindow =>
    simp only [Holds]
    rintro ⟨g,eq,pos,fit,ord⟩
    exact missing (ShenVariablePaid.cycle_in_window eq pos fit hn ord hloop hdegree)

#print axioms excludes
end LeanCH.BR.CHRootExclusions
