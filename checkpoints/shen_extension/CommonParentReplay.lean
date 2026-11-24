import checkpoints.shen_extension.CommonParentHeadRepair

namespace LeanCH.BR.Closure.CommonParentReplay
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights CommonParentHeadRepair

structure State where
  carrier : Finset ℕ
  heads : Finset ℕ
  weights : ℕ→ℚ

noncomputable def ball (q : ℕ) (D : CH.Digraph) (H W : Finset ℕ) := BRsub.ballSet D W H (q-2)

structure Valid (q : ℕ) (D : CH.Digraph) (H R U : Finset ℕ) (s : State) : Prop where
  inside : s.carrier⊆U
  keeps : H⊆s.carrier
  selected : s.heads⊆s.carrier
  positive : ∀i∈s.carrier,0<s.weights i
  heavy : mass s.carrier s.weights<q*mass H s.weights
  same : ball q D H s.carrier=R

/-- Either rule may follow either rule. An exterior cut retains the selected heads. -/
inductive Edge (q : ℕ) (D : CH.Digraph) (H : Finset ℕ) : State → State → Prop where
  | repair {W K L w z} (step : CommonParentHeadRepair.Step q D W H (K,w) (L,z)) :
      Edge q D H ⟨W,K,w⟩ ⟨W,L,z⟩
  | cut {W K w X} (live : X.Nonempty) (outside : X⊆W\ball q D H W)
      (keep : K⊆W\X) : Edge q D H ⟨W,K,w⟩ ⟨W\X,K,w⟩

theorem carry {q D H R U s t} (v : Valid q D H R U s) (edge : Edge q D H s t) :
    Valid q D H R U t ∧ t.carrier.card-t.heads.card<s.carrier.card-s.heads.card := by
  cases edge with
  | @repair W K L w z pay =>
    obtain ⟨_,pos,heavy,_,_,_,_,_,k,kr,fresh,add⟩ := pay
    change L=insert k K at add
    subst L
    have ss : insert k K⊆W := insert_subset (mem_outN.mp kr).1 v.selected
    have sz := card_insert_of_notMem fresh
    have count := card_le_card ss
    exact ⟨⟨v.inside,v.keeps,ss,pos,heavy,v.same⟩,by dsimp at sz count ⊢; omega⟩
  | @cut W K w X live outside keep =>
    have hs : H⊆W\X := by
      intro h hh
      refine mem_sdiff.mpr ⟨v.keeps hh,?_⟩
      intro hx
      exact (mem_sdiff.mp (outside hx)).2
        (BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨v.keeps hh,0,Nat.zero_le _,.refl _⟩⟩)
    have m : mass (W\X) w≤mass W w :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i iu _ => (v.positive i iu).le)
    have same := RankedMerge.ball_delete outside
    have proper : W\X⊂W := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,by
      obtain ⟨x,hx⟩ := live
      intro eq
      have xin : x∈W\X := by rw [eq]; exact (mem_sdiff.mp (outside hx)).1
      exact (mem_sdiff.mp xin).2 hx⟩
    have down := card_lt_card proper
    have left := card_le_card keep
    exact ⟨⟨sdiff_subset.trans v.inside,hs,keep,fun i iu=>v.positive i (mem_sdiff.mp iu).1,
      m.trans_lt v.heavy,same.trans v.same⟩,by dsimp at left ⊢; omega⟩

def Checks (q : ℕ) (D : CH.Digraph) (H R U : Finset ℕ) (t : State) : Prop :=
    Valid q D H R U t ∧
    (∃i∈R, WeightedSD.row q D t.carrier t.weights i≤mass t.carrier t.weights ∨
      ∃j∈t.carrier\R,margin q D t.carrier t.weights i j<0) ∧
    (t.heads.card+2≤q →
      ∃z : ℕ→ℚ,(∀v∈t.carrier,t.weights v≤z v) ∧ (∀v∈t.carrier,0<z v) ∧ mass t.carrier z<q*mass H z ∧
        (∀i∈t.carrier,(∃k∈t.heads,D i k=true) → Protected q D t.carrier z i) ∧
        ∃r∈R,(∀k∈t.heads,D r k=false) ∧
          (WeightedSD.row q D t.carrier z r≤mass t.carrier z ∨ ∃e∈t.carrier\R,margin q D t.carrier z r e<0))

/-- Re-test the old paired-row obstruction AND the fresh-deposit rule at every reachable state.
The first test has no selected-head cutoff. Its witness is on the original inner ball. -/
theorem replay {q n D H R U s t} (hq : 2≤q) (free : QFree D U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n) (hl : H.Nonempty)
    (start : Valid q D H R U s) (path : Relation.ReflTransGen (Edge q D H) s t) :
    Checks q D H R U t := by
  have now : Valid q D H R U t := by
    induction path with
    | refl => exact start
    | tail _ edge ih => exact (carry ih edge).1
  have cap := card_le_card now.inside
  have fits : t.carrier.card+1<n := by omega
  have same := now.same
  unfold ball at same
  obtain ⟨i,ir,_,fail⟩ := RankedMerge.pair_obstruction hq (free.mono_set now.inside) small fits now.keeps
    hl t.weights now.positive now.heavy
  rw [same] at ir fail
  refine ⟨now,⟨i,ir,?_⟩,?_⟩
  · exact fail.imp_right (fun ⟨j,jr,low⟩ => ⟨j,jr,sub_neg.mpr low⟩)
  · intro limit
    simpa only [same] using next_blocker hq (free.mono_set now.inside) small fits now.keeps hl
      now.selected limit t.weights now.positive

#print axioms carry
#print axioms replay
end LeanCH.BR.Closure.CommonParentReplay
