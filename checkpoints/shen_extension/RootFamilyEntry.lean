import checkpoints.shen_extension.GuardedDegreeFrontier
import checkpoints.shen_extension.CHFamilyWorklist
import checkpoints.shen_extension.FamilyLoopLedger
import checkpoints.shen_extension.PeriodicDebit
import checkpoints.shen_extension.MixedFragmentEscape
import checkpoints.shen_extension.HeadSlotRules

namespace LeanCH.BR.RootFamilyEntry
open CHRuleCatalog

attribute [aesop safe forward (immediate := [bad,two,window]) (rule_sets := [CHGraphFamilies])]
  OneLossCutoffDescent.descends
attribute [aesop safe forward (immediate := [b,cut,large,two]) (rule_sets := [CHGraphFamilies])]
  SATBoundaryPilot.even_bad_descends
ch_family_split_result OneLossCutoffDescent.descends
ch_family_split_result SATBoundaryPilot.even_bad_descends
ch_family_split_predicate Closure.TwoHeadRepairReplay.Missing

/-- A failed lane still supplies q distinct labels: keep the original seed,
exclude the dropped vertex from the carrier, and use the very head supplied
by the missing row. This packs the conclusion without forgetting its lane. -/
structure FreshMenu (q : ℕ) (D : CH.Digraph) (V R : Finset ℕ) (a keep drop : ℕ) : Prop where
  witness : ∃ T : Finset ℕ, ∃ row ∈ R, ∃ j ∈ BRq3.outN D (V \ {a,drop}) row,
    keep∈T ∧ j∉T ∧ (∀b∈T,D row b=false) ∧ (insert j T).card=q ∧ T⊆V \ {a,drop} ∧ row∈V

@[aesop safe forward (immediate := [lane]) (rule_sets := [CHGraphFamilies])]
theorem fresh_menu {q D V H R a keep drop price}
    (lane : Closure.TwoHeadRepairReplay.Missed q D V H R a keep drop price) :
    FreshMenu q D V R a keep drop := by
  obtain ⟨T,_,_,kept,count,checks,row,rr,miss,j,head,fresh,_,_⟩ := lane
  have reachable := rr
  rw [←checks.1.same] at reachable
  exact ⟨T,row,rr,j,head,kept,fresh,miss,(Finset.card_insert_of_notMem fresh).trans count,
    checks.1.selected,Finset.sdiff_subset (BRsub.ballSet_subset reachable)⟩

/-- Exact final inequality for the native forward merge on the same positive
row allocation. Each leaf keeps its own graph and price in the conclusion. -/
def RetainedBill (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∃U⊆V, U.card+1<V.card ∧ U.Nonempty ∧
    WeightedSD.mass U w ≤ q*WeightedSD.mass (Closure.ForwardMerge.rounds q D V w U (q-1)) w

@[aesop safe forward (immediate := [pos,unit,high,rows]) (rule_sets := [CHGraphFamilies])]
theorem merge_at_original_price {q D V w c} (pos : ∀i∈V,0<w i)
    (unit : WeightedSD.mass V w=1) (high : 1<c) (rows : ∀i∈V,WeightedSD.row q D V w i=c) :
    RetainedBill q D V w → Closure.ForwardMerge.NativeMergePays q D V := by
  rintro ⟨U,sub,room,live,bill⟩
  exact ⟨D,(fun _ _ h=>h),Or.inl ⟨U,sub,room,live,w,pos,(fun i hi=>by rw [unit,rows i hi]; exact high),bill⟩⟩

/-- A terminal descendant in the existing induction on cutoff, with its
actual chain of certified graph repairs from the input. -/
structure ReducedReach (p : Input) : Prop where
  witness : ∃c : Input,Relation.ReflTransGen Child p c ∧ Bad c ∧
    ReducedCutoff c.n c.s ∧ ¬OneLossCutoffDescent.Window c.n c.s (cutoff c)

private theorem prepend {p c : Input} (edge : Child p c) (rest : ReducedReach c) : ReducedReach p := by
  obtain ⟨t,chain,bad,cut,loss⟩ := rest.witness
  exact ⟨t,Relation.ReflTransGen.head edge chain,bad,cut,loss⟩

@[aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
theorem reduced_reach {p : Input} (bad : Bad p) : ReducedReach p := by
  suffices go : ∀k,∀x : Input,cutoff x=k → Bad x → ReducedReach x from go _ p rfl bad
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x eq bx
    obtain ⟨three,six,region⟩ := remaining_from_run x bx
    by_cases paid : OneLossCutoffDescent.Window x.n x.s (cutoff x)
    · obtain ⟨c,edge,bc,_,_,less⟩ := OneLossCutoffDescent.descends bx (by omega) paid
      exact prepend edge (ih (cutoff c) (by omega) c rfl bc)
    by_cases parity : cutoff x%2=1 ∨ cutoff x<x.s
    · have low : cutoff x≤2*x.s-7 := by
        obtain ⟨bd,seven,_,_⟩|⟨bd,_⟩ := region <;> omega
      exact ⟨x,.refl,bx,⟨low,parity⟩,paid⟩
    · obtain ⟨c,edge,bc,_,_,_,less⟩ := SATBoundaryPilot.even_bad_descends bx
        (k:=cutoff x/2) (by omega) (by omega) (by omega)
      exact prepend edge (ih (cutoff c) (by omega) c rfl bc)

/-- Run the typed rules at the arbitrary initial counterexample, before
any restriction on n, degree or cutoff. Opening the inductive certificate
then retains both the original graph and the certified descendant. -/
theorem from_root (remaining : ∀root : Input,Bad root → ∀c : Input,
    Relation.ReflTransGen Child root c → Bad c → ReducedCutoff c.n c.s →
    ¬OneLossCutoffDescent.Window c.n c.s (cutoff c) →
    CH.HasDirectedCycleAtMost c.D c.n (cutoff c)) : CH.CaccettaHaggkvistConjecture := by
  intro n r D hn hr loop degree
  by_contra missing
  replay_ch_typed_families
  have start : Bad ⟨n,r,D⟩ := by assumption
  have reached : ReducedReach ⟨n,r,D⟩ := by assumption
  obtain ⟨c,chain,bc,cut,loss⟩ := reached.witness
  replay_ch_typed_families
  exact bc.missing (remaining ⟨n,r,D⟩ start c chain bc cut loss)

#print axioms reduced_reach
#print axioms from_root
#print axioms fresh_menu
#print axioms merge_at_original_price
end LeanCH.BR.RootFamilyEntry
