import checkpoints.shen_extension.PunctureCycleLoop
import checkpoints.shen_extension.WeightedSplitInduction

namespace LeanCH.BR.Closure.PunctureFrontier
open Finset BRq2 BRq3 BR45 DeficitLevels ShortestCycleClasses ShortestCycleWeights

structure Conditions {q n} (X : Model q n) : Prop where
  arcs : ∀x∈X.V,∀y∈X.V,X.D x y=true → ∃M,ShenCycleSuccessor.Cycle X.D X.V q M ∧ x∈M ∧ y∈M
  cuts : ∀r L B,insert r (L∪B)=X.V → Disjoint L B → r∉L → r∉B → L.Nonempty → B.Nonempty →
    (∃a∈L, ¬WeightedOneVertexSplit.paid q X.D X.weights B a) ∨
    (∃b∈B, ¬WeightedOneVertexSplit.paid q X.D X.weights L b)
  incidence : ∀h∈X.V, (∀x∈X.V,X.weights h≤X.weights x) → ∀M,
    ShenCycleSuccessor.Cycle X.D (X.V\{h}) q M →
    X.V.card≤q*(inN X.D M h).card ∨ ∃z∈(X.V\{h})\M,2≤(inN X.D M z).card
  dual : ∀h∈X.V,∀y : ℕ→ℚ, (∀x∈X.V.erase h,0≤y x) → (∃x∈X.V.erase h,0<y x) →
    ¬PunctureDualExtension.PairBudget q X.D (X.V.erase h) h y
  pairs : q=3 → ∀x∈X.V,∀y∈X.V,x≠y →
    ∃M,ShenCycleSuccessor.Cycle X.D X.V 3 M ∧ x∈M ∧ y∈M
  recurrent : q=3 → 13≤X.V.card → ∀h∈X.V, (∀x∈X.V,X.weights h≤X.weights x) →
    ∃(f : ℕ→Finset ℕ) (l : ℕ), 2≤l ∧ f l=f 0 ∧ ∀i,
      ShenCycleSuccessor.Cycle X.D (X.V\{h}) 3 (f i) ∧ PunctureCycleLoop.Step X.D (f i) (f (i+1))
  puncture : q=3 → ∃h∈X.V, (∀x∈X.V,X.weights h≤X.weights x) ∧
    ∃r∈X.V,X.D r h=true ∧ carrier X.D (X.V\{h}) 3 r=X.V\{h}

theorem from_input {q n s D} (hq : 2≤q) (hn : 0<n) (ord : n≤q*s)
    (loop : CH.Loopless D n) (deg : CH.MinOutdegreeAtLeast D n s)
    (no : ¬CH.HasDirectedCycleAtMost D n q) : ∃X : Model q n, Conditions X := by
  obtain ⟨X⟩ := normalize hq hn ord loop deg no
  refine ⟨X,fun _ xv _ yv => edge_cycle X hq xv yv,fun _ _ _ => WeightedOneVertexSplit.cross_row X hq,
    fun _ hv m _ => MinimumPunctureIncidence.receiver X hq hv m,?_,?_,?_,?_⟩
  · intro h hv y yn pos pay
    have same := insert_erase hv
    apply PunctureDualExtension.excludes hq (notMem_erase h X.V)
      (Bool.eq_false_iff.mpr (loopfree X.free (by omega) hv)) yn pos pay
      (fun x => (X.weights x : ℚ)) (fun _ _ => Nat.cast_nonneg _)
    rw [same]
    exact X.strict
  · rintro rfl x xv y yv ne
    exact pair_four X xv yv ne
  · rintro rfl large h hv m
    exact PunctureCycleLoop.loop X large hv m
  · rintro rfl
    exact TriangleMinimumPuncture.puncture_exists X

theorem saturated_from_input {base D V s} (hb : 2≤base) (safe : QFree D V base)
    (live : V.Nonempty) (ord : V.card≤base*s) (deg : ∀x∈V,s≤(outN D V x).card) :
    ∃q d, d+1≤s ∧ ∃S : Origin q (d+1), CutoffDegreeRank.Ranked base q (d+1) S.V.card ∧
      BRsub.Sat q S.G S.V ∧ ∀x∈S.V,carrier S.G S.V q x=S.V := by
  obtain ⟨q,d,le,O,_,loop,_⟩ := CycleClassFrontier.from_input hb safe live ord deg
  obtain ⟨S,eq,sat,_,one⟩ := SaturatedCycleClasses.saturated_origin O (hb.trans loop.ranked.1)
  exact ⟨q,d,le,S,eq.symm ▸ loop.ranked,sat,one⟩

#print axioms from_input
#print axioms saturated_from_input
end LeanCH.BR.Closure.PunctureFrontier
