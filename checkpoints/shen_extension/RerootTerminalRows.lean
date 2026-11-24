import checkpoints.shen_extension.OneParentReroot

namespace LeanCH.BR.Closure.RerootTerminalRows
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity
open TwoHeadRepairLanes TwoHeadRepairReplay

def Misses (E : CH.Digraph) (r : ℕ) (T : Finset ℕ) : Prop := ∀k∈T,E r k=false

/-- If a return from an exterior seed enters T, following selected heads
reaches an inner sink, or a different exterior sink. Returning to the seed
itself would close a walk of at most q arcs. -/
theorem return_sink {q E U R T p t} (free : QFree E U q) (ts : T⊆U)
    (size : T.card<q) (tv : t∈U) (pt : E p t=true) (enters : ∃k∈T,E t k=true) :
    (∃i∈T∩R,Misses E i T) ∨ ∃s∈T\R,s≠p ∧ Misses E s T := by
  obtain ⟨k,kt,tk⟩ := enters
  obtain ⟨s,st,sink,m,len,path⟩ := reach_sink_of_card (free.mono_set ts) size.le kt
  have quiet : Misses E s T := fun i it=>Bool.eq_false_iff.mpr (sink i it)
  by_cases sr : s∈R
  · exact Or.inl ⟨s,mem_inter.mpr ⟨st,sr⟩,quiet⟩
  · refine Or.inr ⟨s,mem_sdiff.mpr ⟨st,sr⟩,?_,quiet⟩
    rintro rfl
    exact free s (m+1+1) (by omega) (by omega) (.step tv pt (.step (ts kt) tk (path.mono ts)))

/-- Two exterior selected heads leave too few inner labels for a selected
path from H to reach the exterior before it runs into an inner sink. -/
theorem two_exterior {q E U H R T} (hq : 3≤q) (free : QFree E U q) (ts : T⊆U)
    (size : T.card<q) (same : R=BRsub.ballSet E U H (q-2))
    (two : 2≤(T\R).card) {h k} (hh : h∈H) (kt : k∈T) (hk : E h k=true) :
    ∃i∈T∩R,Misses E i T := by
  have bound := card_sdiff_add_card_inter T R
  have kr : k∈R := same ▸ BRsub.mem_ballSet.mpr
    ⟨h,hh,ball_mono_radius (by omega : 1≤q-2) (ball_of_adj (ts kt) hk)⟩
  have sub : T∩R⊆U := inter_subset_left.trans ts
  obtain ⟨i,it,sink,m,len,path⟩ := reach_sink_of_card (free.mono_set sub)
    (by omega : (T∩R).card≤q) (mem_inter.mpr ⟨kt,kr⟩)
  refine ⟨i,it,fun j jt=>Bool.eq_false_iff.mpr (fun ij=>?_)⟩
  have jr : j∈R := same ▸ BRsub.mem_ballSet.mpr
    ⟨h,hh,mem_ball.mpr ⟨ts jt,m+1+1,by omega,(Walk.step (ts kt) hk (path.mono sub)).snoc (ts jt) ij⟩⟩
  exact sink j (mem_inter.mpr ⟨jt,jr⟩) ij

/-- Uniform trichotomy on the very same terminal heads and carrier. -/
theorem locate {q E U H R T p} (hq : 3≤q) (free : QFree E U q) (ts : T⊆U)
    (size : T.card<q) (same : R=BRsub.ballSet E U H (q-2)) (pr : p∈T\R) :
    (∃i∈T∩R,Misses E i T) ∨ (∀h∈H,Misses E h T) ∨ (∀t∈R,E p t=true → Misses E t T) := by
  classical
  by_cases inside : ∃i∈T∩R,Misses E i T
  · exact Or.inl inside
  right
  by_cases heads : ∀h∈H,Misses E h T
  · exact Or.inl heads
  right
  obtain ⟨h,hh,k,kt,hk⟩ : ∃h∈H,∃k∈T,E h k=true := by
    by_contra! no
    exact heads (fun h hh j jt=>Bool.eq_false_iff.mpr (no h hh j jt))
  intro t tr pt j jt
  apply Bool.eq_false_iff.mpr
  intro tj
  have tv : t∈U := BRsub.ballSet_subset (same ▸ tr)
  rcases return_sink (R:=R) free ts size tv pt ⟨j,jt,tj⟩ with sink|⟨s,sr,ne,_⟩
  · exact inside sink
  · have two : 1<(T\R).card := one_lt_card.mpr ⟨s,sr,p,pr,ne⟩
    exact inside (two_exterior hq free ts size same two hh kt hk)

/-- Keep the actual cut carrier, terminal prices, and replay checks. Every row
in the smaller menu that misses T admits a fresh head and a checked replay
of the cut retaining that head. -/
theorem on_cut {q n b p y z w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (yp : y∈inN X.D X.V b)
    (par : p∈inN X.D X.V b) (hl : (outN X.D X.V b).Nonempty)
    (wp : ∀i∈X.V,0<w i) (flat : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (high : 1<c) (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    (missed : Missed q X.D X.V (outN X.D X.V b) (region q X.D X.V b) b p y z) :
    let U := X.V\{b,y}
    let R := region q X.D X.V b
    let H := outN X.D X.V b
    ∃ T v,Relation.ReflTransGen (CommonParentReplay.Edge q X.D H) ⟨U,{p},z⟩ ⟨U,T,v⟩ ∧
      p∈T ∧ T.card+1=q ∧ CommonParentReplay.Checks q X.D H R U ⟨U,T,v⟩ ∧
      ((∃i∈T∩R,Misses X.D i T) ∨ (∀h∈H,Misses X.D h T) ∨ (∀t∈R,X.D p t=true → Misses X.D t T)) ∧
      ∀i∈R,Misses X.D i T → ∃j∈outN X.D U i,j∉T ∧
        (let W := R∪insert j T
         Relation.ReflTransGen (CommonParentReplay.Edge q X.D H) ⟨U,T,v⟩ ⟨W,T,v⟩ ∧
         CommonParentReplay.Checks q X.D H R U ⟨W,T,v⟩ ∧
           (W=U ∨ W⊂U ∧ CommonParentReplay.Edge q X.D H ⟨U,T,v⟩ ⟨W,T,v⟩)) := by
  intro U R H
  obtain ⟨T,v,path,pT,count,checks,_⟩ := missed
  obtain ⟨yv,yb⟩ := mem_inN.mp yp
  have byNe : b≠y := fun eq=>loopfree X.free (by omega) bv (eq ▸ yb)
  have sub : ({b,y}:Finset ℕ)⊆X.V := insert_subset bv (singleton_subset_iff.mpr yv)
  have room : U.card+1<X.V.card := by
    dsimp [U]; rw [card_sdiff_of_subset sub,card_pair byNe]
    have le := card_le_card sub
    rw [card_pair byNe] at le; omega
  have pr : p∉R := fun h=>((saturated_region (by omega) X.free X.sat bv (mem_inN.mp par).1).mp h).2 (mem_inN.mp par).2
  have safe := X.free.mono_set (sdiff_subset (s:=X.V) (t:={b,y}))
  refine ⟨T,v,path,pT,count,checks,locate hq safe checks.1.selected (by omega) checks.1.same.symm
    (mem_sdiff.mpr ⟨pT,pr⟩),?_⟩
  intro i ir quiet
  obtain ⟨j,jh⟩ := live_after_two hq wp flat high diffuse bv yv byNe (BRsub.ballSet_subset ir)
  refine ⟨j,jh,fun jt=>Bool.noConfusion ((quiet j jt).symm.trans (mem_outN.mp jh).2),?_⟩
  exact CommonParentEndpointReplay.retain_fresh (by omega) safe small room hl checks.1 (mem_outN.mp jh).1

#print axioms return_sink
#print axioms two_exterior
#print axioms locate
#print axioms on_cut
end LeanCH.BR.Closure.RerootTerminalRows
