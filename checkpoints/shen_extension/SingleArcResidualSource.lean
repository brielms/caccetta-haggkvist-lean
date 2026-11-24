import checkpoints.shen_extension.StrictFlatSubsetMerge
import checkpoints.puncture_law_20261119.HeirLaw
import checkpoints.puncture_law_20261119.HeirExit
import LeanCH.BR.BRNonParentBanks

namespace LeanCH.BR.Closure.SingleArcResidualSource
open Finset BRq2 BRq3 BR45 BRsub WeightedSD
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

section Flat
variable {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
  (free : QFree E V q) (small : SmallerSmallRow q V.card)
  {w p : ℕ→ℚ} (pos : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1) (pm : mass V p=1)
  (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1)

include hq free small pos wm pm wr pc in
/-- A source outside the root and its parents is an actual old successor.
The pair merge only requires smaller-order SmallRow, even at the head of
a proposed insertion. -/
theorem arc_of_source {a x : ℕ} (ha : a∈V) (hx : x∈V) (ne : x≠a)
    (parents : ∀i∈V,E i x=true → i=a ∨ E i a=true) : E a x=true := by
  by_contra missing
  have bound := (SharedArcPivotMerge.flat_pair_non_domination hq free small pos wm pm wr pc hx ha ne).2.2.2
  have empty : inN E V x \ inN E V a=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hit,miss⟩ := mem_sdiff.mp hi
    obtain ⟨iv,ix⟩ := mem_inN.mp hit
    rcases parents i iv ix with rfl | ia
    · exact missing ix
    · exact miss (mem_inN.mpr ⟨iv,ia⟩)
  simp [empty,mass] at bound
  exact (pos a ha).2.not_ge bound

include hq free small pos wm pm wr pc in
/-- A nonempty set closed under parents within the residual either has
an heir of the root or contains an old closed walk longer than q.
The set can be confined to the ancestors of a particular missing head. -/
theorem heir_or_walk {a : ℕ} (ha : a∈V) {U : Finset ℕ}
    (sub : U⊆nonParentSet E V a) (live : U.Nonempty)
    (closed : ∀x∈U,∀i∈nonParentSet E V a,E i x=true → i∈U) :
    (∃x∈U,E a x=true ∧ ∀i∈V,i≠a → E i x=true → E i a=true) ∨
    ∃x∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk E U x x m := by
  by_cases acyclic : QFree E U U.card
  · obtain ⟨x,xu,src⟩ := exists_sink acyclic.reverse live le_rfl
    have xv := mem_nonParentSet.mp (sub xu)
    have par (i) (iv : i∈V) (ix : E i x=true) : i=a ∨ E i a=true := by
      by_contra! h
      have inside := closed x xu i (mem_nonParentSet.mpr ⟨iv,h.1,by simp [h.2]⟩) ix
      exact src i inside ix
    exact Or.inl ⟨x,xu,arc_of_source hq free small pos wm pm wr pc ha xv.1 xv.2.1 par,
      fun i iv ne ix=>(par i iv ix).resolve_left ne⟩
  · exact Or.inr (closed_walk_of_not_acyclic free (fun _ hi=>(mem_nonParentSet.mp (sub hi)).1) acyclic)

include hq free small pos wm pm wr pc in
/-- Acyclicity of one nonempty parent-closed set per root suffices for
the round-graph saturation theorem. The whole residual may contain cycles. -/
theorem sat_of_acyclic_sets (noIn : ∀U⊆V,2≤U.card → U≠V → ¬InUniform E V U)
    (sets : ∀a∈V,∃U⊆nonParentSet E V a,U.Nonempty ∧
      (∀x∈U,∀i∈nonParentSet E V a,E i x=true → i∈U) ∧ QFree E U U.card) :
    Sat q E V := by
  apply HeirRound.sat_of_heirs hq free (fun i hi=>(pos i hi).1) wm wr noIn
  intro a ha
  obtain ⟨U,sub,live,closed,ac⟩ := sets a ha
  rcases heir_or_walk hq free small pos wm pm wr pc ha sub live closed with ⟨x,xu,head,par⟩ | ⟨x,_,m,lo,hi,path⟩
  · exact ⟨x,(mem_nonParentSet.mp (sub xu)).1,head,par⟩
  · exact (ac x m (by omega) hi path).elim

end Flat

noncomputable def ancestors (E : CH.Digraph) (V : Finset ℕ) (a b : ℕ) : Finset ℕ := by
  classical
  exact (nonParentSet E V a).filter (fun i=>∃l,Walk E (nonParentSet E V a) i b l)

def Obstruction (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (a b : ℕ) : Prop :=
  let U := ancestors E V a b
  (∃v∈U,E a v=true ∧ (∀i∈V,i≠a → E i v=true → E i a=true) ∧
    (q:ℚ)*w b≤((q:ℚ)-1)*w v) ∨
  ∃x∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk E U x x m

/-- At a legal insertion an old heavy heir can reach the new head
within the residual, or the same ancestor set contains a long old walk. -/
theorem at_hole {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b=false)
    (safe : QFree (insertArc E a b) V q)
    {w p : ℕ→ℚ} (pos : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1) :
    Obstruction q E V w a b := by
  classical
  have pm := HeirExit.mass_col_of_flat wm wr pc
  have edge : insertArc E a b a b=true := by simp [insertArc]
  have ba : (b:ℕ)≠a := by
    intro eq
    exact loopfree safe (by omega) a.property ((congrArg (insertArc E a b a) eq.symm).trans edge)
  have back : ¬E b a=true := fun e=>digonfree safe hq a.property b.property edge (insertArc_mono E a b _ _ e)
  have free := qfree_sub (insertArc_mono E a b) safe
  let U := ancestors E V a b
  have sub : U⊆nonParentSet E V a := filter_subset _ _
  have live : U.Nonempty := ⟨b,mem_filter.mpr ⟨mem_nonParentSet.mpr ⟨b.property,ba,back⟩,0,.refl _⟩⟩
  have closed (x) (xu : x∈U) (i) (ir : i∈nonParentSet E V a) (ix : E i x=true) : i∈U := by
    obtain ⟨l,path⟩ := (mem_filter.mp xu).2
    exact mem_filter.mpr ⟨ir,l+1,.step (sub xu) ix path⟩
  rcases heir_or_walk hq free small pos wm pm wr pc a.property sub live closed with ⟨v,vu,av,par⟩ | cycle
  · have vv := (mem_nonParentSet.mp (sub vu)).1
    exact Or.inl ⟨v,vu,av,par,le_of_not_gt (HeirExit.heir_exit hq small a b off safe pos wm wr pc ⟨v,vv⟩ av par)⟩
  · exact Or.inr cycle

theorem both_ends {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F)
    {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) :
    let E := graph X.D F
    Obstruction q E X.V w f.val.1 f.val.2 ∧ Obstruction q (fun i j=>E j i) X.V p f.val.2 f.val.1 := by
  intro E
  let a := f.val.1
  let b := f.val.2
  have safe : QFree (insertArc E a b) X.V q := by
    apply qfree_sub _ X.free
    intro i j ed
    by_cases eq : i=a.val ∧ j=b.val
    · exact eq.1 ▸ eq.2 ▸ f.property.1
    · have old : E i j=true := by simpa [insertArc,eq] using ed
      exact (mem_col.mp (active.mp old).choose_spec).2.2.2
  have rev := safe.reverse
  rw [insertArc_reverse] at rev
  exact ⟨at_hole hq small a b f.property.2 safe pos wm wr pc,
    at_hole (E:=fun i j=>E j i) hq small b a f.property.2 rev (fun i hi=>(pos i hi).symm)
      (HeirExit.mass_col_of_flat wm wr pc) pc wr⟩

end LeanCH.BR.Closure.SingleArcResidualSource
#print axioms LeanCH.BR.Closure.SingleArcResidualSource.arc_of_source
#print axioms LeanCH.BR.Closure.SingleArcResidualSource.heir_or_walk
#print axioms LeanCH.BR.Closure.SingleArcResidualSource.sat_of_acyclic_sets
#print axioms LeanCH.BR.Closure.SingleArcResidualSource.both_ends
