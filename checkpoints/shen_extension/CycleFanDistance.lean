import checkpoints.shen_extension.CyclePhaseFork

namespace LeanCH.BR.Closure.CycleFanDistance
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor

private noncomputable def reach (D : CH.Digraph) (A H : Finset ℕ) (k : ℕ) := by
  classical exact A.filter (fun z => ∃h∈H,∃j≤k, Walk D A h z j)

private theorem mem_reach {D A H k z} : z∈reach D A H k ↔
    z∈A ∧ ∃h∈H,∃j≤k,Walk D A h z j := by classical simp [reach]

private theorem extend_closed {D : CH.Digraph} {A T : Finset ℕ} (closed : ∀i∈T,∀j∈A,D i j=true → j∈T)
    {a b k} (w : Walk D A a b k) (ha : a∈T) : b∈T := by
  induction w with
  | refl => exact ha
  | step bv ab _ ih => exact ih (closed _ ha _ bv ab)

private theorem expansion {D V A H q} (hq : 1≤q) (free : QFree D V q) (cy : Cycle D V q A)
    (sub : H⊆A) (live : H.Nonempty) (k : ℕ) :
    min A.card (H.card+k) ≤ (reach D A H k).card := by
  induction k with
  | zero =>
    have start : H⊆reach D A H 0 := fun i hi => mem_reach.mpr ⟨sub hi,i,hi,0,le_rfl,.refl _⟩
    exact (min_le_right _ _).trans (by simpa using card_le_card start)
  | succ k ih =>
    let T := reach D A H k
    have nested : T⊆reach D A H (k+1) := by
      intro i hi
      obtain ⟨ia,h,hh,j,le,w⟩ := mem_reach.mp hi
      exact mem_reach.mpr ⟨ia,h,hh,j,by omega,w⟩
    by_cases full : A ⊆ T
    · exact (min_le_left _ _).trans (card_le_card (full.trans nested))
    have grows : T ⊂ reach D A H (k+1) := by
      apply Finset.ssubset_iff_subset_ne.mpr ⟨nested,?_⟩
      intro eq
      have closed (i) (hi : i∈T) (j) (ja : j∈A) (ij : D i j=true) : j∈T := by
        obtain ⟨_,h,hh,l,le,path⟩ := mem_reach.mp hi
        rw [eq]
        exact mem_reach.mpr ⟨ja,h,hh,l+1,by omega,path.snoc ja ij⟩
      obtain ⟨h,hh⟩ := live
      have ht : h∈T := mem_reach.mpr ⟨sub hh,h,hh,0,Nat.zero_le _,.refl _⟩
      apply full
      intro z za
      obtain ⟨_,_,path,_⟩ := MandatoryExcursion.segments hq free cy (sub hh) za
      exact extend_closed closed path ht
    have more := card_lt_card grows
    change min A.card (H.card+k) ≤ T.card at ih
    omega

/-- A route from a recipient of cycle arcs to a sender of cycle arcs has to
allow room for both sets of attachment labels on the same directed cycle. -/
theorem bound {D V A q v u t} (hq : 1≤q) (free : QFree D V q) (cy : Cycle D V q A)
    (vv : v∈V) (walk : Walk D V v u t) (short : t+2≤q)
    (outgoing : (outN D A u).Nonempty) (incoming : (inN D A v).Nonempty) :
    (outN D A u).card + (inN D A v).card ≤ t+3 := by
  classical
  let H := outN D A u
  let B := inN D A v
  let k := q-t-2
  let T := reach D A H k
  have sub : H⊆A := fun _ h => (mem_outN.mp h).1
  have exp := expansion hq free cy sub outgoing k
  have dis : Disjoint T B := by
    apply disjoint_left.mpr
    intro j jt jb
    obtain ⟨_,h,hh,l,le,path⟩ := mem_reach.mp jt
    obtain ⟨ha,uh⟩ := mem_outN.mp hh
    have loop := ((walk.snoc (cy.sub ha) uh).append (path.mono cy.sub)).snoc vv (mem_inN.mp jb).2
    exact free _ _ (by omega) (by dsimp [k] at le; omega) loop
  have all : T ∪ B ⊆ A := union_subset (fun _ hi => (mem_reach.mp hi).1) (fun _ hi => (mem_inN.mp hi).1)
  have size := card_le_card all
  rw [card_union_of_disjoint dis,cy.size] at size
  have bp : 0<B.card := card_pos.mpr incoming
  change min A.card (H.card+k) ≤ T.card at exp
  rw [cy.size] at exp
  change H.card+B.card≤t+3
  dsimp [k] at exp
  omega

#print axioms bound
end LeanCH.BR.Closure.CycleFanDistance
