import checkpoints.shen_extension.FlatMinimumExterior

namespace LeanCH.BR.Closure.FlatOverlapDescent
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor PuncturedDistance

/-- If every arc is witnessed on a shortest cycle through h, every walk
advances its length modulo q+1. No saturation hypothesis is needed. -/
theorem phases {D V q h} (hq : 2≤q) (free : QFree D V q)
    (through : ∀u∈V,∀v∈V,D u v=true → ∃M,Cycle D V q M ∧ h∈M ∧ u∈M ∧ v∈M) :
    ∃phase : ℕ→ZMod (q+1), (∀u∈V,∀v∈V,D u v=true → phase v=phase u+1) ∧
      ∀{u v k},Walk D V u v k → u∈V → phase v=phase u+(k:ℕ) := by
  classical
  let phase (u : ℕ) : ZMod (q+1) := (depth D V h u : ℕ)
  have zero : depth D V h h=0 := Nat.le_zero.mp (depth_le_walk (Walk.refl h : Walk D V h h 0))
  have step (u) (uv : u∈V) (v) (vv : v∈V) (arc : D u v=true) : phase v=phase u+1 := by
    obtain ⟨M,cy,hm,um,vm⟩ := through u uv v vv arc
    by_cases same : v=h
    · subst v
      have ne : h≠u := by rintro rfl; exact loopfree free (by omega) uv arc
      obtain ⟨_,hi,p,r⟩ := MandatoryExcursion.segments (by omega) free cy hm um
      simp only [MandatoryExcursion.span,ite_eq_right ne] at hi p r
      have p' := p.mono cy.sub
      have lp : ¬depth D V h u<q := fun lt => free h _ (by omega) (by omega) (p'.snoc vv arc)
      have back : q+1-depth D V h u≠0 := by
        intro eq
        rw [eq] at r
        cases r
        exact ne rfl
      have eq : depth D V h u=q := by omega
      dsimp only [phase]
      rw [zero,eq,←Nat.cast_succ]
      simp
    · have eq := rise_on_cycle free cy hm um vm same arc
      dsimp only [phase]
      rw [eq,Nat.cast_add,Nat.cast_one]
  have walk {u v k} (p : Walk D V u v k) (uv : u∈V) : phase v=phase u+(k:ℕ) := by
    induction p with
    | refl => simp
    | step bv edge _ ih =>
      rw [ih bv,step _ uv _ bv edge,Nat.cast_succ]
      ring
  exact ⟨phase,step,walk⟩

/-- A saturated graph whose arcs all lie on shortest cycles through the
same label has at most one vertex at each cyclic distance. -/
theorem common_pivot {D V q h} (hq : 2≤q) (free : QFree D V q) (sat : BRsub.Sat q D V)
    (through : ∀u∈V,∀v∈V,D u v=true → ∃M,Cycle D V q M ∧ h∈M ∧ u∈M ∧ v∈M) :
    V.card≤q+1 := by
  classical
  obtain ⟨phase,step,walk⟩ := phases hq free through
  have inj : Function.Injective (fun w : ↥V => phase w.val) := by
    intro u v same
    have one : (1:ZMod (q+1))≠0 := by
      intro eq
      have rem := (ZMod.natCast_eq_natCast_iff 1 0 (q+1)).mp eq
      change 1%(q+1)=0%(q+1) at rem
      rw [Nat.mod_eq_of_lt (by omega),Nat.zero_mod] at rem
      omega
    have miss : ¬D v u=true := by
      intro edge
      have rel := step _ v.property _ u.property edge
      change phase u=phase v at same
      rw [same] at rel
      exact one (add_left_cancel (show phase v+1=phase v+0 by simpa using rel.symm))
    obtain ⟨_,k,le,p⟩ := mem_ball.mp (sat u u.property v v.property miss)
    have eq := walk p u.property
    change phase u=phase v at same
    have kz : (k:ZMod (q+1))=0 := add_left_cancel (show phase u+(k:ℕ)=phase u+0 by simpa using eq.symm.trans same.symm)
    have rem := (ZMod.natCast_eq_natCast_iff k 0 (q+1)).mp kz
    change k%(q+1)=0%(q+1) at rem
    rw [Nat.mod_eq_of_lt (by omega),Nat.zero_mod] at rem
    rw [rem] at p
    have end_eq {i j : ℕ} (w : Walk D V i j 0) : i=j := by cases w; rfl
    exact Subtype.ext (end_eq p)
  simpa only [Fintype.card_coe,ZMod.card] using Fintype.card_le_of_injective _ inj

/-- On a larger flat child, every prescribed vertex is avoided by an
actual shortest cycle of the child. -/
theorem avoiding {D V q z} (hq : 2≤q) (free : QFree D V q) (sat : BRsub.Sat q D V)
    (pos : ∀i∈V,0<z i) (rows : ∀i∈V,realRow q D V z i=1) (room : q+1<V.card) (h : ℕ) :
    ∃M,Cycle D V q M ∧ h∉M := by
  by_contra! all
  apply room.not_ge
  apply common_pivot (h:=h) hq free sat
  intro u uv v vv arc
  obtain ⟨_,⟨w,wh⟩,exts⟩ := FlatOrbitSaturation.successor_mass hq free sat pos rows uv vv arc
  obtain ⟨M,cy,um,vm,_⟩ := exts w wh
  exact ⟨M,cy,all M cy,um,vm⟩

/-- At fixed reference cycle A, replacing B by the indicated shortest
cycle strictly reduces the actual intersection with A. -/
theorem lower_overlap {D V q A B z} (hq : 2≤q) (free : QFree D V q)
    (sat : BRsub.Sat q D (V\(A\B))) (pos : ∀i∈V\(A\B),0<z i)
    (rows : ∀i∈V\(A\B),realRow q D (V\(A\B)) z i=1) (room : q+1<(V\(A\B)).card)
    {h} (shared : h∈A∩B) :
    ∃M,Cycle D V q M ∧ M⊆V\(A\B) ∧ h∉M ∧ A∩M⊂A∩B := by
  obtain ⟨M,cy,no⟩ := avoiding hq (free.mono_set sdiff_subset) sat pos rows room h
  have sub : A∩M⊆A∩B := by
    intro i hi
    obtain ⟨ia,im⟩ := mem_inter.mp hi
    refine mem_inter.mpr ⟨ia,?_⟩
    by_contra nb
    exact (mem_sdiff.mp (cy.sub im)).2 (mem_sdiff.mpr ⟨ia,nb⟩)
  refine ⟨M,⟨cy.sub.trans sdiff_subset,cy.size,cy.heads,cy.incoming⟩,cy.sub,no,Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩⟩
  intro eq
  exact no (mem_inter.mp (eq.symm ▸ shared)).2

#print axioms common_pivot
#print axioms avoiding
#print axioms lower_overlap
/-- Every normalized certificate has a strictly slack retained column. -/
def ForcedSlack (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) :=
  ∀p,RealDual q D U 1 p → ∃z∈U,realCol q D U p z<1

private theorem of_wrong_order {q D U} (hq : 2≤q) (wrong : (U.card : ZMod q)≠1) :
    ForcedSlack q D U := by
  intro p hp
  by_contra! lo
  exact wrong ((CanonicalCycleLaw.unit_columns hq (fun z hz => le_antisymm (hp.columns z hz) (lo z hz))).1 hp.normalized)

/-- For every reference pair, either its present child is already slack, the
two cycles cover the source, or a label-targeted decrease is available.
A second flat child in this decrease costs exactly q labels and ends at
a disjoint cycle. This transition uses all shortest cycles of the same graph. -/
theorem transition {D V q A B} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (ca : Cycle D V q A) (cb : Cycle D V q B) (ne : A≠B) :
    let U := V\(A\B)
    V=A∪B ∨ ForcedSlack q D U ∨
      ∀h∈A∩B,∃M,Cycle D V q M ∧ M⊆U ∧ h∉M ∧ A∩M⊂A∩B ∧
        let U' := V\(A\M)
        U'⊂U ∧ (ForcedSlack q D U' ∨ A∩M=∅ ∧ (A\B).card=1 ∧ U'.card+q=U.card) := by
  classical
  intro U
  have bu : B⊆U := fun i ib => mem_sdiff.mpr ⟨cb.sub ib,fun ab => (mem_sdiff.mp ab).2 ib⟩
  by_cases room : q+1<U.card
  swap
  · left
    have eq : B=U := eq_of_subset_of_card_le bu (cb.size ▸ (by omega))
    ext i
    constructor
    · intro iv
      by_cases ia : i∈A
      · exact mem_union_left _ ia
      · exact mem_union_right _ (eq.symm ▸ mem_sdiff.mpr ⟨iv,fun bad => ia (mem_sdiff.mp bad).1⟩)
    · exact fun hi => union_subset ca.sub cb.sub hi
  right
  by_cases stop : ForcedSlack q D U
  · exact Or.inl stop
  right
  simp only [ForcedSlack,not_forall] at stop
  obtain ⟨p,start⟩ := stop
  push Not at start
  obtain ⟨hp,lo⟩ := start
  have flat (i) (iu : i∈U) : realCol q D U p i=1 := le_antisymm (hp.columns i iu) (lo i iu)
  have rem := (CanonicalCycleLaw.unit_columns hq flat).1 hp.normalized
  have diff : (A\B).Nonempty := sdiff_nonempty.mpr (fun sub => ne (eq_of_subset_of_card_le sub (by rw [ca.size,cb.size])))
  have live := card_pos.mpr diff
  have proper := card_sdiff_add_card_eq_card (sdiff_subset.trans ca.sub : A\B⊆V)
  change U.card+(A\B).card=V.card at proper
  have inside : U⊆V := sdiff_subset
  have limit : U.card<V.card := by omega
  have ulive : U.Nonempty := card_pos.mp (by omega)
  obtain ⟨z,_,pos,rows,_⟩ := FlatChildClosure.rigidity hq small limit (free.mono_set inside) ulive hp flat
  have sat := FlatChildClosure.saturated hq small limit (free.mono_set inside) ulive hp flat
  intro h hh
  obtain ⟨M,cy,ins,absent,less⟩ := lower_overlap hq free sat pos rows room hh
  let U' := V\(A\M)
  have inc : U'⊆U := by
    intro i ih
    obtain ⟨iv,ok⟩ := mem_sdiff.mp ih
    refine mem_sdiff.mpr ⟨iv,?_⟩
    intro gone
    have im : i∈M := by by_contra no; exact ok (mem_sdiff.mpr ⟨(mem_sdiff.mp gone).1,no⟩)
    exact (mem_sdiff.mp (ins im)).2 gone
  have drop : U'⊂U := Finset.ssubset_iff_subset_ne.mpr ⟨inc,fun eq =>
    (mem_sdiff.mp (show h∈U' from eq.symm ▸ bu (mem_inter.mp hh).2)).2 (mem_sdiff.mpr ⟨(mem_inter.mp hh).1,absent⟩)⟩
  refine ⟨M,cy,ins,absent,less,drop,?_⟩
  by_cases other : (U'.card : ZMod q)=1
  swap
  · exact Or.inl (of_wrong_order hq other)
  right
  have dec := card_lt_card drop
  have newSum := card_sdiff_add_card_eq_card (sdiff_subset.trans ca.sub : A\M⊆V)
  change U'.card+(A\M).card=V.card at newSum
  have otherSize := card_sdiff_add_card_inter A M
  rw [ca.size] at otherSize
  have eq : ((U.card-U'.card : ℕ) : ZMod q)=0 := by rw [Nat.cast_sub dec.le,rem,other,sub_self]
  have mult := (ZMod.natCast_eq_natCast_iff (U.card-U'.card) 0 q).mp (by simpa using eq)
  change (U.card-U'.card)%q=0%q at mult
  have big : q≤U.card-U'.card := by
    by_contra! short
    rw [Nat.mod_eq_of_lt short,Nat.zero_mod] at mult
    omega
  have empty : (A∩M).card=0 := by omega
  change A∩M=∅ ∧ (A\B).card=1 ∧ U'.card+q=U.card
  exact ⟨card_eq_zero.mp empty,by omega,by omega⟩

#print axioms transition

end LeanCH.BR.Closure.FlatOverlapDescent
