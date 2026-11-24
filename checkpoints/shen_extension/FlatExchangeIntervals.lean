import checkpoints.shen_extension.FlatExchangeCycle

namespace LeanCH.BR.Closure.FlatExchangeIntervals
open Finset BRq2 BRq3 BR45 WeightedSD FlatExchangeCycle

def ConstantOnArcs (E : CH.Digraph) (L : Finset ℕ) (label : ℕ → Bool) : Prop :=
  ∀ i∈L, ∀j∈L, E i j=true → label i=label j

/-- A finite graph is weakly connected if every binary labelling constant
along its arcs is constant on its vertices. -/
def Connected (E : CH.Digraph) (L : Finset ℕ) : Prop :=
  ∀ label : ℕ → Bool, ConstantOnArcs E L label →
    ∀i∈L,∀j∈L,label i=label j

private theorem along_walk {E L c} (same : ConstantOnArcs E L c) {i j k}
    (w : Walk E L i j k) (hi : i∈L) : c i=c j := by
  induction w with
  | refl => rfl
  | step hb edge _ ih => exact (same _ hi _ hb edge).trans (ih hb)

private theorem inv_fixed {S T : Finset ℕ} {e : ↥S ≃ ↥T}
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (i : ↥T) (h : (i:ℕ)∈S) : (e.symm i:ℕ)=i := by
  have hj : e ⟨i,h⟩=i := Subtype.ext (fix ⟨i,h⟩ i.property)
  exact congrArg Subtype.val (e.symm_apply_eq.mpr hj.symm)

private theorem inv_out {S T : Finset ℕ} {e : ↥S ≃ ↥T}
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (i : ↥T) (h : (i:ℕ)∉S) : (e.symm i:ℕ)∈S\T := by
  refine mem_sdiff.mpr ⟨(e.symm i).property,fun overlap => ?_⟩
  have eqn := fix (e.symm i) overlap
  rw [e.apply_symm_apply] at eqn
  exact h (eqn ▸ (e.symm i).property)

/-- An arc from the first private block to the second preserves any
labelling constant on each block and respected by the comparison. -/
private theorem cross_label {q E V S T} (hq : 2≤q) (free : QFree E V q)
    (sat : BRsub.Sat q E S) (sv : S⊆V) (tv : T⊆V) (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i)
    (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    (c : ℕ→Bool) (align : ∀i : ↥S,c i=c (e i)) (arcs : ConstantOnArcs E (S\T) c)
    {i j} (hi : i∈S\T) (hj : j∈T\S) (edge : E i j=true) : c i=c j := by
  let a : ↥S := ⟨i,(mem_sdiff.mp hi).1⟩
  let b : ↥T := ⟨j,(mem_sdiff.mp hj).1⟩
  let r := e.symm b
  have hr := inv_out fix b (mem_sdiff.mp hj).2
  have cb : c r=c j := by simpa [r,b] using align (e.symm b)
  apply Eq.trans _ cb
  cases ir : E i r
  · have cross : E a (e r)=true := by simpa [r,a,b] using edge
    obtain ⟨_,_,path⟩ := confined hq free sat sv tv e fix iso a r cross ir
    exact (along_walk arcs path hr).symm
  · exact arcs i hi r hr ir

private theorem whole_arcs {q E V S T} (hq : 2≤q) (free : QFree E V q)
    (sSat : BRsub.Sat q E S) (tSat : BRsub.Sat q E T) (sv : S⊆V) (tv : T⊆V)
    (e : ↥S ≃ ↥T) (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i)
    (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    (c : ℕ→Bool) (align : ∀i : ↥S,c i=c (e i))
    (sa : ConstantOnArcs E (S\T) c) (ta : ConstantOnArcs E (T\S) c) :
    ConstantOnArcs E (moved S T) c := by
  intro i hi j hj edge
  rcases mem_union.mp hi with h | h <;> rcases mem_union.mp hj with k | k
  · exact sa i h j k edge
  · exact cross_label hq free sSat sv tv e fix iso c align sa h k edge
  · exact cross_label hq free tSat tv sv e.symm (inv_fixed fix)
      (fun u v => by simpa using (iso (e.symm u) (e.symm v)).symm) c
      (fun u => by simpa using (align (e.symm u)).symm) ta h k edge
  · exact ta i h j k edge

/-- Any nonempty class which arcs cannot leave or enter in the moved
graph inherits the long distinguishing walk. -/
theorem class_cycle {q E V S T} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (sv : S⊆V) (tv : T⊆V) (cover : V⊆S∪T) (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    (K : Finset ℕ) (sub : K⊆moved S T) (live : K.Nonempty)
    (closed : ∀j∈moved S T, ∀i∈K,E j i=true → j∈K) :
    ∃v k,q<k ∧ k≤K.card ∧ Walk (distinguished E (partner e)) K v v k := by
  have mv : moved S T⊆V := union_subset (sdiff_subset.trans sv) (sdiff_subset.trans tv)
  apply cycle free small (sub.trans mv) live xp strict
  · intro i hi
    rcases mem_union.mp (sub hi) with h | h
    · obtain ⟨hs,ht⟩ := mem_sdiff.mp h
      simp only [partner,dite_eq_left hs]
      exact ⟨tv (e ⟨i,hs⟩).property,fun eq => ht (eq ▸ (e ⟨i,hs⟩).property)⟩
    · obtain ⟨ht,hs⟩ := mem_sdiff.mp h
      simp only [partner,dite_eq_right hs,dite_eq_left ht]
      exact ⟨sv (e.symm ⟨i,ht⟩).property,fun eq => hs (eq ▸ (e.symm ⟨i,ht⟩).property)⟩
  · intro i hi j hj edge
    have no : j∉moved S T := fun jm => (mem_sdiff.mp hj).2 (closed j jm i hi edge)
    have both : j∈S ∧ j∈T := by
      have either := mem_union.mp (cover (mem_sdiff.mp hj).1)
      by_cases js : j∈S <;> by_cases jt : j∈T <;> simp_all [moved]
    let u : ↥S := ⟨j,both.1⟩
    rcases mem_union.mp (sub hi) with h | h
    · obtain ⟨hs,_⟩ := mem_sdiff.mp h
      have eq := iso u ⟨i,hs⟩
      rw [fix u both.2] at eq
      simpa only [partner,dite_eq_left hs] using eq.symm.trans edge
    · obtain ⟨ht,hs⟩ := mem_sdiff.mp h
      have eq := iso u (e.symm ⟨i,ht⟩)
      rw [fix u both.2,e.apply_symm_apply] at eq
      simpa only [partner,dite_eq_right hs,dite_eq_left ht] using eq.trans edge

theorem connected {q E V S T} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (sv : S⊆V) (tv : T⊆V) (cover : V⊆S∪T) (sSat : BRsub.Sat q E S) (tSat : BRsub.Sat q E T)
    (e : ↥S ≃ ↥T) (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i)
    (iso : ∀i j : ↥S,E i j=E (e i) (e j)) (budget : (moved S T).card≤2*q) :
    Connected E (S\T) := by
  classical
  intro label arcs i hi j hj
  let c (t : ℕ) := if h : t∈T then label (e.symm ⟨t,h⟩) else label t
  have left (t) (ts : t∈S) : c t=label t := by
    by_cases ht : t∈T
    · simp only [c,dite_eq_left ht,inv_fixed fix (⟨t,ht⟩ : ↥T) ts]
    · simp [c,ht]
  have right (v : ↥T) : c v=label (e.symm v) := by simp [c,v.property]
  have align (v : ↥S) : c v=c (e v) := by rw [left _ v.property,right,e.symm_apply_apply]
  have sa : ConstantOnArcs E (S\T) c := by
    intro a ha b hb arc
    rw [left a (mem_sdiff.mp ha).1,left b (mem_sdiff.mp hb).1]
    exact arcs a ha b hb arc
  have ta : ConstantOnArcs E (T\S) c := by
    intro a ha b hb arc
    let u : ↥T := ⟨a,(mem_sdiff.mp ha).1⟩
    let v : ↥T := ⟨b,(mem_sdiff.mp hb).1⟩
    have eq := iso (e.symm u) (e.symm v)
    rw [e.apply_symm_apply,e.apply_symm_apply] at eq
    exact (right u).trans ((arcs _ (inv_out fix u (mem_sdiff.mp ha).2) _
      (inv_out fix v (mem_sdiff.mp hb).2) (eq.trans arc)).trans (right v).symm)
  have whole := whole_arcs hq free sSat tSat sv tv e fix iso c align sa ta
  let K := moved S T
  let P (t : ℕ) := c t=c i
  have large (pred : ℕ→Prop) [DecidablePred pred]
      (agree : ∀a∈K,∀b∈K,E a b=true → (pred b → pred a))
      (live : (K.filter pred).Nonempty) : q<(K.filter pred).card := by
    obtain ⟨_,_,long,cap,_⟩ := class_cycle free small xp strict sv tv cover e fix iso
      (K.filter pred) (filter_subset _ _) live (fun a ha b hb edge =>
        mem_filter.mpr ⟨ha,agree a ha b (mem_filter.mp hb).1 edge (mem_filter.mp hb).2⟩)
    omega
  by_contra ne
  have mi : i∈K := mem_union_left _ hi
  have mj : j∈K := mem_union_left _ hj
  have diff : ¬P j := by
    dsimp [P]; rw [left i (mem_sdiff.mp hi).1,left j (mem_sdiff.mp hj).1]; exact Ne.symm ne
  have lo := large P (fun a ha b hb edge h => (whole a ha b hb edge).trans h)
    ⟨i,mem_filter.mpr ⟨mi,rfl⟩⟩
  have hi' := large (fun v => ¬P v) (fun a ha b hb edge h same => h ((whole a ha b hb edge).symm.trans same))
    ⟨j,mem_filter.mpr ⟨mj,diff⟩⟩
  have split := card_filter_add_card_filter_not (s:=K) P
  change K.card≤2*q at budget
  omega

#print axioms class_cycle
#print axioms connected

end LeanCH.BR.Closure.FlatExchangeIntervals
