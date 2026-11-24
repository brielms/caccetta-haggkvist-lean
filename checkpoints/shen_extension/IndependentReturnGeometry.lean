import checkpoints.shen_extension.TwoParentReturnCapacity

namespace LeanCH.BR.Closure.IndependentReturnGeometry
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity

/-- Saturation separates independent returns by actual first heads of short
walks. Only the opposite parent can serve as an exterior first head. -/
theorem first_label {q E V b p y I t h} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (bv : b∈V) (parents : inN E V b={p,y}) (within : I⊆outN E (region q E V b) p)
    (indep : ∀i∈I,∀j∈I,E i j=false) (ti : t∈I) (hi : h∈I) (ne : t≠h) :
    ∃k∈insert y (region q E V b \ I),E t k=true ∧ E h k=false ∧ k∉I ∧
      ∃l,1≤l ∧ l≤q-2 ∧ Walk E V k h l := by
  obtain ⟨tr,pt⟩ := mem_outN.mp (within ti)
  obtain ⟨hr,_⟩ := mem_outN.mp (within hi)
  have tv := BRsub.ballSet_subset tr
  have hv := BRsub.ballSet_subset hr
  have miss : E h t≠true := by simp [indep h hi t ti]
  obtain ⟨_,j,le,path⟩ := mem_ball.mp (sat t tv h hv miss)
  cases path with
  | refl => exact (ne rfl).elim
  | @step _ k _ l kv tk tail =>
    have diff : k∉I := fun ki=>Bool.noConfusion (tk.symm.trans (indep t ti k ki))
    have pos : 1≤l := by
      by_contra! zl
      have zero : l=0 := by omega
      subst l; cases tail; exact diff hi
    have nk : E h k=false := by
      cases hk : E h k
      · rfl
      · exact (free k _ (by omega) (by omega) (tail.snoc kv hk)).elim
    refine ⟨k,?_,tk,nk,diff,l,pos,by omega,tail⟩
    by_cases ky : k=y
    · exact mem_insert.mpr (.inl ky)
    have ktp : k≠p := fun eq=>digonfree free hq (eq ▸ kv) tv pt (eq ▸ tk)
    have ktb : k≠b := fun eq=>((saturated_region hq free sat bv tv).mp tr).2 (eq ▸ tk)
    have nob : E k b≠true := fun kb=>by
      have either : k∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨kv,kb⟩
      simp [ktp,ky] at either
    exact mem_insert_of_mem (mem_sdiff.mpr ⟨(saturated_region hq free sat bv kv).mpr ⟨ktb,nob⟩,diff⟩)

/-- Within each of the two classes determined by the arc into y, the
actual inner head sets form an antichain. The separating head begins a
return to the other label of length at most q-2. -/
theorem inner_label {q E V b p y I t h} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (bv : b∈V) (parents : inN E V b={p,y}) (within : I⊆outN E (region q E V b) p)
    (indep : ∀i∈I,∀j∈I,E i j=false) (ti : t∈I) (hi : h∈I) (ne : t≠h)
    (bit : E t y=true → E h y=true) :
    ∃k∈region q E V b \ I,E t k=true ∧ E h k=false ∧ ∃l,1≤l ∧ l≤q-2 ∧ Walk E V k h l := by
  obtain ⟨k,where_,tk,hk,_,path⟩ := first_label hq free sat bv parents within indep ti hi ne
  refine ⟨k,(mem_insert.mp where_).resolve_left ?_,tk,hk,path⟩
  rintro rfl; exact Bool.noConfusion (hk.symm.trans (bit tk))

/-- At cutoff three, every ordered pair of independent returns has an
actual two-step path through the inner region outside I, even across the
two classes. Column separation prevents the middle vertex from being y. -/
theorem triangle {E V b p y I t h} (free : QFree E V 3) (sat : BRsub.Sat 3 E V)
    (sep : ShenParentIntersection.Separated E V V) (bv : b∈V) (parents : inN E V b={p,y})
    (within : I⊆outN E (region 3 E V b) p) (indep : ∀i∈I,∀j∈I,E i j=false)
    (ti : t∈I) (hi : h∈I) (ne : t≠h) :
    ∃k∈region 3 E V b \ I,E t k=true ∧ E k h=true ∧ E h k=false := by
  obtain ⟨k,where_,tk,hk,_,l,pos,le,walk⟩ := first_label (by decide) free sat bv parents within indep ti hi ne
  have one : l=1 := by omega
  subst l
  obtain ⟨i,zero,_,edge⟩ := walk.unsnoc
  cases zero
  obtain ⟨hr,ph⟩ := mem_outN.mp (within hi)
  have hv := BRsub.ballSet_subset hr
  obtain ⟨x,xv,xb,xh⟩ := sep b bv h hv ((saturated_region (by decide) free sat bv hv).mp hr).1
  have xp : x∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨xv,xb⟩
  have xy : x=y := mem_singleton.mp ((mem_insert.mp xp).resolve_left (fun e=>Bool.noConfusion ((e ▸ xh).symm.trans ph)))
  subst x
  refine ⟨_,(mem_insert.mp where_).resolve_left (fun ky=>Bool.noConfusion (xh.symm.trans (ky ▸ edge))),tk,edge,hk⟩

#print axioms first_label
#print axioms inner_label
#print axioms triangle
end LeanCH.BR.Closure.IndependentReturnGeometry
