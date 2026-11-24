import checkpoints.shen_extension.SharedArcPivotSpread
import checkpoints.shen_extension.SharedArcFlatBudget

namespace LeanCH.BR.Closure.SharedArcPivotGate
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights SharedArcBarrier FirstPacketBarrier MarkedCyclePeeling
open SharedArcComponentExchange SharedArcPivotDetour

/-- Keep every native arc except exits from t beyond the heads of a
and entrances to h from outside the parents of a. -/
def cut (D : CH.Digraph) (a t h : ℕ) : CH.Digraph := fun i j =>
  D i j && (decide (i≠t) || D a j) && (decide (j≠h) || D i a)

theorem kept {D : CH.Digraph} {a t h i j : ℕ} :
    cut D a t h i j=true ↔ D i j=true ∧ (i=t → D a j=true) ∧ (j=h → D i a=true) := by
  by_cases e : i=t <;> by_cases f : j=h <;> simp [cut,e,f,and_assoc]

/-- The cut destroys every short return from t to h. Hence the reverse
arc is legal on the proper puncture. No degree or payment is assumed. -/
theorem safe_insert {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hq : 2≤q) (free : QFree D V q)
    {a t h : ℕ} (av : a∈V) (tu : t∈V.erase a) (hu : h∈V.erase a)
    (ta : D t a=true) (ah : D a h=true) (off : D t h=false) :
    QFree (insertArc (cut D a t h) h t) (V.erase a) q := by
  let E := cut D a t h
  have lift {i j m} (w : Walk E (V.erase a) i j m) : Walk D V i j m := by
    induction w with
    | refl => exact .refl _
    | step u e _ ih => exact .step (mem_of_mem_erase u) (kept.mp e).1 ih
  have sub : QFree E (V.erase a) q := fun i m lo hi w => free i m lo hi (lift w)
  apply qfree_insertArc sub (⟨h,hu⟩ : V.erase a) (⟨t,tu⟩ : V.erase a)
  rintro hit
  obtain ⟨_,l,bound,path⟩ := mem_ball.mp hit
  change Walk E (V.erase a) t h l at path
  cases path with
  | refl =>
    exact free _ 2 (by decide) hq (.step av ta (.step (mem_of_mem_erase hu) ah (.refl _)))
  | @step _ x _ k xu tx tail =>
    cases k with
    | zero =>
      cases tail
      exact Bool.noConfusion (off.symm.trans (kept.mp tx).1)
    | succ m =>
      obtain ⟨y,body,_,yh⟩ := tail.unsnoc
      exact free a (m+1+1) (by omega) (by omega)
        (.step (mem_of_mem_erase xu) ((kept.mp tx).2.1 rfl) ((lift body).snoc av ((kept.mp yh).2.2 rfl)))

/-- The smaller-order rule is now available on the specific edited graph
for every pair of fresh endpoints at a stopped pivot. -/
theorem child {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {t h : X.V} (ta : Fresh X F (t,a)) (ah : Fresh X F (a,h)) :
    SmallRow q (insertArc (cut X.D a t h) h t) (X.V.erase a.val) := by
  have absent := (SharedArcPivotChoice.stopped_rectangle X hq small step least stop multi edge no ta ah).1
  have ne {i j : X.V} (ed : X.D i j=true) : i.val≠j.val :=
    fun eq => loopfree X.free (by omega) j.property (by simpa [eq] using ed)
  exact small _ _ (card_erase_lt_of_mem a.property)
    (safe_insert hq X.free a.property (mem_erase.mpr ⟨ne ta.2.2.1,t.property⟩)
      (mem_erase.mpr ⟨(ne ah.2.2.1).symm,h.property⟩) ta.2.2.1 ah.2.2.1 absent)

#print axioms safe_insert
#print axioms child

def cutMany (D : CH.Digraph) (a : ℕ) (T H : Finset ℕ) : CH.Digraph := fun i j =>
  D i j && (decide (i∉T) || D a j) && (decide (j∉H) || D i a)

def edit (D : CH.Digraph) (a : ℕ) (T H : Finset ℕ) : CH.Digraph := fun i j =>
  cutMany D a T H i j || decide (i∈H ∧ j∈T)

private theorem first_new {D : CH.Digraph} {a} {T H U : Finset ℕ} {i j k}
    (walk : Walk (edit D a T H) U i j k) :
    Walk (cutMany D a T H) U i j k ∨ ∃h∈H,∃t∈T,∃l r,l+1+r=k ∧
      Walk (cutMany D a T H) U i h l ∧ Walk (edit D a T H) U t j r := by
  induction walk with
  | refl => exact Or.inl (.refl _)
  | @step i v j k vu iv tail ih =>
    by_cases old : cutMany D a T H i v=true
    · rcases ih with all | ⟨h,hh,t,tt,l,r,eq,pre,post⟩
      · exact Or.inl (.step vu old all)
      · exact Or.inr ⟨h,hh,t,tt,l+1,r,by omega,.step vu old pre,post⟩
    · have rect : i∈H ∧ v∈T := by simpa [edit,Bool.eq_false_iff.mpr old] using iv
      exact Or.inr ⟨i,rect.1,v,rect.2,0,k,by omega,.refl _,tail⟩

/-- Every subrectangle of the reverse arcs can be installed at once after
the two corresponding families of cuts. A short circuit with multiple
installed arcs would have an old segment from T back to H. -/
theorem rectangle_safe {q : ℕ} {D : CH.Digraph} {V T H : Finset ℕ} (hq : 2≤q) (free : QFree D V q)
    {a : ℕ} (av : a∈V) (ts : T⊆V.erase a) (hs : H⊆V.erase a)
    (parents : ∀t∈T,D t a=true) (heads : ∀h∈H,D a h=true) (absent : ∀t∈T,∀h∈H,D t h=false) :
    QFree (edit D a T H) (V.erase a) q := by
  have facts {i j} (e : cutMany D a T H i j=true) :
      D i j=true ∧ (i∈T → D a j=true) ∧ (j∈H → D i a=true) := by
    by_cases it : i∈T <;> by_cases jh : j∈H <;> simp_all [cutMany]
  have shorter {t h l} (tt : t∈T) (hh : h∈H) (len : l<q)
      (w : Walk (cutMany D a T H) (V.erase a) t h l) : False := by
    let J := insertArc (cut D a t h) h t
    have sub {i j} (e : cutMany D a T H i j=true) : J i j=true := by
      obtain ⟨ij,left,right⟩ := facts e
      exact insertArc_mono _ _ _ _ _ (kept.mpr ⟨ij,fun eq => left (eq ▸ tt),fun eq => right (eq ▸ hh)⟩)
    have lift {u v m} (path : Walk (cutMany D a T H) (V.erase a) u v m) : Walk J (V.erase a) u v m := by
      induction path with
      | refl => exact .refl _
      | step inside ed _ ih => exact .step inside (sub ed) ih
    exact safe_insert hq free av (ts tt) (hs hh) (parents _ tt) (heads _ hh) (absent _ tt _ hh)
      t (l+1) (by omega) (by omega) ((lift w).snoc (ts tt) (by simp [J,insertArc]))
  intro i k pos len walk
  rcases first_new walk with all | ⟨h,hh,t,tt,l,r,eq,pre,post⟩
  · exact (qfree_sub (fun _ _ e => (facts e).1) (free.mono_set (erase_subset _ _))) i k pos len all
  · rcases first_new post with back | ⟨h',hh',_,_,m,_,split,old,_⟩
    · exact shorter tt hh (by omega) (back.append pre)
    · exact shorter tt hh' (by omega) old

/-- All cuts and deposits of the rectangle act in a single proper child.
The row rule may then be tested against any nonnegative weights. -/
theorem rectangle_child {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    (T H : Finset ℕ) (ts : ∀t∈T,Fresh X F (t,a)) (hs : ∀h∈H,Fresh X F (a,h)) :
    SmallRow q (edit X.D a T H) (X.V.erase a.val) := by
  have ne {i j : ℕ} (jv : j∈X.V) (ij : X.D i j=true) : i≠j :=
    fun eq => loopfree X.free (by omega) jv (eq ▸ ij)
  apply small _ _ (card_erase_lt_of_mem a.property)
  apply rectangle_safe hq X.free a.property
  · exact fun t tt => mem_erase.mpr ⟨ne a.property (ts t tt).2.2.1,(ts t tt).1⟩
  · exact fun h hh => mem_erase.mpr ⟨(ne (hs h hh).2.1 (hs h hh).2.2.1).symm,(hs h hh).2.1⟩
  · exact fun t tt => (ts t tt).2.2.1
  · exact fun h hh => (hs h hh).2.2.1
  · intro t tt h hh
    exact (SharedArcPivotChoice.stopped_rectangle X hq small step least stop multi edge no
      (s:=⟨t,(ts t tt).1⟩) (h:=⟨h,(hs h hh).2.1⟩) (ts t tt) (hs h hh)).1

#print axioms rectangle_safe
#print axioms rectangle_child

/-- The three terms are the new reverse rectangle, the cut beyond the
pivot's heads, and the cut into H from outside the pivot's parents. -/
theorem row_change {D : CH.Digraph} {a q : ℕ} {T H U : Finset ℕ}
    (parents : ∀t∈T,D t a=true) (reverse : ∀h∈H,∀t∈T,D h t=false)
    (w : ℕ→ℚ) (i : ℕ) :
    WeightedSD.row q (edit D a T H) U w i = WeightedSD.row q D U w i +
      q*((∑j∈U,if i∈H ∧ j∈T then w j else 0) -
         (∑j∈U,if D i j=true ∧ i∈T ∧ D a j=false then w j else 0) -
         (∑j∈U,if D i j=true ∧ j∈H ∧ D i a=false then w j else 0)) := by
  have diff (j : ℕ) :
      (if edit D a T H i j=true then w j else 0) =
      (if D i j=true then w j else 0)+(if i∈H ∧ j∈T then w j else 0)-
      (if D i j=true ∧ i∈T ∧ D a j=false then w j else 0)-
      (if D i j=true ∧ j∈H ∧ D i a=false then w j else 0) := by
    by_cases e : D i j=true
    · have no : ¬(i∈H ∧ j∈T) := fun h => Bool.noConfusion (e.symm.trans (reverse i h.1 j h.2))
      by_cases it : i∈T <;> by_cases jh : j∈H <;> cases aj : D a j <;> cases ia : D i a <;>
        simp_all [edit,cutMany]
    · simp [edit,cutMany,Bool.eq_false_iff.mpr e]
  simp only [WeightedSD.row,outW,diff,sum_sub_distrib,sum_add_distrib]
  ring

/-- Positive weights paying every retained row, with one strictly paid
row, give a recursive exit on the explicit smaller graph. -/
def Paid {q n} (X : Model q n) : Prop :=
  ∃ (a : X.V) (T H : Finset ℕ),T⊆X.V.erase a.val ∧ H⊆X.V.erase a.val ∧
    (∀t∈T,X.D t a=true) ∧ (∀h∈H,X.D a h=true) ∧ (∀t∈T,∀h∈H,X.D t h=false) ∧
    ∃w : ℕ→ℚ,(∀i∈X.V.erase a.val,0<w i) ∧
      (∀i∈X.V.erase a.val,mass (X.V.erase a.val) w≤WeightedSD.row q (edit X.D a T H) (X.V.erase a.val) w i) ∧
      ∃i∈X.V.erase a.val,mass (X.V.erase a.val) w<WeightedSD.row q (edit X.D a T H) (X.V.erase a.val) w i

def ProgressAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ) (K : Matrix X.V X.V ℝ)
    (p : ℕ→ℚ) (c : ℚ) : Prop := SharedArcFlatBudget.ProgressAt X F B K p c ∨ Paid X

theorem blocks {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B K p c} (prior : ¬SharedArcFlatBudget.ProgressAt X F B K p c) : ¬ProgressAt X F B K p c := by
  rintro (done|⟨a,T,H,ts,hs,ta,ah,absent,w,pos,weak,i,iv,strict⟩)
  · exact prior done
  · have row := positive_feasible_rows_tight_of_smallRow hq (small _ _ (card_erase_lt_of_mem a.property)
      (rectangle_safe hq X.free a.property ts hs ta ah absent)) w pos weak i iv
    exact strict.ne row.symm

#print axioms row_change
#print axioms blocks

/-- A complete payment using the positive weights already present on the
puncture. Every selected parent is clean, and the selected heads absorb
their own losses. No bound on individual degrees is needed. -/
theorem paid_of_closed {q n} (X : Model q n) (hq : 3≤q) (a : X.V) (T H : Finset ℕ)
    (ts : T⊆X.V.erase a.val) (hs : H⊆X.V.erase a.val) (live : H.Nonempty)
    (parents : ∀t∈T,X.D t a=true) (heads : ∀h∈H,X.D a h=true) (absent : ∀t∈T,∀h∈H,X.D t h=false)
    (clean : ∀t∈T,∀x∈X.V.erase a.val,X.D t x=true → X.D a x=true)
    (closed : ∀h∈H,∀y∈X.V.erase a.val,X.D y h=true → X.D y a=false → y∈H)
    (w : ℕ→ℚ) (pos : ∀i∈X.V.erase a.val,0<w i)
    (flat : ∀i∈X.V.erase a.val,mass (X.V.erase a.val) w≤WeightedSD.row q X.D (X.V.erase a.val) w i)
    (enough : mass H w≤mass T w) : Paid X := by
  classical
  let U := X.V.erase a.val
  have reverse (h) (hh : h∈H) (t) (tt : t∈T) : X.D h t=false := Bool.eq_false_iff.mpr fun ht =>
    X.free a 3 (by decide) hq (.step (mem_of_mem_erase (hs hh)) (heads h hh)
      (.step (mem_of_mem_erase (ts tt)) ht (.step a.property (parents t tt) (.refl _))))
  have payment (i) (ui : i∈U) :
      (mass U w≤WeightedSD.row q (edit X.D a T H) U w i) ∧
      (i∈H → mass U w<WeightedSD.row q (edit X.D a T H) U w i) := by
    have changeRow := row_change (U:=U) (q:=q) parents reverse w i
    have noLoss : (∑j∈U,if X.D i j=true ∧ i∈T ∧ X.D a j=false then w j else 0)=0 :=
      sum_eq_zero fun j ju => ite_eq_right fun ⟨ij,it,aj⟩ => Bool.noConfusion (aj.symm.trans (clean i it j ju ij))
    rw [noLoss,sub_zero] at changeRow
    have old := flat i ui
    by_cases ih : i∈H
    · have gain : (∑j∈U,if i∈H ∧ j∈T then w j else 0)=mass T w := by
        simp [ih,inter_eq_right.mpr ts,mass,U]
      let L := U.filter (fun j => X.D i j=true ∧ j∈H ∧ X.D i a=false)
      have sub : L⊆H.erase i := by
        intro j hj
        obtain ⟨_,ij,jh,_⟩ := mem_filter.mp hj
        exact mem_erase.mpr ⟨fun e => loopfree X.free (by omega) (mem_of_mem_erase ui) (e ▸ ij),jh⟩
      have cap := sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun j hj _ => (pos j (hs (mem_of_mem_erase hj))).le)
      have strictLoss : (∑j∈L,w j)<mass H w := by
        change (∑j∈L,w j)<∑j∈H,w j
        linarith [sum_erase_add H w ih,pos i ui]
      rw [gain,←sum_filter] at changeRow
      have strict : mass U w<WeightedSD.row q (edit X.D a T H) U w i := by
        rw [changeRow]
        exact lt_add_of_le_of_pos old (mul_pos (by exact_mod_cast (show 0<q by omega)) (sub_pos.mpr (strictLoss.trans_le enough)))
      exact ⟨strict.le,fun _ => strict⟩
    · have noIn : (∑j∈U,if X.D i j=true ∧ j∈H ∧ X.D i a=false then w j else 0)=0 :=
        sum_eq_zero fun j _ => ite_eq_right fun ⟨ij,jh,ia⟩ => ih (closed j jh i ui ij ia)
      rw [noIn] at changeRow
      simp [ih] at changeRow
      exact ⟨changeRow ▸ old,fun e => (ih e).elim⟩
  obtain ⟨h,hh⟩ := live
  exact ⟨a,T,H,ts,hs,parents,heads,absent,w,pos,fun i ui => (payment i ui).1,
    h,hs hh,(payment h (hs hh)).2 hh⟩

#print axioms paid_of_closed

/-- Saturation forces every other native parent to feed a parent whose
puncture successors are already heads of the pivot. -/
theorem forced_parent {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {a t u : ℕ}
    (free : QFree D V q) (sat : BRsub.Sat q D (V.erase a)) (av : a∈V)
    (tu : t∈V.erase a) (uu : u∈V.erase a) (diff : t≠u) (ua : D u a=true)
    (clean : ∀x∈V.erase a,D t x=true → D a x=true) (hq : 1≤q) : D u t=true := by
  by_contra no
  obtain ⟨_,m,len,path⟩ := mem_ball.mp (sat t tu u uu no)
  cases path with
  | refl => exact diff rfl
  | @step _ x _ k xu tx body =>
    exact free a (k+1+1) (by omega) (by omega)
      (.step (mem_of_mem_erase xu) (clean x xu tx) ((body.mono (erase_subset _ _)).snoc av ua))

theorem clean_bank_card {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ} {a : ℕ}
    (hq : 2≤q) (free : QFree D V q) (sat : BRsub.Sat q D (V.erase a)) (av : a∈V)
    (ts : T⊆V.erase a) (parents : ∀t∈T,D t a=true)
    (clean : ∀t∈T,∀x∈V.erase a,D t x=true → D a x=true) : T.card≤1 := by
  apply card_le_one.mpr
  intro t tt u uu
  by_contra diff
  have ut := forced_parent free sat av (ts tt) (ts uu) diff (parents u uu) (clean t tt) (by omega)
  have tu := forced_parent free sat av (ts uu) (ts tt) (Ne.symm diff) (parents t tt) (clean u uu) (by omega)
  exact free t 2 (by decide) hq (.step (mem_of_mem_erase (ts uu)) tu (.step (mem_of_mem_erase (ts tt)) ut (.refl _)))

#print axioms clean_bank_card

/-- A clean fresh parent is the only fresh parent, including those
which might themselves have exterior successors. -/
theorem clean_parent_only {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {t : X.V} (fresh : Fresh X F (t,a))
    (clean : ∀x∈X.V.erase a.val,X.D t x=true → X.D a x=true)
    {u : X.V} (freshU : Fresh X F (u,a)) : u=t := by
  classical
  obtain ⟨_,sat,_,_⟩ := (SharedArcPivot.alternatives X (by omega) small step least multi edge).resolve_left no
  have punct {i : X.V} (ia : X.D i a=true) : i.val∈X.V.erase a.val :=
    mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) a.property (by simpa [eq] using ia),i.property⟩
  have tu := punct fresh.2.2.1
  have vu : t∈rest a := mem_erase.mpr ⟨fun e => (mem_erase.mp tu).1 (congrArg Subtype.val e),mem_univ _⟩
  have covers (x : X.V) (_ : x∈rest a) (old : graph X.D F x a=true) : X.D x t=true := by
    obtain ⟨_,w⟩ := active.mp old
    have xa := (mem_col.mp w).2.2.2
    apply forced_parent X.free sat a.property tu (punct xa) _ xa clean (by omega)
    intro e
    exact Bool.noConfusion (fresh.2.2.2.symm.trans (by simpa [e] using old))
  have off := (SharedArcPivotSpread.masks X hq small step least stop multi edge no freshU edge t vu).2 covers
  by_contra diff
  have ut := forced_parent X.free sat a.property tu (punct freshU.2.2.1)
    (fun eq => diff (Subtype.ext eq.symm)) freshU.2.2.1 clean (by omega)
  exact Bool.noConfusion (off.symm.trans ut)

#print axioms clean_parent_only
end LeanCH.BR.Closure.SharedArcPivotGate
