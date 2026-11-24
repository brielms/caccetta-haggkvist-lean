import checkpoints.shen_extension.RecurrentRecipient

namespace LeanCH.BR.Closure.ShortSplitExterior
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor MandatoryExcursion

/-- A cross-parent on the other arm must occur after its first head and
before the common meeting label on the directed cycle. -/
private theorem within_arm {E V A q r b z y m} (hq : 1≤q) (free : QFree E V q)
    (cy : Cycle E V q A) (rc : r∈A) (bc : b∈A) (zc : z∈A) (bz : b≠z)
    (yv : y∈V) (byArc : E b y=true) (miss : E b r=false)
    (first : Walk E A r z m) (second : Walk E V y z m) :
    ∃ k,k<m ∧ Walk E V r b k := by
  obtain ⟨_,du,along,back⟩ := segments hq free cy zc bc
  let d := span E V q z b
  have upper : d≤q := by
    by_contra! large
    change Walk E A b z (q+1-d) at back
    rw [show q+1-d=0 by omega] at back
    cases back; exact bz rfl
  have loop := (along.mono cy.sub).append (Walk.step yv byArc second)
  have lb : q<m+d+1 := by
    by_contra! low
    exact free _ _ (by omega) (by change d+(m+1)≤q; omega) loop
  have full := (segments hq free cy rc rc).2.2.1
  have turn : Walk E A r r (q+1) := by simpa [span] using full
  have seq : Walk E A r b (m+d) := first.append along
  have neq : m+d≠q := by
    intro eq
    rw [eq] at seq
    obtain ⟨t,pre,_,last⟩ := turn.unsnoc
    have be := ConsecutiveBlockerPool.same_end cy rc seq pre
    rw [←be,miss] at last
    contradiction
  have len : q+1≤m+d := by omega
  obtain ⟨f,start,finish,edges⟩ := seq.toFun
  have frontPart := walk_between edges (i:=0) (j:=q+1) (by omega) len
  rw [start,Nat.sub_zero] at frontPart
  have mid := ConsecutiveBlockerPool.same_end cy rc frontPart turn
  have tail := walk_between edges len le_rfl
  rw [mid,finish] at tail
  exact ⟨_,by omega,tail.mono cy.sub⟩

/-- Either an exclusive parent escapes both cycles or two actual cross-parents
produce a closed walk whose two internal segment lengths must pay the girth. -/
theorem alternatives {E V A M q u y r z m x c} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (a : Cycle E V q A) (b : Cycle E V q M)
    (ua : u∈A) (um : u∈M) (ya : y∈A) (rm : r∈M) (za : z∈A) (zm : z∈M)
    (diff : y≠r) (uy : E u y=true) (ur : E u r=true)
    (left : Walk E A y z m) (right : Walk E M r z m)
    (pos : ∀v∈V,0≤x v) (high : mass V x<c) (rows : ∀v∈V,WeightedSD.row q E V x v=c) :
    (∃p∈V\(A∪M),
      (E p y=true ∧ E p r=false ∧ RecurrentRecipient.Fails q E V x p y r) ∨
      (E p r=true ∧ E p y=false ∧ RecurrentRecipient.Fails q E V x p r y)) ∨
    ∃p∈M\A, ∃t∈A\M, E p y=true ∧ E p r=false ∧ E t r=true ∧ E t y=false ∧
      ∃ i : ℕ, i < m ∧ ∃ j : ℕ, j < m ∧ Walk E V r p i ∧ Walk E V y t j ∧ (q + 1 ≤ i + j + 2) := by
  classical
  have pick {C B i j} (cy : Cycle E V q C) (cb : Cycle E V q B)
      (uc : u∈C) (ic : i∈C) (jb : j∈B) (ne : i≠j) (ui : E u i=true) (uj : E u j=true) :
      ∃p∈V\C,E p i=true ∧ E p j=false := by
    by_contra! none
    apply strict_no_incoming_domination (small.induced free) x pos
      (fun v hv => (rows v hv) ▸ high) (cy.sub ic) (cb.sub jb) ne
    intro p pv hit
    by_cases pc : p∈C
    · have same := card_le_one.mp (cy.incoming i ic).le _ (mem_inN.mpr ⟨pc,hit⟩) _ (mem_inN.mpr ⟨uc,ui⟩)
      exact same ▸ uj
    · exact Bool.eq_true_of_not_eq_false (none p (mem_sdiff.mpr ⟨mem_of_mem_erase pv,pc⟩) hit)
  obtain ⟨p,pa,py,pr⟩ := pick a b ua ya rm diff uy ur
  obtain ⟨t,tm,tr,ty⟩ := pick b a um rm ya diff.symm ur uy
  by_cases pm : p∈M
  · by_cases ta : t∈A
    · obtain ⟨i,im,path⟩ := within_arm (by omega) free b rm pm zm
        (fun eq => (mem_sdiff.mp pa).2 (eq ▸ za)) (a.sub ya) py pr right (left.mono a.sub)
      obtain ⟨j,jm,other⟩ := within_arm (by omega) free a ya ta za
        (fun eq => (mem_sdiff.mp tm).2 (eq ▸ zm)) (b.sub rm) tr ty left (right.mono b.sub)
      have loop := ((path.snoc (a.sub ya) py).append other).snoc (b.sub rm) tr
      have room : (q + 1 ≤ i + j + 2) := by
        by_contra! tooShort
        exact free _ _ (by omega) (by omega) loop
      exact Or.inr ⟨p,mem_sdiff.mpr ⟨pm,(mem_sdiff.mp pa).2⟩,t,mem_sdiff.mpr ⟨ta,(mem_sdiff.mp tm).2⟩,
        py,pr,tr,ty,i,im,j,jm,path,other,room⟩
    · have tv := (mem_sdiff.mp tm).1
      exact Or.inl ⟨t,mem_sdiff.mpr ⟨tv,fun h => (mem_union.mp h).elim ta (mem_sdiff.mp tm).2⟩,
        Or.inr ⟨tr,ty,PairedFamilyLoop.fails hq free small pos high rows tv (b.sub rm) (a.sub ya) tr ty⟩⟩
  · have pv := (mem_sdiff.mp pa).1
    exact Or.inl ⟨p,mem_sdiff.mpr ⟨pv,fun h => (mem_union.mp h).elim (mem_sdiff.mp pa).2 pm⟩,
      Or.inl ⟨py,pr,PairedFamilyLoop.fails hq free small pos high rows pv (a.sub ya) (b.sub rm) py pr⟩⟩

/-- A short reunion of equal-length branches forces an actual distinguishing
parent outside both cycles. Its single-head transfer strictly fails there. -/
theorem escape {E V A M q u y r z m x c} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (a : Cycle E V q A) (b : Cycle E V q M)
    (ua : u∈A) (um : u∈M) (ya : y∈A) (rm : r∈M) (za : z∈A) (zm : z∈M)
    (diff : y≠r) (uy : E u y=true) (ur : E u r=true)
    (left : Walk E A y z m) (right : Walk E M r z m) (short : 2*m≤q)
    (pos : ∀v∈V,0≤x v) (high : mass V x<c) (rows : ∀v∈V,WeightedSD.row q E V x v=c) :
    ∃p∈V\(A∪M),
      (E p y=true ∧ E p r=false ∧ RecurrentRecipient.Fails q E V x p y r) ∨
      (E p r=true ∧ E p y=false ∧ RecurrentRecipient.Fails q E V x p r y) := by
  rcases alternatives hq free small a b ua um ya rm za zm diff uy ur left right pos high rows with escaped|witness
  · exact escaped
  · obtain ⟨_,_,_,_,_,_,_,_,_,im,_,jm,_,_,room⟩ := witness
    omega

#print axioms alternatives
#print axioms escape
end LeanCH.BR.Closure.ShortSplitExterior
