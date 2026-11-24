import checkpoints.shen_extension.SharedArcBudget

namespace LeanCH.BR.Closure.SharedArcAffordablePaths
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier
open SharedArcExpansion SharedArcBarrier

/-- Each added arc fits the old dual by itself. Several added arcs entering
one column need not fit together. -/
noncomputable def affordable (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (F : Family) (p : ℕ→ℝ) :
    CH.Digraph := by
  classical exact fun u v => decide (D u v=true ∧
    (graph D F u v=true ∨ realCol q (graph D F) V p v+q*p u≤1))

private theorem parts {q D V F p u v} (arc : affordable q D V F p u v=true) :
    D u v=true ∧ (graph D F u v=true ∨ realCol q (graph D F) V p v+q*p u≤1) := by
  classical exact of_decide_eq_true arc

/-- A bounded affordable return at any mixed corner supplies an actual
attachable cycle paid by the very certificate used to select the arcs. -/
theorem attachment_of_return {D V q F p} (hq : 2≤q) (safe : QFree D V q)
    (dual : RealDual q (graph D F) V 1 p) :
    let E := graph D F
    let H := affordable q D V F p
    ∀u∈V,∀v∈V,∀w∈V,H u v=true → H v w=true → E u v≠E v w → u∈ball H V w (q-1) →
      ∃B,SharedArcInduction.Next D V q F B ∧ RealDual q (graph D (insert B F)) V 1 p := by
  classical
  intro E H
  have native {a b} (ed : H a b=true) : D a b=true := (parts ed).1
  have lift {a b l} (path : Walk H V a b l) : Walk D V a b l := by
    induction path with
    | refl => exact .refl _
    | step j ed _ ih => exact .step j (native ed) ih
  have free : QFree H V q := fun a l lo hi path => safe a l lo hi (lift path)
  intro u uv v vv w wv a b diff reach
  obtain ⟨B,cb,ub,vb,wb⟩ := FiniteHorizonHall.marked_of_port hq free vv (mem_outN.mpr ⟨wv,b⟩)
    (mem_inN.mpr ⟨uv,a⟩) reach
  have minDeg (i) (ib : i∈B) : 1≤(outN D B i).card := by
    rw [←cb.heads i ib]
    exact card_le_card (fun j hj => mem_outN.mpr ⟨(mem_outN.mp hj).1,native (mem_outN.mp hj).2⟩)
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (safe.mono_set cb.sub) minDeg (by simpa using cb.size)
  have cD : Cycle D V q B := ⟨cb.sub,cb.size,reg.1,reg.2⟩
  have kept {i j} (ib : i∈B) (jb : j∈B) (ij : D i j=true) : H i j=true := by
    obtain ⟨k,kh⟩ := card_pos.mp (show 0<(outN H B i).card by rw [cb.heads i ib]; decide)
    obtain ⟨kb,ik⟩ := mem_outN.mp kh
    obtain rfl : j=k := card_le_one.mp (cD.heads i ib).le _ (mem_outN.mpr ⟨jb,ij⟩) _ (mem_outN.mpr ⟨kb,native ik⟩)
    exact ik
  have off : B∉F := fun inF => diff (show E u v=E v w from
    (active.mpr ⟨B,mem_col.mpr ⟨inF,ub,vb,native a⟩⟩).trans (active.mpr ⟨B,mem_col.mpr ⟨inF,vb,wb,native b⟩⟩).symm)
  have touch {i j} (ib : i∈B) (jb : j∈B) (ij : E i j=true) : ∃A∈F,Touch D A B := by
    obtain ⟨A,hit⟩ := active.mp ij
    obtain ⟨af,ia,ja,ed⟩ := mem_col.mp hit
    exact ⟨A,af,i,mem_inter.mpr ⟨ia,ib⟩,j,mem_inter.mpr ⟨ja,jb⟩,ed⟩
  have mixed : ∃A∈F,Touch D A B := by
    cases eu : E u v with
    | true => exact touch ub vb eu
    | false => exact touch vb wb (by cases ew : E v w <;> simp_all)
  refine ⟨B,⟨cD,off,mixed⟩,(SharedArcBudget.fits_iff cD dual).mpr ?_⟩
  intro i ib j jb ij missing
  exact (parts (kept ib jb ij)).2.resolve_left (fun old => Bool.noConfusion (missing.symm.trans old))

/-- A mixed two-arc turn using individually affordable arcs has no
affordable return within q−1 at a maximal family. A native return of that
length must therefore use some other arc on which the budget fails. -/
theorem separator {q n} (X : Model q n) (hq : 2≤q) {F : Family} {p}
    (dual : RealDual q (graph X.D F) X.V 1 p)
    (stop : ∀B,Boundary X F B → ¬SmallRow q (graph X.D (insert B F)) X.V) :
    let E := graph X.D F
    let H := affordable q X.D X.V F p
    ∀u∈X.V,∀v∈X.V,∀w∈X.V,H u v=true → H v w=true → E u v≠E v w →
      u∉ball H X.V w (q-1) ∧ (X.D u w=false → ∃m,m=q-1 ∧ Walk X.D X.V w u m ∧ ¬Walk H X.V w u m) := by
  classical
  intro E H
  have native {a b} (ed : H a b=true) : X.D a b=true := (parts ed).1
  intro u uv v vv w wv a b diff
  have absent : u∉ball H X.V w (q-1) := by
    intro reach
    obtain ⟨M,next,paid⟩ := attachment_of_return hq X.free dual u uv v vv w wv a b diff reach
    exact stop M ⟨mem_filter.mpr ⟨mem_powerset.mpr next.1.sub,next.1⟩,next.2⟩ (smallRow_of_realDual paid)
  refine ⟨absent,fun skip => ?_⟩
  obtain ⟨_,m,lim,ret⟩ := mem_ball.mp (X.sat w wv u uv (by simp [skip]))
  have len : m=q-1 := by
    by_contra ne
    exact X.free u _ (by omega) (by omega) (.step vv (native a) (.step wv (native b) ret))
  exact ⟨m,len,ret,fun path => absent (mem_ball.mpr ⟨uv,m,lim,path⟩)⟩

#print axioms separator
private theorem follow {D A} {P : ℕ→Prop}
    (closed : ∀u∈A,∀v∈A,D u v=true → P u → P v)
    {i j n} (walk : Walk D A i j n) (ic : i∈A) (pi : P i) : P j := by
  induction walk with
  | refl => exact pi
  | step vn ij _ ih => exact ih vn (closed _ ic _ vn ij pi)

/-- The *same* old/new turn witnesses the alternative for every old dual.
Its existence and its native return are independent of the prices. -/
theorem boundary_turn {q n} (X : Model q n) (hq : 2≤q) {F B}
    (step : Boundary X F B) (good : SmallRow q (graph X.D F) X.V)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) :
    let E := graph X.D F
    ∃u∈B,∃v∈B,∃w∈B,E u v=true ∧ E v w=false ∧ X.D u v=true ∧ X.D v w=true ∧
      X.D u w=false ∧ Walk X.D X.V w u (q-1) ∧
      ∀p,RealDual q E X.V 1 p →
        1<realCol q E X.V p w+q*p v ∨
          (affordable q X.D X.V F p v w=true ∧ u∉ball (affordable q X.D X.V F p) X.V w (q-1)) := by
  classical
  intro E
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  obtain ⟨p,dual⟩ := realDual_of_smallRow good X.live
  obtain ⟨i,ib,j,jb,ij,missing,_⟩ := price cb dual (stop B step)
  obtain ⟨A,af,a,aa,b,bb,ab⟩ := step.2.2
  have seedArc : E a b=true := active.mpr ⟨A,mem_col.mpr ⟨af,(mem_inter.mp aa).1,(mem_inter.mp bb).1,ab⟩⟩
  have mixed : ∃u∈B,∃v∈B,∃w∈B,E u v=true ∧ E v w=false ∧ X.D u v=true ∧ X.D v w=true := by
    by_contra no
    let P := fun u => ∃v∈B,X.D u v=true ∧ E u v=true
    have edge {u v} (ub : u∈B) (vb : v∈B) (uv : X.D u v=true) (pu : P u) : E u v=true := by
      obtain ⟨t,tb,ut,pay⟩ := pu
      exact (card_le_one.mp (cb.heads u ub).le _ (mem_outN.mpr ⟨tb,ut⟩) _ (mem_outN.mpr ⟨vb,uv⟩)) ▸ pay
    have closed (u) (ub : u∈B) (v) (vb : v∈B) (uv : X.D u v=true) (pu : P u) : P v := by
      obtain ⟨w,wh⟩ := card_pos.mp (show 0<(outN X.D B v).card by rw [cb.heads v vb]; decide)
      obtain ⟨wb,vw⟩ := mem_outN.mp wh
      refine ⟨w,wb,vw,?_⟩
      cases e : E v w
      · exact (no ⟨u,ub,v,vb,w,wb,edge ub vb uv pu,e,uv,vw⟩).elim
      · rfl
    obtain ⟨_,_,path,_⟩ := MandatoryExcursion.segments (by omega : 1≤q) X.free cb (mem_inter.mp aa).2 ib
    have pi := follow closed path (mem_inter.mp aa).2 ⟨b,(mem_inter.mp bb).2,ab,seedArc⟩
    exact Bool.noConfusion (missing.symm.trans (edge ib jb ij pi))
  obtain ⟨u,ub,v,vb,w,wb,old,newArc,uv,vw⟩ := mixed
  have miss : X.D u w=false := Bool.eq_false_iff.mpr (fun uw => by
    obtain rfl : v=w := card_le_one.mp (cb.heads u ub).le _ (mem_outN.mpr ⟨vb,uv⟩) _ (mem_outN.mpr ⟨wb,uw⟩)
    exact loopfree X.free (by omega : 1≤q) (cb.sub vb) vw)
  have ret := NativeSharedSegment.complement (by omega : 1≤q) X.free cb ub
    (.step vb uv (.step wb vw (.refl _)) : Walk X.D B u w 2) (by omega)
  refine ⟨u,ub,v,vb,w,wb,old,newArc,uv,vw,miss,by simpa [show q+1-2=q-1 by omega] using ret.mono cb.sub,?_⟩
  intro r hr
  by_cases expensive : 1<realCol q E X.V r w+q*r v
  · exact Or.inl expensive
  have h1 : affordable q X.D X.V F r u v=true := decide_eq_true (And.intro uv (Or.inl old))
  have h2 : affordable q X.D X.V F r v w=true := decide_eq_true (And.intro vw (Or.inr (le_of_not_gt expensive)))
  exact Or.inr ⟨h2,(separator X hq hr stop u (cb.sub ub) v (cb.sub vb) w (cb.sub wb) h1 h2
    (by change E u v≠E v w; rw [old,newArc]; decide)).1⟩

/-- The remaining target in terms of three labels and one bounded path. -/
def ReturnLaw (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀C F,Built D C F → (∀M∈F,Cycle D V q M) → support F=V → SmallRow q (graph D F) V →
    (∃B,SharedArcInduction.Next D V q F B) →
    (∀B,SharedArcInduction.Next D V q F B → ∃u∈B,∃v∈B,D u v=true ∧ graph D F u v=false) →
    ∃p,RealDual q (graph D F) V 1 p ∧
      let E := graph D F
      let H := affordable q D V F p
      ∃u∈V,∃v∈V,∃w∈V,H u v=true ∧ H v w=true ∧ E u v≠E v w ∧ u∈ball H V w (q-1)

theorem extension_of_return {q D V} (hq : 2≤q) (free : QFree D V q) (law : ReturnLaw q D V) :
    SharedArcInduction.ExtensionLaw q D V := by
  classical
  intro C F built cycles cover good next
  by_cases fresh : ∀B,SharedArcInduction.Next D V q F B → ∃u∈B,∃v∈B,D u v=true ∧ graph D F u v=false
  swap
  · push Not at fresh
    obtain ⟨B,step,unchanged⟩ := fresh
    have live : V.Nonempty := (card_pos.mp (by rw [step.1.size]; omega : 0<B.card)).mono step.1.sub
    obtain ⟨p,pay⟩ := realDual_of_smallRow good live
    exact ⟨B,step,p,pay,fun u ub v vb uv off => (unchanged u ub v vb uv off).elim⟩
  obtain ⟨p,dual,u,uv,v,vv,w,wv,a,b,diff,path⟩ := law C F built cycles cover good next fresh
  obtain ⟨B,step,paid⟩ := attachment_of_return hq free dual u uv v vv w wv a b diff path
  exact ⟨B,step,p,dual,(SharedArcBudget.fits_iff step.1 dual).mp paid⟩

theorem ch_of_return (law : ∀q n,∀X : Model q n,2≤q → SmallerSmallRow q X.V.card → ReturnLaw q X.D X.V) :
    CH.CaccettaHaggkvistConjecture :=
  SharedArcInduction.ch_of_extension (fun q n X hq small => extension_of_return hq X.free (law q n X hq small))

#print axioms attachment_of_return
#print axioms boundary_turn
#print axioms ch_of_return
end LeanCH.BR.Closure.SharedArcAffordablePaths
