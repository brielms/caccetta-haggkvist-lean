import checkpoints.shen_extension.SingleArcMidpointSign

namespace LeanCH.BR.Closure.SingleArcCycleParents
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

private theorem avoid_root {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} {a j i t m : ℕ}
    (free : QFree E V q) (pre : Walk E V a j t) (path : Walk E V j i m) (budget : t+m≤q) :
    Walk E (V \ {a}) j i m := by
  induction path generalizing t with
  | refl => exact .refl _
  | @step j u i m uv ju tail ih =>
    have nex := pre.snoc uv ju
    have ne : u≠a := by rintro rfl; exact free _ (t+1) (by omega) (by omega) nex
    exact .step (mem_sdiff.mpr ⟨uv,by simpa using ne⟩) ju (ih nex (by omega))

private theorem host_regular {q : ℕ} (hq : 2≤q) {E D : CH.Digraph} {V C : Finset ℕ}
    (free : QFree D V q) (sub : ∀i j,E i j=true → D i j=true) (cy : Cycle E V q C) :
    Cycle D V q C := by
  have min (i) (ic : i∈C) : 1≤(outN D C i).card := by
    rw [←cy.heads i ic]
    apply card_le_card
    intro j hj
    exact mem_outN.mpr ⟨(mem_outN.mp hj).1,sub _ _ (mem_outN.mp hj).2⟩
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (free.mono_set cy.sub)
    min (by simpa using cy.size)
  exact ⟨cy.sub,cy.size,reg.1,reg.2⟩

/-- On a shortest cycle containing the fixed old arc, the new head
is exterior. Saturation and the induction hypothesis are unnecessary. -/
theorem head_outside {q : ℕ} (hq : 2≤q) {E D : CH.Digraph} {V C : Finset ℕ}
    (free : QFree D V q) (sub : ∀i j,E i j=true → D i j=true) (cy : Cycle E V q C)
    {a b v : ℕ} (ac : a∈C) (vc : v∈C) (av : E a v=true) (off : E a b=false)
    (ab : D a b=true) : b∉C := by
  intro bc
  have ne : b≠v := fun e=>Bool.noConfusion (off.symm.trans (e ▸ av))
  have both : ({b,v}:Finset ℕ)⊆outN D C a := insert_subset_iff.mpr ⟨mem_outN.mpr ⟨bc,ab⟩,
    singleton_subset_iff.mpr (mem_outN.mpr ⟨vc,sub _ _ av⟩)⟩
  have size := card_le_card both
  rw [card_pair ne,(host_regular hq free sub cy).heads a ac] at size
  omega

/-- With an old two-step path through the midpoint, its shortest old
cycles record exactly whether the shortcut creates a forbidden cycle. -/
theorem legal_iff {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q) (a b v : V) (av : E a v=true) (vb : E v b=true) (off : E a b=false) :
    QFree (insertArc E a b) V q ↔ ∀C, Cycle E V q C → a.val∈C → v.val∈C → b.val∉C := by
  constructor
  · intro safe C cy ac vc
    exact head_outside hq safe (insertArc_mono E a b) cy ac vc av off (by simp [insertArc])
  · intro allC
    apply qfree_insertArc free a b
    intro hit
    obtain ⟨_,m,le,w⟩ := mem_ball.mp hit
    have floor : q<m+2 := by
      by_contra! low
      exact free a (m+1+1) (by omega) (by omega) (.step v.property av (.step b.property vb w))
    have path := avoid_root free (Walk.step b.property vb (.refl _)) w (by omega)
    have len : m=q-1 := by omega
    obtain ⟨C,cy,ac,vc,bc⟩ := marked_cycle hq free v.property b.property av vb (len ▸ path)
    exact allC C cy ac vc bc

/-- Each parent in the diagonal sum has a genuine old cycle through it,
the tail and the midpoint. If it misses the new head, a second length-q+1
return through that head uses the same final old arc into the tail. -/
theorem paired {q n} (X : Model q n) (hq : 2≤q) (F : Family) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (v i : X.V)
    (av : graph X.D F f.val.1 v=true) (ia : graph X.D F i f.val.1=true) (iv : graph X.D F i v=false) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    (∃C,Cycle E X.V q C ∧ a.val∈C ∧ v.val∈C ∧ i.val∈C ∧ b.val∉C) ∧
    (E i b=false ↔ Walk E (X.V \ {a.val}) b i (q-1)) := by
  intro E a b
  have edge (j k) (ed : E j k=true) : X.D j k=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have free := PrivateArcEndpoints.graph_free X F
  have path := (SingleArcMidpointSign.return_layer X hq F f single v i av ia).mp iv
  have root := avoid_root free (Walk.step v.property av (.refl _)) path (by omega)
  obtain ⟨C,cy,ic,ac,vc⟩ := marked_cycle hq free a.property v.property ia av root
  refine ⟨⟨C,cy,ac,vc,ic,head_outside hq X.free edge cy ac vc av f.property.2 f.property.1⟩,?_⟩
  have only (j) (jv : j∈X.V) (k) (kv : k∈X.V) (ed : X.D j k=true) : E j k=true ∨ (j=a.val ∧ k=b.val) := by
    by_cases old : E j k=true
    · exact Or.inl old
    · let g : SharedArcFlatCut.Missing X F := ⟨(⟨j,jv⟩,⟨k,kv⟩),ed,Bool.eq_false_iff.mpr old⟩
      exact Or.inr ⟨congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.1.val) (single g),
        congrArg (fun z : SharedArcFlatCut.Missing X F=>z.val.2.val) (single g)⟩
  constructor
  · intro miss
    have ine : i.val≠a.val := fun eq=>loopfree free (by omega) a.property ((congrArg (fun j=>E j a) eq).symm.trans ia)
    have absent : ¬X.D i b=true := fun ed=>Bool.noConfusion (miss.symm.trans
      ((only _ i.property _ b.property ed).resolve_right (fun h=>ine h.1)))
    have ballEq := (SingleArcReturnProfile.balls (by omega : 1≤q) X.free X.sat edge only b.property f.property.1).2
    have hit : i.val∈ball E X.V b (q-1) := by
      rw [ballEq]; exact mem_sdiff.mpr ⟨i.property,fun p=>absent (mem_inN.mp p).2⟩
    obtain ⟨_,m,le,w⟩ := mem_ball.mp hit
    have floor : q<m+2 := by
      by_contra! low
      exact X.free a (m+1+1) (by omega) (by omega) (.step b.property f.property.1 ((walk_sub edge w).snoc a.property (edge _ _ ia)))
    have trim {u k l t : ℕ} (w' : Walk E X.V u k l) (pre : Walk X.D X.V a u t) (budget : t+l≤q) :
        Walk E (X.V \ {a.val}) u k l := by
      induction w' generalizing t with
      | refl => exact .refl _
      | @step j z k l zv jz rest ih =>
        have next := pre.snoc zv (edge _ _ jz)
        have ne : z≠a.val := fun eq=>X.free a (t+1) (by omega) (by omega) (eq ▸ next)
        exact .step (mem_sdiff.mpr ⟨zv,by simpa using ne⟩) jz (ih next (by omega))
    exact (by omega : m=q-1) ▸ trim w (.step b.property f.property.1 (.refl _)) (by omega)
  · intro w
    exact Bool.eq_false_iff.mpr (fun ib=>free i (q-1+1) (by omega) (by omega) (.step b.property ib (w.mono sdiff_subset)))

/-- The parent sum is nonempty by the flat column merge. In particular
the family of old cycles through the marked edge has a member. -/
theorem supply {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (v : X.V) (av : graph X.D F f.val.1 v=true) :
    ∃i : X.V,graph X.D F i f.val.1=true ∧ graph X.D F i v=false ∧
      ∃C,Cycle (graph X.D F) X.V q C ∧ f.val.1.val∈C ∧ v.val∈C ∧ i.val∈C ∧ f.val.2.val∉C := by
  let E := graph X.D F
  let a := f.val.1
  have free := PrivateArcEndpoints.graph_free X F
  have ne : a.val≠v.val := fun eq=>loopfree free (by omega) v.property ((congrArg (fun j=>E j v) eq).symm.trans av)
  have bill := (SharedArcPivotMerge.flat_pair_non_domination hq free small wp wm
    (HeirExit.mass_col_of_flat wm wr pc) wr pc a.property v.property ne).2.2.2
  have live : (inN E X.V a \ inN E X.V v).Nonempty := by
    by_contra empty
    change p v≤(q:ℚ)*mass (inN E X.V a \ inN E X.V v) p at bill
    rw [not_nonempty_iff_eq_empty.mp empty] at bill
    simp only [mass,sum_empty,mul_zero] at bill
    exact (wp v v.property).2.not_ge bill
  obtain ⟨i,hi⟩ := live
  obtain ⟨ii,miss⟩ := mem_sdiff.mp hi
  obtain ⟨iv,ia⟩ := mem_inN.mp ii
  have off : E i v=false := Bool.eq_false_iff.mpr (fun h=>miss (mem_inN.mpr ⟨iv,h⟩))
  exact ⟨⟨i,iv⟩,ia,off,(paired X hq F f single v ⟨i,iv⟩ av ia off).1⟩

end LeanCH.BR.Closure.SingleArcCycleParents
#print axioms LeanCH.BR.Closure.SingleArcCycleParents.head_outside
#print axioms LeanCH.BR.Closure.SingleArcCycleParents.legal_iff
#print axioms LeanCH.BR.Closure.SingleArcCycleParents.paired
#print axioms LeanCH.BR.Closure.SingleArcCycleParents.supply
