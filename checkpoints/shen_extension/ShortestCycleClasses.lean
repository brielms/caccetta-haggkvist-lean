import checkpoints.shen_extension.CutoffDegreeRank

namespace LeanCH.BR.Closure.ShortestCycleClasses
open Finset BRq2 BRq3 BR45 DeficitLevels CutoffDegreeRank

def Together (D : CH.Digraph) (V : Finset ℕ) (q x y : ℕ) : Prop :=
  ∃M⊆V, M.card=q+1 ∧ OutEq 1 D M ∧ x∈M ∧ y∈M

noncomputable def carrier (D : CH.Digraph) (V : Finset ℕ) (q x : ℕ) : Finset ℕ := by
  classical exact V.filter (Relation.EqvGen (Together D V q) x)

theorem same_class {D V q x y} (link : Together D V q x y) :
    carrier D V q x=carrier D V q y := by
  classical
  have rel := Relation.EqvGen.rel x y link
  ext a
  simp only [carrier,mem_filter]
  exact and_congr_right (fun _ => ⟨fun path => .trans _ _ _ (.symm _ _ rel) path,
    fun path => .trans _ _ _ rel path⟩)

theorem contains {D V q x} (xv : x∈V) : x∈carrier D V q x := by
  classical
  exact mem_filter.mpr ⟨xv,.refl _⟩

/-- Any proper overlap class has an original in-degree bottleneck, or
has size exceeding s if all its vertices have in-degree at least s. -/
theorem bottleneck {q s} (O : Origin q s) (hq : 2≤q) (laws : ∀j<s, OrderLaw q j (q*j+1))
    {x} (xv : x∈O.V) (proper : (carrier O.G O.V q x).card<O.V.card) :
    let C := carrier O.G O.V q x
    ∃h∈C,(inN O.G O.V h).card+q*((outN O.G O.V h).card-s)+1≤C.card := by
  classical
  apply ReturnArcRecurrence.recurrent O hq laws (filter_subset _ _) proper ⟨x,contains xv⟩
  intro h hc a ha
  obtain ⟨_,M,c,hm,am⟩ := ReturnArcRecurrence.cycle_of_first O hq (mem_filter.mp hc).1 ha
  have link : Together O.G O.V q h a := ⟨M,c.sub,c.size,c.heads,hm,am⟩
  exact mem_filter.mpr ⟨c.sub am, .trans _ _ _ (mem_filter.mp hc).2 (.rel _ _ link)⟩

private def edited (D : CH.Digraph) (Z : ℕ→Finset ℕ) : CH.Digraph := fun x y =>
  D x y && decide (y∉Z x)

private theorem lift {D V Z x y k} (p : Walk (edited D Z) V x y k) : Walk D V x y k := by
  induction p with
  | refl => exact .refl _
  | step yw edge _ ih => exact .step yw (Bool.and_eq_true_iff.mp edge).1 ih

/-- Independently prescribe a different forbidden head set for every row.
An original shortest cycle avoids every prescribed outgoing arc. -/
theorem escapes_rows {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    (mark : ℕ→Finset ℕ) {k : ℕ} (cap : ∀x∈O.V,(mark x).card≤k)
    (budget : O.V.card≤(q+1)*(s-k)) :
    ∃M⊆O.V, M.card=q+1 ∧ OutEq 1 O.G M ∧ ∀x∈M,∀y∈outN O.G M x,y∉mark x := by
  classical
  let E := edited O.G mark
  have ef : QFree E O.V q := fun x n pos le p => O.free x n pos le (lift p)
  have degree (x) (xv : x∈O.V) : s-k≤(outN E O.V x).card := by
    have sub : outN O.G O.V x⊆outN E O.V x∪mark x := by
      intro z hz
      obtain ⟨zv,xz⟩ := mem_outN.mp hz
      by_cases zm : z∈mark x
      · exact mem_union_right _ zm
      · exact mem_union_left _ (mem_outN.mpr ⟨zv,by simp [E,edited,xz,zm]⟩)
    have mx := (card_le_card sub).trans (card_union_le _ _)
    have le : (mark x).card≤k := cap x xv
    have dg := O.deg x xv
    omega
  obtain ⟨M,mv,sz,one⟩ := surviving_edit O hb rank le_rfl ef O.ne (Nat.sub_le _ _) budget degree
  have lo (x) (xm : x∈M) : 1≤(outN O.G M x).card := by
    rw [←one x xm]
    exact card_le_card (fun z hz => mem_outN.mpr ⟨(mem_outN.mp hz).1,
      (Bool.and_eq_true_iff.mp (mem_outN.mp hz).2).1⟩)
  have hq := hb.trans rank.1
  have regG := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (O.free.mono_set mv) lo (by simpa using sz)
  refine ⟨M,mv,sz,regG.1,?_⟩
  intro x xm y yh
  have inc : outN E M x⊆outN O.G M x := fun z hz => mem_outN.mpr
    ⟨(mem_outN.mp hz).1,(Bool.and_eq_true_iff.mp (mem_outN.mp hz).2).1⟩
  have eq := eq_of_subset_of_card_le inc (by rw [regG.1 x xm,one x xm])
  have ye : y∈outN E M x := eq.symm ▸ yh
  have allowed := (Bool.and_eq_true_iff.mp (mem_outN.mp ye).2).2
  simpa using allowed

/-- A ranked source has an overlap class whose shortest cycles escape
any k prescribed labels per class. The per-row deletion budget is k even when different classes choose disjoint marks. -/
theorem escapes_marks {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    (Z : Finset ℕ→Finset ℕ) {k : ℕ} (cap : ∀x∈O.V,(Z (carrier O.G O.V q x)).card≤k)
    (budget : O.V.card≤(q+1)*(s-k)) :
    ∃M⊆O.V, M.card=q+1 ∧ OutEq 1 O.G M ∧ ∀x∈M, x∉Z (carrier O.G O.V q x) := by
  obtain ⟨M,mv,sz,one,allowed⟩ := escapes_rows O hb rank (fun x => Z (carrier O.G O.V q x)) cap budget
  have hq := hb.trans rank.1
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (O.free.mono_set mv)
    (fun x xm => (one x xm).ge) (by simpa using sz)
  refine ⟨M,mv,sz,one,?_⟩
  intro x xm
  obtain ⟨a,ax⟩ := card_pos.mp (show 0<(inN O.G M x).card by rw [reg.2 x xm]; decide)
  obtain ⟨am,edge⟩ := mem_inN.mp ax
  have same := same_class (show Together O.G O.V q a x from ⟨M,mv,sz,one,am,xm⟩)
  simpa only [same] using allowed a am x (mem_outN.mpr ⟨xm,edge⟩)

/-- One and the same overlap class defeats *every* k-label transversal.
The witness cycle may depend on the choice of those k labels. -/
theorem hard_class {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    {k : ℕ} (budget : O.V.card≤(q+1)*(s-k)) :
    ∃x∈O.V, ∀Z : Finset ℕ, Z.card≤k → ∃M⊆carrier O.G O.V q x,
      M.card=q+1 ∧ OutEq 1 O.G M ∧ Disjoint M Z := by
  classical
  let cover (C Z : Finset ℕ) : Prop := Z.card≤k ∧ ∀M⊆C, M.card=q+1 →
    OutEq 1 O.G M → ¬Disjoint M Z
  by_contra! none
  have haveCover (x) (xv : x∈O.V) : ∃Z,cover (carrier O.G O.V q x) Z := by
    obtain ⟨Z,le,bad⟩ := none x xv
    exact ⟨Z,le,fun M mc sz deg => bad M mc sz deg⟩
  let mark (C : Finset ℕ) := if h : ∃Z,cover C Z then h.choose else ∅
  have spec (x) (xv : x∈O.V) : cover (carrier O.G O.V q x) (mark (carrier O.G O.V q x)) := by
    have ex := haveCover x xv
    simpa [mark,ex] using ex.choose_spec
  obtain ⟨M,mv,sz,one,unmarked⟩ := escapes_marks O hb rank mark (fun x xv => (spec x xv).1) budget
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<M.card by omega)
  have pair (y) (ym : y∈M) : Together O.G O.V q x y := ⟨M,mv,sz,one,xm,ym⟩
  have mc : M⊆carrier O.G O.V q x := fun y ym => mem_filter.mpr ⟨mv ym,.rel _ _ (pair y ym)⟩
  apply (spec x (mv xm)).2 M mc sz one
  exact disjoint_left.mpr (fun y ym marked => unmarked y ym (same_class (pair y ym) ▸ marked))

theorem two_linked_cycles {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    (budget : O.V.card≤(q+1)*(s-(q+1))) :
    ∃x∈O.V, ∃A⊆carrier O.G O.V q x, ∃B⊆carrier O.G O.V q x,
      A.card=q+1 ∧ B.card=q+1 ∧ OutEq 1 O.G A ∧ OutEq 1 O.G B ∧ Disjoint A B := by
  obtain ⟨x,xv,escape⟩ := hard_class O hb rank budget
  obtain ⟨A,ac,az,one,_⟩ := escape ∅ (by simp)
  obtain ⟨B,bc,bz,two,dis⟩ := escape A az.le
  exact ⟨x,xv,A,ac,B,bc,az,bz,one,two,dis.symm⟩

#print axioms two_linked_cycles
#print axioms escapes_rows
#print axioms hard_class
#print axioms same_class
#print axioms bottleneck
#print axioms escapes_marks
end LeanCH.BR.Closure.ShortestCycleClasses
