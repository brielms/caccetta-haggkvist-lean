import checkpoints.shen_extension.ClassParentBanks
import LeanCH.BR.BRsubSat

namespace LeanCH.BR.Closure.SaturatedCycleClasses
open Finset BRq2 BRq3 BR45 DeficitLevels ShortestCycleClasses ShenMinimumOrder

/-- A missing shortcut in a saturated graph completes the specified two arcs
to an induced shortest cycle, retaining all three original labels. -/
theorem missing {D V q a b c} (hq : 2≤q) (hf : QFree D V q) (sat : BRsub.Sat q D V)
    (av : a∈V) (bv : b∈V) (cv : c∈V) (ab : D a b=true) (bc : D b c=true)
    (miss : ¬D a c=true) :
    ∃M, ShenCycleSuccessor.Cycle D V q M ∧ a∈M ∧ b∈M ∧ c∈M := by
  obtain ⟨_,m,le,back⟩ := mem_ball.mp (sat c cv a av miss)
  have len : m=q-1 := by
    by_contra ne
    exact hf a (m+1+1) (by omega) (by omega) (.step bv ab (.step cv bc back))
  subst m
  exact ShenCycleSuccessor.marked_cycle hq hf bv cv ab bc
    (DeleteRepair.head_avoided hf bv ab back (by omega))

/-- A cut crossed by any returning arc in U has a two-arc path on original U
labels crossing that cut for which the direct shortcut is missing. -/
theorem open_triple {D U} (color : ℕ→Prop) {k x y} (xu : x∈U) (yu : y∈U)
    (xy : D x y=true) (back : Walk D U y x k) (cross : ¬(color x ↔ color y))
    (free : QFree D U 2) :
    ∃a∈U,∃b∈U,∃c∈U,D a b=true ∧ D b c=true ∧ ¬D a c=true ∧
      (¬(color a ↔ color b) ∨ ¬(color b ↔ color c)) := by
  classical
  match k, back with
  | 0, .refl _ => exact False.elim (cross Iff.rfl)
  | 1, .step _ yx (.refl _) => exact False.elim (free x 2 (by decide) le_rfl (.step yu xy (.step xu yx (.refl _))))
  | k+2, .step wu yw tail =>
    rename_i w
    by_cases xw : D x w=true
    · by_cases same : color x ↔ color w
      · obtain ⟨z,path,_,zx⟩ := tail.unsnoc
        have zu := path.end_mem_or.elim (fun eq => eq ▸ wu) id
        by_cases zy : D z y=true
        · exact open_triple color yu wu yw (path.snoc yu zy) (fun eq => cross (same.trans eq.symm)) free
        · exact ⟨z,zu,x,xu,y,yu,zx,xy,zy,Or.inr cross⟩
      · exact open_triple color xu wu xw tail same free
    · exact ⟨x,xu,y,yu,_,wu,xy,yw,xw,Or.inl cross⟩
termination_by k

/-- Saturation is needed only in the ambient graph. The two marked arcs of
the shortest cycle stay inside the prescribed carrier. -/
theorem cut_witness {D V U q x y k} (hq : 2≤q) (hf : QFree D V q) (sat : BRsub.Sat q D V)
    (uv : U⊆V) (color : ℕ→Prop) (xu : x∈U) (yu : y∈U) (xy : D x y=true)
    (back : Walk D U y x k) (cross : ¬(color x↔color y)) :
    ∃a∈U,∃b∈U,∃c∈U,D a b=true ∧ D b c=true ∧
      (¬(color a↔color b) ∨ ¬(color b↔color c)) ∧
      ∃M, ShenCycleSuccessor.Cycle D V q M ∧ a∈M ∧ b∈M ∧ c∈M := by
  obtain ⟨a,au,b,bu,c,cu,ab,bc,miss,split⟩ :=
    open_triple color xu yu xy back cross ((hf.mono_set uv).mono_bound hq)
  exact ⟨a,au,b,bu,c,cu,ab,bc,split,missing hq hf sat (uv au) (uv bu) (uv cu) ab bc miss⟩

theorem returning_arc {D V q x y k} (hq : 2≤q) (hf : QFree D V q) (sat : BRsub.Sat q D V)
    (xv : x∈V) (yv : y∈V) (xy : D x y=true) (back : Walk D V y x k) :
    y∈carrier D V q x := by
  classical
  by_contra outside
  obtain ⟨a,_,b,_,c,_,_,_,split,M,cy,am,bm,cm⟩ :=
    cut_witness hq hf sat Subset.rfl (fun i => i∈carrier D V q x) xv yv xy back
      (fun eq => outside (eq.mp (contains xv)))
  have iff_mem {i j} (im : i∈M) (jm : j∈M) :
      i∈carrier D V q x ↔ j∈carrier D V q x := by
    have eq := same_class (show Together D V q i j from ⟨M,cy.sub,cy.size,cy.heads,im,jm⟩)
    constructor
    · intro h
      rw [ClassParentBanks.class_eq h,eq]
      exact contains (cy.sub jm)
    · intro h
      rw [ClassParentBanks.class_eq h,←eq]
      exact contains (cy.sub im)
  exact split.elim (fun no => no (iff_mem am bm)) (fun no => no (iff_mem bm cm))

private theorem reaches {q s} (X : Source q s) {x y} (xv : x∈X.V) (yv : y∈X.V) :
    ∃k,Walk X.D X.V x y k := by
  classical
  let W := X.V.filter (fun a => ∃k,Walk X.D X.V x a k)
  have sub : W⊆X.V := filter_subset _ _
  have deg (a) (aw : a∈W) : s≤(outN X.D W a).card := by
    apply (X.degree a (sub aw)).trans
    apply card_le_card
    intro z zh
    obtain ⟨k,p⟩ := (mem_filter.mp aw).2
    have ⟨zv,az⟩ := mem_outN.mp zh
    exact mem_outN.mpr ⟨mem_filter.mpr ⟨zv,k+1,p.snoc zv az⟩,az⟩
  have live : W.Nonempty := ⟨x,mem_filter.mpr ⟨xv,0,.refl _⟩⟩
  have eq := eq_of_subset_of_card_le sub (X.least X.D W (X.free.mono_set sub) deg live)
  exact (mem_filter.mp (show y∈W from eq.symm ▸ yv)).2

theorem one_class {q s} (X : Source q s) (hq : 2≤q) (sat : BRsub.Sat q X.D X.V)
    {x} (xv : x∈X.V) : carrier X.D X.V q x=X.V := by
  classical
  apply Subset.antisymm (filter_subset _ _)
  intro y yv
  obtain ⟨k,path⟩ := reaches X xv yv
  induction path with
  | refl => exact contains xv
  | @step a b c k bv ab _ ih =>
    obtain ⟨j,back⟩ := reaches X bv xv
    change c∈carrier X.D X.V q a
    rw [ClassParentBanks.class_eq (returning_arc hq X.free sat xv bv ab back)]
    exact ih bv yv

theorem saturated_origin {q s} (O : Origin q s) (hq : 2≤q) :
    ∃S : Origin q s, S.V=O.V ∧ BRsub.Sat q S.G S.V ∧
      (∀x∈O.V,∀y∈O.V,O.G x y=true → S.G x y=true) ∧
      ∀x∈S.V,carrier S.G S.V q x=S.V := by
  obtain ⟨E,extE,ef,sat⟩ := BRsub.exists_satQ O.free
  have deg (x) (hx : x∈O.V) : s≤(outN E O.V x).card :=
    (O.deg x hx).trans (card_le_card (fun y hy => mem_outN.mpr
      ⟨outN_subset hy,extE x hx y (outN_subset hy) (mem_outN.mp hy).2⟩))
  let S : Origin q s := ⟨E,O.V,O.ne,O.order,ef,O.least,deg⟩
  let X : Source q s := ⟨E,O.V,O.ne,ef,deg,O.least⟩
  exact ⟨S,rfl,sat,extE,fun _ hx => one_class X hq sat hx⟩

#print axioms saturated_origin
#print axioms cut_witness
#print axioms one_class
end LeanCH.BR.Closure.SaturatedCycleClasses
