import checkpoints.shen_extension.ClassPunctureRecurrence

namespace LeanCH.BR.Closure.MarkedCyclePeeling
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights ShenPrimeTransition

abbrev Family := Finset (Finset ℕ)
abbrev Arc := ℕ × ℕ

def Uses (D : CH.Digraph) (C : Finset ℕ) (e : Arc) : Prop :=
  e.1∈C ∧ e.2∈C ∧ D e.1 e.2=true

noncomputable def col (D : CH.Digraph) (F : Family) (e : Arc) : Family := by
  classical exact F.filter (fun C => Uses D C e)

theorem mem_col {D F e C} : C∈col D F e ↔ C∈F ∧ Uses D C e := by
  classical exact mem_filter

/-- The discarded arc witnesses, the affected rows and columns, and the
retained marked cycle are on their original labels. -/
structure Cut (D : CH.Digraph) (M : Finset ℕ) (F G : Family) : Prop where
  marked : M∈G
  less : G ⊂ F
  packet : ∃e : Arc,(col D F e).Nonempty ∧ G=F\col D F e ∧
    (∀f : Arc,(col D F f).Nonempty → (col D G f=∅ ↔ col D F f=col D F e)) ∧
    (∀f g : Arc,col D F f=col D F e → col D F g=col D F e →
      (f.1=g.1 ∨ f.2=g.2) → f=g)

/-- One paid-or-unpaid combinatorial move, with any shortest cycle pinned. -/
theorem cut {D V q M F} (actual : ∀C∈F,Cycle D V q C) (mf : M∈F) (more : F≠{M}) :
    ∃G,Cut D M F G := by
  classical
  have extra : ∃C∈F,C≠M := by
    by_contra! none
    exact more (Subset.antisymm (fun C cf => mem_singleton.mpr (none C cf)) (singleton_subset_iff.mpr mf))
  obtain ⟨C,cf,cm⟩ := extra
  have c := actual C cf
  have m := actual M mf
  have diff : (C\M).Nonempty := sdiff_nonempty.mpr (fun sub => cm (eq_of_subset_of_card_le sub (by rw [c.size,m.size])))
  obtain ⟨x,xcm⟩ := diff
  obtain ⟨xc,xm⟩ := mem_sdiff.mp xcm
  obtain ⟨y,yi⟩ := card_pos.mp (show 0<(outN D C x).card by rw [c.heads x xc]; decide)
  obtain ⟨yc,xy⟩ := mem_outN.mp yi
  let e0 : Arc := (x,y)
  let T := (V ×ˢ V).filter (fun e => (col D F e).Nonempty ∧ col D F e⊆col D F e0)
  have ce : C∈col D F e0 := mem_col.mpr ⟨cf,xc,yc,xy⟩
  have e0t : e0∈T := mem_filter.mpr ⟨mem_product.mpr ⟨c.sub xc,c.sub yc⟩,⟨C,ce⟩,Subset.rfl⟩
  obtain ⟨e,et,least⟩ := T.exists_min_image (fun f => (col D F f).card) ⟨e0,e0t⟩
  obtain ⟨_,live,below⟩ := mem_filter.mp et
  obtain ⟨A,ae⟩ := live
  have af := (mem_col.mp ae).1
  let G := F\col D F e
  have mg : M∈G := mem_sdiff.mpr ⟨mf,fun me => xm (mem_col.mp (below me)).2.1⟩
  have less : G ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun same =>
    (mem_sdiff.mp (show A∈G from same.symm ▸ af)).2 ae⟩
  refine ⟨G,mg,less,e,⟨A,ae⟩,rfl,?_,?_⟩
  · intro f flive
    constructor
    · intro none
      have sub : col D F f⊆col D F e := by
        intro B bf
        by_contra absent
        have bg : B∈col D G f := mem_col.mpr ⟨mem_sdiff.mpr ⟨(mem_col.mp bf).1,absent⟩,(mem_col.mp bf).2⟩
        rw [none] at bg
        exact notMem_empty _ bg
      obtain ⟨B,bf⟩ := flive
      obtain ⟨bF,u,v,_⟩ := mem_col.mp bf
      have bc := actual B bF
      have ft : f∈T := mem_filter.mpr ⟨mem_product.mpr ⟨bc.sub u,bc.sub v⟩,⟨B,bf⟩,sub.trans below⟩
      exact eq_of_subset_of_card_le sub (least f ft)
    · intro same
      apply eq_empty_iff_forall_notMem.mpr
      intro B bg
      obtain ⟨bG,use⟩ := mem_col.mp bg
      obtain ⟨bF,absent⟩ := mem_sdiff.mp bG
      exact absent (same ▸ mem_col.mpr ⟨bF,use⟩)
  · intro f g fe ge shared
    obtain ⟨_,fu,fv,fa⟩ := mem_col.mp (show A∈col D F f from fe.symm ▸ ae)
    obtain ⟨_,gu,gv,ga⟩ := mem_col.mp (show A∈col D F g from ge.symm ▸ ae)
    have ac := actual A af
    rcases shared with same|same
    · exact Prod.ext same (card_le_one.mp (ac.heads f.1 fu).le _ (mem_outN.mpr ⟨fv,fa⟩) _
        (mem_outN.mpr ⟨gv,same ▸ ga⟩))
    · exact Prod.ext (card_le_one.mp (ac.incoming f.2 fv).le _ (mem_inN.mpr ⟨fu,fa⟩) _
        (mem_inN.mpr ⟨gu,same ▸ ga⟩)) same

/-- The rank is the number of remaining shortest-cycle supports. All cuts
preserve the chosen marked support, down to the singleton family. -/
theorem peel {D V q M F} (actual : ∀C∈F,Cycle D V q C) (mf : M∈F) :
    Relation.ReflTransGen (Cut D M) F {M} := by
  classical
  by_cases done : F={M}
  · rw [done]
  obtain ⟨G,step⟩ := cut actual mf done
  exact Relation.ReflTransGen.head step (peel (fun C cg => actual C (step.less.subset cg)) step.marked)
termination_by F.card
decreasing_by exact card_lt_card step.less

#print axioms cut
#print axioms peel
end LeanCH.BR.Closure.MarkedCyclePeeling
