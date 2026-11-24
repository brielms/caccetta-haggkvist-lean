import checkpoints.shen_extension.ReturnCycleOmissions

namespace LeanCH.BR.Closure.ReturnSuffixCover
open Finset BRq2 BRq3 BR45 WeightedSD CrossValueOmissions ReturnCycleOmissions

/-- All native two-step returns u→h→p with u in U share their last
arc when h is fixed. If that arc survives, charge their distinct first arcs. -/
def charges (D G : CH.Digraph) (U : Finset ℕ) (p h : ℕ) : Finset (ℕ×ℕ) :=
  if G h p=true then inN D U h ×ˢ {h} else {(h,p)}

private theorem separated {D G V U p} {i j : ℕ} (no_loop : D p p=false)
    (ip : i∈inN D V p) (jp : j∈inN D V p) (ne : i≠j) :
    Disjoint (charges D G U p i) (charges D G U p j) := by
  have ni : i≠p := fun eq=>Bool.noConfusion (no_loop.symm.trans (eq ▸ (mem_inN.mp ip).2))
  have nj : j≠p := fun eq=>Bool.noConfusion (no_loop.symm.trans (eq ▸ (mem_inN.mp jp).2))
  apply disjoint_left.mpr
  rintro ⟨x,y⟩ hi hj
  unfold charges at hi hj
  split at hi <;> split at hj
  · exact ne ((mem_singleton.mp (mem_product.mp hi).2).symm.trans (mem_singleton.mp (mem_product.mp hj).2))
  · exact ni ((mem_singleton.mp (mem_product.mp hi).2).symm.trans (congrArg Prod.snd (mem_singleton.mp hj)))
  · exact nj ((mem_singleton.mp (mem_product.mp hj).2).symm.trans (congrArg Prod.snd (mem_singleton.mp hi)))
  · exact ne ((congrArg Prod.fst (mem_singleton.mp hi)).symm.trans (congrArg Prod.fst (mem_singleton.mp hj)))

/-- A lower bound that charges a shared closing arc just once. For each
parent h of p take the lesser of the price of h→p and the total price of
all u→h. Add these bounds across h and to the full initial omission set. -/
theorem last_two {q D G V p U a b c d} (hq : 3≤q) (free : QFree D V q) (pv : p∈V)
    (sub : U⊆V) (blocked : ∀u∈U,p∉ball G V u 2)
    (an : ∀i∈V,0≤a i) (bn : ∀i∈V,0≤b i) (gap : cost q a b (lost D G V)=c-d) :
    cost q a b (initial D G V p) +
      ∑h∈inN D V p,min ((q:ℚ)*a h*b p) ((q:ℚ)*mass (inN D U h) a*b h) ≤ c-d := by
  classical
  let P := inN D V p
  let L := charges D G U p
  have actual (h) (hp : h∈P) : L h⊆lost D G V := by
    obtain ⟨hv,hp'⟩ := mem_inN.mp hp
    rintro ⟨i,j⟩ arc
    change _∈charges D G U p h at arc
    unfold charges at arc
    split at arc
    · rename_i kept
      obtain ⟨ih,jh⟩ := mem_product.mp arc
      obtain rfl := mem_singleton.mp jh
      obtain ⟨iu,edge⟩ := mem_inN.mp ih
      refine mem_filter.mpr ⟨mem_product.mpr ⟨sub iu,hv⟩,edge,Bool.eq_false_iff.mpr (fun ij=>?_ )⟩
      exact blocked i iu (mem_ball.mpr ⟨pv,2,le_rfl,.step hv ij (.step pv kept (.refl _))⟩)
    · rename_i off
      obtain eq := mem_singleton.mp arc
      rw [eq]
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hv,pv⟩,hp',Bool.eq_false_iff.mpr off⟩
  have initSep : Disjoint (initial D G V p) (P.biUnion L) := by
    apply disjoint_left.mpr
    rintro ⟨i,j⟩ e inside
    obtain ⟨h,hp,arc⟩ := mem_biUnion.mp inside
    obtain ⟨hv,hp'⟩ := mem_inN.mp hp
    have tail : i∈insert p (outN D V p) := (mem_filter.mp e).2
    change _∈charges D G U p h at arc
    unfold charges at arc
    split at arc
    · obtain ⟨iu,ih⟩ := mem_inN.mp (mem_product.mp arc).1
      rcases mem_insert.mp tail with rfl|pi
      · exact free _ 2 (by omega) (by omega) (.step hv ih (.step pv hp' (.refl _)))
      · exact free p 3 (by omega) hq (.step (sub iu) (mem_outN.mp pi).2 (.step hv ih (.step pv hp' (.refl _))))
    · have eq : i=h := congrArg Prod.fst (mem_singleton.mp arc)
      subst i
      rcases mem_insert.mp tail with rfl|ph
      · exact free _ 1 (by omega) (by omega) (.step pv hp' (.refl _))
      · exact free p 2 (by omega) (by omega) (.step hv (mem_outN.mp ph).2 (.step pv hp' (.refl _)))
  have lower (h) : min ((q:ℚ)*a h*b p) ((q:ℚ)*mass (inN D U h) a*b h)≤cost q a b (L h) := by
    dsimp only [L,charges]
    split
    · simpa only [rectangle,mass,sum_singleton] using
        (min_le_right ((q:ℚ)*a h*b p) ((q:ℚ)*mass (inN D U h) a*b h))
    · simpa only [cost,sum_singleton] using
        (min_le_left ((q:ℚ)*a h*b p) ((q:ℚ)*mass (inN D U h) a*b h))
  have noLoop := Bool.eq_false_iff.mpr (loopfree free (by omega) pv)
  have pairwise : (P:Set ℕ).PairwiseDisjoint L := fun _ hi _ hj ne=>separated noLoop hi hj ne
  have unionSub : initial D G V p ∪ P.biUnion L ⊆ lost D G V := by
    apply union_subset (filter_subset _ _)
    intro e he
    obtain ⟨h,hp,eh⟩ := mem_biUnion.mp he
    exact actual h hp eh
  have bound := subset_budget an bn gap unionSub
  unfold cost at bound
  rw [sum_union initSep,sum_biUnion pairwise] at bound
  exact (add_le_add_right (sum_le_sum (s:=P) (fun h _=>lower h)) _).trans bound

#print axioms last_two
end LeanCH.BR.Closure.ReturnSuffixCover
