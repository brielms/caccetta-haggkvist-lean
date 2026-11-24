import checkpoints.shen_extension.FullRowsOnShortestCycle
namespace LeanCH.BR.SparseCycleReturns
open Finset BRq2 BRq3 BR45 BRsGen

/-- On a cycle of length q+1, an exterior row that reaches the cycle in
l steps has at most l+1 parents on that cycle. The bound holds for each
actual return and any specified subset of the cycle. -/
theorem parent_cap {D V C P q l a c} (free : QFree D V q) (cv : C⊆V) (pc : P⊆C)
    (size : C.card=q+1) (positive : ∀v∈C,1≤(outN D C v).card)
    (av : a∈V) (cm : c∈C) (path : Walk D V a c l) (time : l+1≤q) :
    (inN D P a).card≤l+1 := by
  let B := ball D C c (q-l-1)
  have dis : Disjoint (inN D P a) B := by
    apply disjoint_left.mpr
    intro x arc near
    obtain ⟨_,k,le,walk⟩ := mem_ball.mp near
    exact free a _ (by omega) (by omega) ((path.append (walk.mono cv)).snoc av (mem_inN.mp arc).2)
  have total := card_le_card (union_subset ((show inN D P a⊆P from fun _ h=>(mem_inN.mp h).1).trans pc)
    (show B⊆C from ball_subset))
  rw [card_union_of_disjoint dis] at total
  have reach := ball_one_growth (free.mono_set cv) positive cm (q-l-1) (by omega)
  change q-l-1+1≤B.card at reach
  omega

/-- Two sinks, first in A and then in A with the first sink erased,
return to the cycle in at most one and two steps respectively. If each
marked cycle row misses at most one exterior label, these two labelled
columns cover all marked cycle rows. -/
theorem two_port_cap {D V C P A q} (free : QFree D V q) (cv : C⊆V) (av : A⊆V) (pc : P⊆C)
    (size : C.card=q+1) (positive : ∀v∈C,1≤(outN D C v).card)
    (small : A.card≤q) (lo : 2≤A.card) (hq : 3≤q)
    (exit : ∀v∈A,(outN D (C∪A) v).Nonempty)
    (misses : ∀v∈P,(A\outN D A v).card≤1) : P.card≤5 := by
  classical
  obtain ⟨z,zm,stop⟩ := exists_sink (free.mono_set av) (card_pos.mp (by omega)) small
  obtain ⟨c,ch⟩ := exit z zm
  have cc : c∈C := (mem_union.mp (outN_subset ch)).resolve_right (fun ca=>stop c ca (mem_outN.mp ch).2)
  have zc : Walk D V z c 1 := .step (cv cc) (mem_outN.mp ch).2 (.refl c)
  have boundZ := parent_cap free cv pc size positive (av zm) cc zc (by omega)
  have rest := card_erase_add_one zm
  obtain ⟨b,bm,last⟩ := exists_sink (free.mono_set ((erase_subset z A).trans av))
    (card_pos.mp (by omega)) (by omega)
  obtain ⟨ne,ba⟩ := mem_erase.mp bm
  obtain ⟨a,ah⟩ := exit b ba
  have boundB : (inN D P b).card≤3 := by
    by_cases ac : a∈C
    · have step : Walk D V b a 1 := .step (cv ac) (mem_outN.mp ah).2 (.refl a)
      have := parent_cap free cv pc size positive (av ba) ac step (by omega)
      omega
    · have az : a=z := by
        by_contra diff
        exact last a (mem_erase.mpr ⟨diff,(mem_union.mp (outN_subset ah)).resolve_left ac⟩) (mem_outN.mp ah).2
      subst a
      exact parent_cap free cv pc size positive (av ba) cc (.step (av zm) (mem_outN.mp ah).2 zc) (by omega)
  have cover : P⊆inN D P b∪inN D P z := by
    intro v vm
    by_cases hit : D v b=true
    · exact mem_union_left _ (mem_inN.mpr ⟨vm,hit⟩)
    · apply mem_union_right
      apply mem_inN.mpr
      refine ⟨vm,?_⟩
      by_contra miss
      have left : b∈A\outN D A v := mem_sdiff.mpr ⟨ba,fun h=>hit (mem_outN.mp h).2⟩
      have right : z∈A\outN D A v := mem_sdiff.mpr ⟨zm,fun h=>miss (mem_outN.mp h).2⟩
      have many := one_lt_card.mpr ⟨b,left,z,right,ne⟩
      have := misses v vm
      omega
  have total := (card_le_card cover).trans (card_union_le _ _)
  omega

attribute [aesop safe forward (immediate := [free,cv,pc,size,positive,av,cm,path,time]) (rule_sets := [CHGraphFamilies])] parent_cap
attribute [aesop safe forward (immediate := [free,cv,av,pc,size,positive,small,lo,hq,exit,misses]) (rule_sets := [CHGraphFamilies])] two_port_cap
#print axioms parent_cap
#print axioms two_port_cap
end LeanCH.BR.SparseCycleReturns
