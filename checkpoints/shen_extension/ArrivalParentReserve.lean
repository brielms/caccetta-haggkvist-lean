import checkpoints.shen_extension.CompleteAccountEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

noncomputable def highParents (D : CH.Digraph) (V C : Finset ℕ) (k b : ℕ) :=
  (allParents D V C).filter (fun x=>b<(ball D V x k).card)

/-- Every arrival reserves actual high parents of its terminal. On a path
of positive length the last complete bank supplies them; on a path of
length zero the full rows of the first cycle supply them. -/
theorem arrival_reserves_parents {D V q r δ g d C T target} (free : QFree D V q)
    (reg : OutEq r D V) (ready : RoutingRoom q r V.card target)
    (arrival : WeakArrival D V r δ g d C T) (length : C.card≤g+(q-3))
    (cheap : g≤r-1) :
    g≤(highParents D V T 3 (3*r)).card ∧ (allParents D V T).card≤δ := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have reserve {B K} (bank : RouteBank D V r δ B) (cy : ∀k∈K,Rooted D V k K)
      (many : g≤(K.filter (fun v=>B⊆outN D V v)).card)
      (near : K.card≤(K.filter (fun v=>B⊆outN D V v)).card+(q-3)) :
      g≤(highParents D V B 3 (3*r)).card := by
    have bs := bank.size
    obtain ⟨b,bm⟩ := card_pos.mp (by omega : 0<B.card)
    have bv := (bank.cycle b bm).sub
    have grow := bank_growth free hq reg bv ⟨b,bm⟩ (by omega) ready.cycle.2.1 (by simpa only [bs] using ready.score)
    refine many.trans (card_le_card ?_)
    intro v vm
    obtain ⟨vk,heads⟩ := mem_filter.mp vm
    have kv := (cy v vk).sub
    have row := score_from_bank free kv bv (fun a am=>((cy a am).one a am).ge)
      (by omega) (by omega : (q-3)+3≤q) vk heads near grow
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨kv vk,heads⟩,ready.high.trans_le row⟩
  have lastEdge {P} (last : RouteEdge D V r δ P T) : g≤(highParents D V T 3 (3*r)).card ∧ (allParents D V T).card≤δ := by
    obtain ⟨p,t,edge⟩ := last
    have all v (vm : _ ) := complete_row (p.cycle v vm) (reg v ((p.cycle v vm).sub vm)) (edge ▸ t.size)
    have heads : ∀v∈P,T⊆outN D V v := by
      intro v vm z zm
      exact mem_of_mem_erase ((all v vm).symm ▸ (edge.symm ▸ zm))
    exact ⟨reserve t p.cycle (by rw [filter_true_of_mem heads,p.size]; exact cheap)
      (by rw [filter_true_of_mem heads]; omega),t.parents⟩

  obtain ⟨B,bank,_,many,path⟩ := arrival.route
  cases path with
  | refl => exact ⟨reserve bank arrival.cycle many (by omega),bank.parents⟩
  | tail _ last => exact lastEdge last

/-- The representative of each low class remains a distinct physical
parent. A reserved high row cannot serve as one of these representatives. -/
theorem representatives_with_reserve {D V q r k b C} (t : Selection D V q r k b)
    {K : Finset (Finset ℕ)} (keys : K⊆claims t C) (first : ∀Y∈K,C⊆outN D V (t.rep Y)) :
    K.card+(highParents D V C k b).card≤(allParents D V C).card := by
  classical
  let U := K.image t.rep
  have key Y (ym : Y∈K) := (mem_filter.mp (keys ym)).1
  have count : U.card=K.card := card_image_of_injOn (fun a am b bm eq=>
    (rep_key t (key _ am)).symm.trans ((congrArg (N2 D V) eq).trans (rep_key t (key _ bm))))
  have sub : U⊆allParents D V C := by
    rintro _ xm; obtain ⟨Y,ym,rfl⟩ := mem_image.mp xm
    exact mem_filter.mpr ⟨rep_native t (key Y ym),first Y ym⟩
  have dis : Disjoint U (highParents D V C k b) := by
    apply disjoint_left.mpr
    rintro _ xm hm; obtain ⟨Y,ym,rfl⟩ := mem_image.mp xm
    exact (mem_filter.mp (mem_filter.mp (t.represents Y (key Y ym))).1).2.not_gt (mem_filter.mp hm).2
  have bound := card_le_card (union_subset sub (filter_subset _ _ : highParents D V C k b⊆allParents D V C))
  change (U∪highParents D V C k b).card≤(allParents D V C).card at bound
  rwa [card_union_of_disjoint dis,count] at bound

#print axioms arrival_reserves_parents
#print axioms representatives_with_reserve
end LeanCH.BR.LowShellCycleSelection
