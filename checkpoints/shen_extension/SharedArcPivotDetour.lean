import checkpoints.shen_extension.SharedArcPivotChoice

namespace LeanCH.BR.Closure.SharedArcPivotDetour
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open SharedArcBarrier SharedArcComponentExchange FirstPacketBarrier MarkedCyclePeeling

/-- In a saturated puncture, a parent and a head without a shortcut
cannot both have their respective neighbourhoods absorbed by the pivot. -/
theorem detour {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hq : 3≤q) (free : QFree D V q)
    {a t h : ℕ} (av : a∈V) (tu : t∈V.erase a) (hu : h∈V.erase a)
    (ta : D t a=true) (ah : D a h=true) (off : D t h=false) (sat : BRsub.Sat q D (V.erase a)) :
    (∃x∈V.erase a,D t x=true ∧ D a x=false) ∨
    (∃y∈V.erase a,D y h=true ∧ D y a=false) := by
  by_contra! absorb
  have out {x} (xu : x∈V.erase a) (tx : D t x=true) : D a x=true := by
    cases eq : D a x <;> simp_all
  have inc {y} (yu : y∈V.erase a) (yh : D y h=true) : D y a=true := by
    cases eq : D y a <;> simp_all
  have ht : ¬D h t=true := fun e => free a 3 (by decide) hq
    (.step (mem_of_mem_erase hu) ah (.step (mem_of_mem_erase tu) e (.step av ta (.refl _))))
  obtain ⟨_,l,bound,path⟩ := mem_ball.mp (sat t tu h hu ht)
  cases path with
  | refl =>
    exact free _ 2 (by decide) (by omega) (.step av ta (.step (mem_of_mem_erase hu) ah (.refl _)))
  | @step _ x _ k xu tx tail =>
    cases k with
    | zero => cases tail; simp_all
    | succ m =>
      obtain ⟨y,body,_,yh⟩ := tail.unsnoc
      have yu : y∈V.erase a := body.end_mem_or.elim (fun e => e ▸ xu) id
      exact free a (m+1+1) (by omega) (by omega)
        (.step (mem_of_mem_erase xu) (out xu tx) ((body.mono (erase_subset _ _)).snoc av (inc yu yh)))

private theorem fill {α : Type*} [DecidableEq α] {S T : Finset α} {c : α} {k : ℕ}
    (many : k<S.card) (few : T.card≤k) (incl : S.erase c⊆T) : T⊆S := by
  have enough : k≤(S.erase c).card := by
    by_cases h : c∈S
    · have eq := card_erase_add_one h
      omega
    · simpa [erase_eq_of_notMem h] using many.le
  have eq := eq_of_subset_of_card_le incl (few.trans enough)
  exact eq ▸ erase_subset _ _

abbrev rest {V : Finset ℕ} (a : V) : Finset V := univ.erase a

/-- On one side of a stopped pivot there is an actual exterior vertex
and all the other attached neighbours fit inside the corresponding native
neighbourhood. This statement uses no degree bounds. -/
theorem endpoint_escape {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    let U := rest a
    let J := graph X.D (insert B F)
    ∃ t h : X.V, Fresh X F (t,a) ∧ Fresh X F (a,h) ∧ added X.D F B=SharedArcPivotChoice.pair a t h ∧
      ((U.filter (fun j : X.V => J a j=true)).erase h ⊆ U.filter (fun j : X.V => X.D t j=true)) ∧
      ((U.filter (fun j : X.V => J j a=true)).erase t ⊆ U.filter (fun j : X.V => X.D j h=true)) ∧
      ((∃ x∈U,X.D t x=true ∧ X.D a x=false) ∨ (∃ x∈U,X.D x h=true ∧ X.D x a=false)) := by
  classical
  intro U J
  have two : 2≤q := by omega
  obtain ⟨_,sat,center,_⟩ := (SharedArcPivot.alternatives X two small step least multi edge).resolve_left no
  obtain ⟨t,h,ta,ah,shape⟩ := SharedArcPivotChoice.boundary_pair X step multi a center
  have native {i j : ℕ} (e : J i j=true) : X.D i j=true := by
    obtain ⟨_,m⟩ := active.mp e
    exact (mem_col.mp m).2.2.2
  have ne {i j : X.V} (e : X.D i j=true) : i≠j := fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  have cross := SharedArcPivotPaths.crossed X two small step least multi edge no
  have outIn : (U.filter (fun j : X.V => J a j=true)).erase h ⊆ U.filter (fun j : X.V => X.D t j=true) := by
    intro x hit
    obtain ⟨xh,hx⟩ := mem_erase.mp hit
    obtain ⟨xu,ax⟩ := mem_filter.mp hx
    have old : graph X.D F a x=true := by
      rcases union_arc.mp ax with old|added
      · exact old
      · rw [shape] at added
        simp only [SharedArcPivotChoice.pair,mem_insert,mem_singleton,Prod.mk.injEq] at added
        exact (added.elim (fun e => ne ta.2.2.1 (Subtype.ext e.1.symm)) (fun e => xh (Subtype.ext e.2))).elim
    exact mem_filter.mpr ⟨xu,cross t x ta.2.2.1 (native ax) (by rw [old,ta.2.2.2]; decide)⟩
  have inOut : (U.filter (fun j : X.V => J j a=true)).erase t ⊆ U.filter (fun j : X.V => X.D j h=true) := by
    intro x hit
    obtain ⟨xt,hx⟩ := mem_erase.mp hit
    obtain ⟨xu,xa⟩ := mem_filter.mp hx
    have old : graph X.D F x a=true := by
      rcases union_arc.mp xa with old|added
      · exact old
      · rw [shape] at added
        simp only [SharedArcPivotChoice.pair,mem_insert,mem_singleton,Prod.mk.injEq] at added
        exact (added.elim (fun e => xt (Subtype.ext e.1)) (fun e => ne ah.2.2.1 (Subtype.ext e.2))).elim
    exact mem_filter.mpr ⟨xu,cross x h (native xa) ah.2.2.1 (by rw [old,ah.2.2.2]; decide)⟩
  have inside {x : X.V} (nx : x≠a) : x.val∈X.V.erase a.val :=
    mem_erase.mpr ⟨fun e => nx (Subtype.ext e),x.property⟩
  have asU {x : ℕ} (xu : x∈X.V.erase a.val) : (⟨x,mem_of_mem_erase xu⟩ : X.V)∈U :=
    mem_erase.mpr ⟨fun e => (mem_erase.mp xu).1 (congrArg Subtype.val e),mem_univ _⟩
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have it : (t.val,a.val)∈added X.D F B := shape ▸ mem_insert_self _ _
  have oh : (a.val,h.val)∈added X.D F B := shape ▸ mem_insert_of_mem (mem_singleton_self _)
  have off : X.D t h=false := Bool.eq_false_iff.mpr fun th =>
    ne ah.2.2.1 (Subtype.ext (card_le_one.mp (cyc.heads t (mem_added.mp it).1).le _
      (mem_outN.mpr ⟨(mem_added.mp it).2.1,ta.2.2.1⟩) _ (mem_outN.mpr ⟨(mem_added.mp oh).2.1,th⟩)))
  refine ⟨t,h,ta,ah,shape,outIn,inOut,?_⟩
  rcases detour hq X.free a.property (inside (ne ta.2.2.1)) (inside (ne ah.2.2.1).symm)
    ta.2.2.1 ah.2.2.1 off sat with ⟨x,xu,tx,ax⟩ | ⟨x,xu,xh,xa⟩
  · exact Or.inl ⟨⟨x,mem_of_mem_erase xu⟩,asU xu,tx,ax⟩
  · exact Or.inr ⟨⟨x,mem_of_mem_erase xu⟩,asU xu,xh,xa⟩

/-- A stopped two-arc attachment excludes every puncture of order at least qk+1
whose native row and column degrees are bounded by k. -/
theorem capped_false {q n k} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    (size : q*k+1≤(rest a).card)
    (rows : ∀i : X.V,i≠a → ((rest a).filter (fun j : X.V => X.D i j=true)).card≤k)
    (cols : ∀i : X.V,i≠a → ((rest a).filter (fun j : X.V => X.D j i=true)).card≤k) : False := by
  classical
  let U := rest a
  let J := graph X.D (insert B F)
  have native {i j : ℕ} (e : J i j=true) : X.D i j=true := by
    obtain ⟨_,m⟩ := active.mp e
    exact (mem_col.mp m).2.2.2
  obtain ⟨w,wn,_,strict⟩ := strict_witness_of_not_smallRow stop
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced (PrivateArcEndpoints.graph_free X (insert B F))) w wn strict
  have subOut (i : X.V) : U.filter (fun j : X.V => J i j=true) ⊆ U.filter (fun j : X.V => X.D i j=true) :=
    fun _ hj => mem_filter.mpr ⟨(mem_filter.mp hj).1,native (mem_filter.mp hj).2⟩
  have subIn (i : X.V) : U.filter (fun j : X.V => J j i=true) ⊆ U.filter (fun j : X.V => X.D j i=true) :=
    fun _ hj => mem_filter.mpr ⟨(mem_filter.mp hj).1,native (mem_filter.mp hj).2⟩
  obtain ⟨heads,parents⟩ := SharedArcIntervalPuncture.inverse_degree_floors inv a U size
    (fun i ne => (card_le_card (subOut i)).trans (rows i ne))
    (fun i ne => (card_le_card (subIn i)).trans (cols i ne))
  have ne {i j : X.V} (e : X.D i j=true) : i≠j := fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  obtain ⟨t,h,ta,ah,_,outIn,inOut,escape⟩ := endpoint_escape X hq small step least multi edge no
  have allOut := fill heads (rows t (ne ta.2.2.1)) outIn
  have allIn := fill parents (cols h (ne ah.2.2.1).symm) inOut
  rcases escape with ⟨x,xu,tx,ax⟩ | ⟨x,xu,xh,xa⟩
  · have yes := native (mem_filter.mp (allOut (mem_filter.mpr ⟨xu,tx⟩))).2
    simp_all
  · have yes := native (mem_filter.mp (allIn (mem_filter.mpr ⟨xu,xh⟩))).2
    simp_all

#print axioms detour
#print axioms capped_false

private theorem filter_count {V : Finset ℕ} (a : V) (P : ℕ → Bool) :
    ((rest a).filter (fun j : V => P j=true)).card=((V.erase a.val).filter (fun j => P j=true)).card := by
  classical
  rw [←card_image_of_injective _ (Subtype.val_injective (p:=fun x => x∈V))]
  congr 1
  ext x
  simp only [mem_image,mem_filter,rest,mem_erase,mem_univ,and_true]
  constructor
  · rintro ⟨j,⟨ne,hit⟩,rfl⟩
    exact ⟨⟨fun e => ne (Subtype.ext e),j.property⟩,hit⟩
  · rintro ⟨⟨ne,xv⟩,hit⟩
    exact ⟨⟨x,xv⟩,⟨fun e => ne (congrArg Subtype.val e),hit⟩,rfl⟩

/-- Regularity alone supplies the required size through SmallRow on the
proper puncture, with no assumptions on order, symmetry or cycle shape. -/
theorem regular_false {q n k} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    (outdeg : ∀i∈X.V.erase a.val, (outN X.D (X.V.erase a.val) i).card=k)
    (indeg : ∀i∈X.V.erase a.val, (inN X.D (X.V.erase a.val) i).card≤k) : False := by
  classical
  let U := X.V.erase a.val
  have live : b.val∈U := mem_erase.mpr ⟨fun e => loopfree X.free (by omega) a.property
    (by simpa [e] using edge.2.2.1),b.property⟩
  obtain ⟨i,ui,low⟩ := small X.D U (card_erase_lt_of_mem a.property)
    (X.free.mono_set (erase_subset _ _)) (fun _ => 1) (by intros; norm_num) ⟨b,live⟩
  simp only [WeightedSD.row,outW_eq_mass,mass,sum_const,nsmul_eq_mul,mul_one] at low
  rw [outdeg i ui] at low
  have lower : q*k+1≤U.card := by
    rw [Nat.add_comm]
    exact_mod_cast low
  have cardU : (rest a).card=U.card := by
    simpa [U] using filter_count a (fun _ => true)
  have inU {x : X.V} (nx : x≠a) : x.val∈U := mem_erase.mpr ⟨fun e => nx (Subtype.ext e),x.property⟩
  apply capped_false X hq small step least stop multi edge no (cardU ▸ lower)
  · intro x nx
    exact (filter_count a (X.D x)).le.trans (outdeg x (inU nx)).le
  · intro x nx
    exact (filter_count a (fun j => X.D j x)).le.trans (indeg x (inU nx))

#print axioms regular_false
end LeanCH.BR.Closure.SharedArcPivotDetour
