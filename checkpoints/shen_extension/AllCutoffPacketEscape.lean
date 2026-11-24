import checkpoints.shen_extension.MinimumRootColumn

namespace LeanCH.BR.Closure.AllCutoffPacketEscape
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights

/-- At any cutoff a large packet forces a marked *exterior receiver*.
There is an original shortest-cycle destination. At cutoffs beyond three
the destination may contain h. -/
theorem from_loop {q n} (X : Model q n) (hq : 2≤q) {h} (hv : h∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (large : (q+1)^2≤X.V.card)
    (M : ℕ→Finset ℕ) (a u v b : ℕ→ℕ) (closed : M (q+1)=M 0)
    (cycle : ∀i,Cycle X.D (X.V\{h}) q (M i))
    (move : ∀i,CycleSquareTensor.Shift X.D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) :
    let S := (range (q+1)).image u
    let P := (M 0).erase (u 0)
    ∃z∈(X.V\{h})\(P∪S),∃A N,(A=S ∨ ∃x∈S,A=insert x P) ∧
      Cycle X.D (X.V\{h}) q A ∧ 2≤(inN X.D A z).card ∧
      Cycle X.D X.V q N ∧ z∈N\A := by
  classical
  intro S P
  let W := X.V\{h}
  have wv : W⊆X.V := sdiff_subset
  have safe := X.free.mono_set wv
  obtain ⟨cs,_,_,_,arcs⟩ := AnchoredShiftFlow.least_period (by omega) safe M a u v b closed cycle move
  have us : u 0∈S := mem_image_of_mem u (mem_range.mpr (by omega))
  obtain ⟨dis,fits⟩ := ShortestCycleFiberModule.slots (by omega) safe (cycle 0)
    (move 0).aM (move 0).uM (move 0).bM cs.sub us arcs
  have ps : P.card=q := by
    have e := card_erase_add_one (move 0).uM
    change P.card+1=(M 0).card at e
    rw [(cycle 0).size] at e; omega
  have sub : P∪S⊆W := union_subset ((erase_subset _ _).trans (cycle 0).sub) cs.sub
  have he : h∈X.V\(P∪S) := mem_sdiff.mpr ⟨hv,fun hu => (mem_sdiff.mp (sub hu)).2 (mem_singleton_self h)⟩
  obtain ⟨z,ze,rich⟩ := MinimumRootColumn.fresh_pair X hq wv ps dis cs fits he minimum large
  obtain ⟨zh,zr⟩ := mem_erase.mp ze
  obtain ⟨zv,zu⟩ := mem_sdiff.mp zr
  have fresh : z∈W\(P∪S) := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨zv,by simpa using zh⟩,zu⟩
  have answer (A) (which : A=S ∨ ∃x∈S,A=insert x P) (ca : Cycle X.D W q A)
      (az : z∉A) (many : 2≤(inN X.D A z).card) :
      ∃N,(A=S ∨ ∃x∈S,A=insert x P) ∧ Cycle X.D W q A ∧ 2≤(inN X.D A z).card ∧
        Cycle X.D X.V q N ∧ z∈N\A := by
    obtain ⟨p,pi⟩ := card_pos.mp (show 0<(inN X.D A z).card by omega)
    obtain ⟨pm,pz⟩ := mem_inN.mp pi
    obtain ⟨N,cn,_,zn⟩ := edge_cycle X hq (wv (ca.sub pm)) zv pz
    exact ⟨N,which,ca,many,cn,mem_sdiff.mpr ⟨zn,az⟩⟩
  refine ⟨z,fresh,?_⟩
  by_cases twoS : 2≤(inN X.D S z).card
  · exact ⟨S,answer S (Or.inl rfl) cs (fun zs => zu (mem_union_right _ zs)) twoS⟩
  have slot (x) (xs : x∈S) (two : 2≤(inN X.D (insert x P) z).card) :=
    answer (insert x P) (Or.inr ⟨x,xs,rfl⟩) (fits x xs) (fun hit => zu
      ((mem_insert.mp hit).elim (fun eq => mem_union_right _ (eq ▸ xs)) (mem_union_left _))) two
  by_cases twoP : 2≤(inN X.D P z).card
  · have subP : inN X.D P z⊆inN X.D (insert (u 0) P) z := fun p pi =>
      mem_inN.mpr ⟨mem_insert_of_mem (mem_inN.mp pi).1,(mem_inN.mp pi).2⟩
    exact ⟨_,slot _ us (twoP.trans (card_le_card subP))⟩
  change 2≤(inN X.D P z).card+(inN X.D S z).card at rich
  obtain ⟨x,xi⟩ := card_pos.mp (show 0<(inN X.D S z).card by omega)
  obtain ⟨p,pi⟩ := card_pos.mp (show 0<(inN X.D P z).card by omega)
  obtain ⟨xs,xz⟩ := mem_inN.mp xi
  obtain ⟨pm,pz⟩ := mem_inN.mp pi
  have ne : p≠x := fun eq => disjoint_left.mp dis pm (eq.symm ▸ xs)
  exact ⟨_,slot x xs (one_lt_card.mpr ⟨p,mem_inN.mpr ⟨mem_insert_of_mem pm,pz⟩,x,
    mem_inN.mpr ⟨mem_insert_self x P,xz⟩,ne⟩)⟩

#print axioms from_loop
end LeanCH.BR.Closure.AllCutoffPacketEscape
