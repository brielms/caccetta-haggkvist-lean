import checkpoints.shen_extension.PairedFamilyLoop
import checkpoints.shen_extension.FullCycleTransfer

namespace LeanCH.BR.Closure.FullFamilySchedule
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier FullCycleTransfer PairedFamilyLoop

/-- Keep the actual bijection in the mark. Every slot, including an unmarked
one at a later time, consequently follows the very map used for payment. -/
def Mark (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (x : ℕ → ℚ) {F : Family}
    (s t : PairedFamilyLoop.State F) (send : ↥(previous s) ≃ ↥(previous t)) (b y r : ℕ) : Prop :=
  ∃ P : Pairing E (previous t) (previous s), send=P.equiv.symm ∧ P.label y=r ∧
    b∈current t\current s ∧ y∈current t∩(current s\previous s) ∧
    let U := V\(current s\previous s)
    let child := fun v => x v+P.deposit x v
    WeightedSD.row q E U child b ≤ mass U child

theorem admissible {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {F x} (sub : F⊆family X) (nonneg : ∀ z∈X.V, 0≤x z)
    (strict : ∀z∈X.V,mass X.V x<WeightedSD.row q (graph X.D F) X.V x z) :
    PairedFamilyLoop.Admissible F (graph X.D F) (Mark q (graph X.D F) X.V x) := by
  classical
  let E := graph X.D F
  intro s
  let A := current s
  let M := previous s
  have state := mem_filter.mp s.property
  obtain ⟨mf,af⟩ := mem_product.mp state.1
  have ne : A≠M := Ne.symm state.2
  have actual (C) (cf : C∈F) : Cycle E X.V q C := retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have a := actual A af
  have m := actual M mf
  obtain ⟨P⟩ := exists_pairing a m
  have gone : (A\M).Nonempty := by
    by_contra! empty
    have incl := sdiff_eq_empty_iff_subset.mp empty
    exact ne (eq_of_subset_of_card_le incl (by rw [a.size,m.size]))
  obtain ⟨z,za⟩ := gone
  have sz : X.V\(A\M) ≠ X.V := by
    intro eq
    have keep : z∈X.V\(A\M) := by rw [eq]; exact a.sub (mem_sdiff.mp za).1
    exact (mem_sdiff.mp keep).2 za
  have proper := small.induced (PrivateArcEndpoints.graph_free X F) _ sdiff_subset sz
  obtain ⟨b,bv,failed,y,yd,hit,miss⟩ := rational_step P a m x nonneg strict proper
  obtain ⟨L,use⟩ := active.mp hit
  obtain ⟨lf,bl,yl,_⟩ := mem_col.mp use
  have la : A≠L := fun eq => (mem_sdiff.mp bv).2 (eq ▸ bl)
  let t : PairedFamilyLoop.State F := ⟨(A,L),mem_filter.mpr ⟨mem_product.mpr ⟨af,lf⟩,la⟩⟩
  let Y : ↥A := ⟨y,(mem_sdiff.mp yd).1⟩
  let R := P.equiv Y
  have dest : (R : ℕ)=P.label y := (P.label_apply Y.property).symm
  have back : (P.equiv.symm R : ℕ)=y := congrArg Subtype.val (P.equiv.symm_apply_apply Y)
  refine ⟨t,rfl,P.equiv.symm,b,R,?_,?_,?_⟩
  · simpa only [dest] using miss
  · change E b (P.equiv.symm R)=true
    rw [back]; exact hit
  · refine ⟨P,rfl,?_,mem_sdiff.mpr ⟨bl,(mem_sdiff.mp bv).2⟩,?_,failed⟩
    · exact (congrArg P.label back).trans dest.symm
    · change (P.equiv.symm R : ℕ)∈L∩(A\M)
      rw [back]; exact mem_inter.mpr ⟨yl,yd⟩

theorem seed {F : Family} (two : 2≤F.card) : Nonempty (PairedFamilyLoop.State F) := by
  obtain ⟨M,mf,A,af,ne⟩ := one_lt_card.mp two
  exact ⟨⟨(M,A),mem_filter.mpr ⟨mem_product.mpr ⟨mf,af⟩,ne⟩⟩⟩

#print axioms admissible
#print axioms seed
end LeanCH.BR.Closure.FullFamilySchedule
