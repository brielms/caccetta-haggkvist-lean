import checkpoints.shen_extension.PacketCompression
import checkpoints.shen_extension.SharedArcComponentExchange

namespace LeanCH.BR.Closure.SharedArcCompression
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcComponentExchange FiniteCutInverse
open scoped Matrix

private theorem mono {D F J} (incl : F ⊆ J) {i j : ℕ} (old : graph D F i j=true) :
    graph D J i j=true := by
  obtain ⟨A,h⟩ := active.mp old
  obtain ⟨af,ia,ja,ij⟩ := mem_col.mp h
  exact active.mpr ⟨A,mem_col.mpr ⟨incl af,ia,ja,ij⟩⟩

/-- Test any competing attachment on at most q coordinates. The inverse
comes from the union of both children. Only the initial boundary child
needs to be strict. -/
theorem competitor {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B) (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (M : Finset ℕ) :
    let G := graph X.D (insert B (insert M F))
    let E := graph X.D (insert M F)
    let T : Finset X.V := univ.filter (fun j : X.V => j.val ∈ targets X.D X.V F B)
    T.card ≤ q ∧ ∃ H : Matrix X.V X.V ℝ, CommonInverse (realMatrix q G X.V) H ∧
      (SmallRow q E X.V ↔ ∃ t : T → ℝ, PacketCompression.Live t ∧ ∀ j : T,
        t j ≤ ∑ k : T, t k * ∑ i : X.V, H k i * (realMatrix q G X.V i j - realMatrix q E X.V i j)) := by
  classical
  intro G E T
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have subE {u v} (e : E u v=true) : G u v=true := mono (subset_insert B _) e
  have subB {u v} (e : graph X.D (insert B F) u v=true) : G u v=true :=
    mono (insert_subset_insert B (subset_insert M F)) e
  obtain ⟨w,wn,_,strong⟩ := strict_witness_of_not_smallRow bad
  have strongG (i) (iv : i∈X.V) : mass X.V w < WeightedSD.row q G X.V w i := by
    apply (strong i iv).trans_le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun _ _ _ _ h => subB h) wn iv) (Nat.cast_nonneg q))
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow
    (small.induced (PrivateArcEndpoints.graph_free X (insert B (insert M F)))) w wn strongG
  have size : T.card ≤ q := by
    have imageT : T.image Subtype.val = targets X.D X.V F B := by
      ext z
      constructor
      · rintro h; obtain ⟨i,hi,rfl⟩ := mem_image.mp h; exact (mem_filter.mp hi).2
      · intro hz
        exact mem_image.mpr ⟨⟨z,(mem_filter.mp hz).1⟩,mem_filter.mpr ⟨mem_univ _,hz⟩,rfl⟩
    obtain ⟨A,af,i,im,j,jm,ij⟩ := step.2.2
    have jb := (mem_inter.mp jm).2
    have old : graph X.D F i j=true :=
      active.mpr ⟨A,mem_col.mpr ⟨af,(mem_inter.mp im).1,(mem_inter.mp jm).1,ij⟩⟩
    have absent : j ∉ targets X.D X.V F B := by
      intro h
      obtain ⟨_,_,v,vb,vj,off⟩ := mem_filter.mp h
      have same := card_le_one.mp (cb.incoming j jb).le _ (mem_inN.mpr ⟨vb,vj⟩) _
        (mem_inN.mpr ⟨(mem_inter.mp im).2,ij⟩)
      exact Bool.noConfusion (off.symm.trans (same ▸ old))
    have strict : targets X.D X.V F B ⊂ B :=
      Finset.ssubset_iff_subset_ne.mpr ⟨fun _ h => (mem_filter.mp h).2.1,fun eq => absent (by rw [eq]; exact jb)⟩
    have sz := card_lt_card strict
    rw [cb.size,←imageT,card_image_of_injective _ Subtype.val_injective] at sz
    omega
  refine ⟨size,H,inv,PacketCompression.graph_iff X.live inv (fun _ _ _ _ h => subE h) T ?_⟩
  intro j hj i
  apply Bool.eq_iff_iff.mpr ⟨subE,?_⟩
  intro all
  by_contra missing
  obtain old | mark := union_arc.mp all
  · exact missing old
  · obtain ⟨ib,jb,raw,_⟩ := mem_added.mp mark
    have was : graph X.D F i j = false :=
      Bool.eq_false_iff.mpr (fun yes => missing (mono (subset_insert M F) yes))
    exact hj (mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨j.property,jb,i,ib,raw,was⟩⟩)

end LeanCH.BR.Closure.SharedArcCompression
#print axioms LeanCH.BR.Closure.SharedArcCompression.competitor

