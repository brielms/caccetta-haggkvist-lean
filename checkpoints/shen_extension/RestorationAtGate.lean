import checkpoints.shen_extension.OmittedCycleProgress

namespace LeanCH.BR.Closure.RestorationAtGate
open Finset BRq2 BRq3 BR45 WeightedSD FirstPacketBarrier MarkedCyclePeeling OmittedCycleProgress

/-- Start the recursive restoration at the actual first strict attachment.
Completion keeps its adjacency matrix and the chosen terminal column prices. -/
theorem start {q n F π d} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (sub : F⊆family X)
    (bad : ¬SmallRow q (graph X.D F) X.V) (high : 1<d) (pp : ∀i∈X.V,0<π i)
    (pm : mass X.V π=1) (cols : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V π i=d) :
    ∃A : Stage X,F⊆A.cycles ∧ graph X.D A.cycles=graph X.D F ∧ A.π=π ∧ A.value=d := by
  classical
  let G := graph X.D F
  have free := PrivateArcEndpoints.graph_free X F
  obtain ⟨v,vn,_,strict⟩ := strict_witness_of_not_smallRow bad
  obtain ⟨x,_,c,_,xp,_,xm,_,rows,_⟩ := strict_pair_of_proper_smallRow
    (small.induced free) X.live v vn strict
  have balance := NativeReturnAccounts.balance q (graph X.D F) X.V x π
  simp only [sum_congr rfl (fun i hi=>congrArg (fun z : ℚ=>π i*z) (rows i hi)),
    sum_congr rfl (fun i hi=>congrArg (fun z : ℚ=>x i*z) (cols i hi)),←sum_mul] at balance
  change mass X.V π*c=mass X.V x*d at balance
  rw [pm,xm,one_mul,one_mul] at balance
  subst c
  have actual (M) (mf : M∈F) : ShenCycleSuccessor.Cycle G X.V q M := retain_cycle (mem_filter.mp (sub mf)).2 mf
  obtain ⟨C,fc,same,complete,native⟩ := FlatCycleFamilyCompletion.complete (by omega : 1≤q) X.free actual
  let A : Stage X := ⟨C,x,π,d,fun M mc=>mem_filter.mpr ⟨mem_powerset.mpr (native M mc).sub,native M mc⟩,
    fun M=>by rw [same]; exact complete M,by rw [same]; exact ⟨high,xp,pp,xm,pm,rows,cols⟩⟩
  exact ⟨A,fc,same,rfl,rfl⟩

#print axioms start
end LeanCH.BR.Closure.RestorationAtGate
