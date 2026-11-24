import checkpoints.shen_extension.ReceiverBank
import checkpoints.shen_extension.CorridorOriginalBills

namespace LeanCH.BR.Closure.ReceiverRetry
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier

/-- At least q+1 old intermediates bill the same original column. -/
theorem cheap_middle {q : ℕ} {D : CH.Digraph} {V J : Finset ℕ} {π : ℕ → ℝ} {w}
    (old : RealDual q D V 1 π) (wv : w ∈ V) (many : q+1 ≤ J.card) (sub : J ⊆ inN D V w) :
    ∃ r ∈ J, (q:ℝ) * (q+1) * π r ≤ 1 - π w := by
  classical
  obtain ⟨r,rm,low⟩ := J.exists_min_image π (card_pos.mp (by omega))
  have rv := (mem_inN.mp (sub rm)).1
  have jr : (q:ℝ)+1 ≤ J.card := by exact_mod_cast many
  have jmin : (q+1:ℝ) * π r ≤ ∑ i ∈ J, π i := calc
    _ ≤ (J.card:ℝ) * π r := mul_le_mul_of_nonneg_right jr (old.nonneg r rv)
    _ = ∑ _i ∈ J, π r := by simp
    _ ≤ _ := sum_le_sum (fun i im => low i im)
  have inflow : (∑ i ∈ J, π i) ≤ realInW D V π w := calc
    _ = ∑ i ∈ J, if D i w = true then π i else 0 := by
      apply sum_congr rfl
      intro i im
      simp [(mem_inN.mp (sub im)).2]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun i im => (mem_inN.mp (sub im)).1)
      (fun i iv _ => by split <;> simp [old.nonneg i iv])
  have atW : π w + (q:ℝ) * realInW D V π w ≤ 1 := old.columns w wv
  have bound := mul_le_mul_of_nonneg_left (jmin.trans inflow) (Nat.cast_nonneg (α:=ℝ) q)
  exact ⟨r,rm,by rw [mul_assoc]; linarith⟩

/-- Use the paid bank and the old-price test at the very same native turn.
In the large bank, either an actual missing half fails the original dual,
or all alternatives are already old and one of them is cheap. -/
theorem priced_bank {q n} (X : Model q n) (hq : 2 ≤ q) {F L K d z w} {π : ℕ → ℝ}
    (native : F ⊆ family X) (kf : K ∈ F)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (bad : ∀ M, Boundary X F M → ¬ SmallRow q (graph X.D (insert M F)) X.V)
    (old : RealDual q (graph X.D F) X.V 1 π)
    (dk : d ∈ K) (zk : z ∈ K) (wk : w ∈ K) (dz : X.D d z = true) (zw : X.D z w = true) :
    let P := K.erase z
    let J := middles X.D X.V P q d w
    (∃ r ∈ J, let cut := (insert r P).erase d
      cut.card = q ∧ d ∉ cut ∧ (outN X.D cut d).card = 1 ∧ protectsHeads X.D X.V cut d) ∨
    (q+1 ≤ J.card ∧ (∀ r ∈ J, ∃ v ∈ J, X.D v r = true) ∧
      ((∃ r ∈ J, insert r P ∉ F ∧ (targets X.D X.V F L).card ≤ 2 ∧
        ((graph X.D F d r = false ∧ 1 < realCol q (graph X.D F) X.V π r + q * π d) ∨
          (graph X.D F r w = false ∧ 1 < realCol q (graph X.D F) X.V π w + q * π r))) ∨
       ((∀ r ∈ J, insert r P ∈ F) ∧ ∃ r ∈ J, (q:ℝ) * (q+1) * π r ≤ 1 - π w))) := by
  classical
  intro P J
  have ck : Cycle X.D X.V q K := (mem_filter.mp (native kf)).2
  rcases bank_or_many hq X.free ck dk zk wk dz zw with paid | ⟨many,joint,stuck⟩
  · exact Or.inl paid
  refine Or.inr ⟨many,stuck,?_⟩
  by_cases allOld : ∀ r ∈ J, insert r P ∈ F
  · right
    have wz : w ≠ z := fun eq => loopfree X.free (by omega) (ck.sub zk) (eq ▸ zw)
    apply And.intro allOld (cheap_middle old (ck.sub wk) many ?_)
    intro r rm
    obtain ⟨rv,arc⟩ := mem_inN.mp (mem_inter.mp (joint rm)).2
    exact mem_inN.mpr ⟨rv,active.mpr ⟨insert r P,mem_col.mpr ⟨allOld r rm,mem_insert_self _ _,
      mem_insert_of_mem (mem_erase.mpr ⟨wz,wk⟩),arc⟩⟩⟩
  · push Not at allOld
    obtain ⟨r,rm,off⟩ := allOld
    obtain ⟨dr,rw'⟩ := mem_inter.mp (joint rm)
    have bills := CorridorPayment.original_bills X hq ck kf zk dk wk dz zw (mem_outN.mp dr).1
      (mem_outN.mp dr).2 (mem_inN.mp rw').2 least bad π old
    obtain ⟨cap,fail⟩ := bills.resolve_left off
    refine Or.inl ⟨r,rm,off,cap.trans ?_,fail⟩
    split <;> split <;> decide

#print axioms priced_bank
end LeanCH.BR.Closure.ReceiverRetry
