import checkpoints.shen_extension.ReceiverBankPrice

namespace LeanCH.BR.Closure.ReceiverRetry
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier

/-- Two candidate menus share a choice. Either it can be made without any
incoming incidence from either menu, a private choice attacks a shared one,
or at least q+1 shared choices themselves have no source. -/
theorem joint_source {D V q} (free : QFree D V q) {I J : Finset ℕ}
    (sub : I ∩ J ⊆ V) (live : (I ∩ J).Nonempty) :
    (∃ r ∈ I ∩ J, ∀ v ∈ I ∪ J, D v r ≠ true) ∨
    (∃ r ∈ I ∩ J, ∃ v ∈ (I ∪ J) \ (I ∩ J), D v r = true) ∨
    (q+1 ≤ (I ∩ J).card ∧ ∀ r ∈ I ∩ J, ∃ v ∈ I ∩ J, D v r = true) := by
  classical
  by_cases yes : ∃ r ∈ I ∩ J, ∀ v ∈ I ∪ J, D v r ≠ true
  · exact Or.inl yes
  by_cases privateEdge : ∃ r ∈ I ∩ J, ∃ v ∈ (I ∪ J) \ (I ∩ J), D v r = true
  · exact Or.inr (Or.inl privateEdge)
  have fed (r) (rm : r ∈ I ∩ J) : ∃ v ∈ I ∩ J, D v r = true := by
    by_contra! miss
    apply yes
    refine ⟨r,rm,?_⟩
    intro v vu vr
    by_cases shared : v ∈ I ∩ J
    · exact miss v shared vr
    · exact privateEdge ⟨r,rm,v,mem_sdiff.mpr ⟨vu,shared⟩,vr⟩
  refine Or.inr (Or.inr ⟨?_,fed⟩)
  by_contra! small
  obtain ⟨r,rm,light⟩ := exists_sink (free.reverse.mono_set sub) live (by omega : (I ∩ J).card ≤ q)
  obtain ⟨v,vm,vr⟩ := fed r rm
  exact light v vm vr

def SharedOutcome (D : CH.Digraph) (V S : Finset ℕ) (q p t z w : ℕ) : Prop :=
    let T := S.erase z
    let I := middles D V (insert p T) q p w
    let J := middles D V (insert t T) q t w
    (∃ r ∈ I ∩ J, let cut := insert r T
      cut.card = q ∧ p ∉ cut ∧ t ∉ cut ∧ (outN D cut p).card = 1 ∧ (outN D cut t).card = 1 ∧
      protectsHeads D V cut p ∧ protectsHeads D V cut t) ∨
    (∃ r ∈ I ∩ J, ∃ v ∈ (I ∪ J) \ (I ∩ J), D v r = true) ∨
    (q+1 ≤ (I ∩ J).card ∧ ∀ r ∈ I ∩ J, ∃ v ∈ I ∩ J, D v r = true)

/-- If two supports differ only in their feeder, the successful common
choice makes one deletion and protects both out-neighbourhoods. -/
theorem shared_bank {D V q S p t z w} (hq : 2 ≤ q) (free : QFree D V q)
    (ca : Cycle D V q (insert p S)) (cb : Cycle D V q (insert t S))
    (ps : p ∉ S) (ts : t ∉ S) (zs : z ∈ S) (ws : w ∈ S)
    (pz : D p z = true) (tz : D t z = true) (zw : D z w = true) :
    SharedOutcome D V S q p t z w := by
  classical
  unfold SharedOutcome
  intro T I J
  have wne : w ≠ z := fun e => loopfree free (by omega) (ca.sub (mem_insert_of_mem zs)) (e ▸ zw)
  have wt : w ∈ T := mem_erase.mpr ⟨wne,ws⟩
  have initial {f} (fs : f ∉ S) (fz : D f z = true) (cy : Cycle D V q (insert f S)) :
      z ∈ middles D V (insert f T) q f w := by
    have zf : z ≠ f := fun e => fs (e ▸ zs)
    have zoff : z ∉ insert f T := by simp [T,zf]
    have eq : insert z (insert f T) = insert f S := by rw [insert_comm z f]; simp [T,zs]
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨cy.sub (mem_insert_of_mem zs),zoff⟩,fz,zw,eq ▸ cy⟩
  have visible : I ∩ J ⊆ V := fun _ rm => (mem_sdiff.mp (mem_filter.mp (mem_inter.mp rm).1).1).1
  rcases joint_source free visible ⟨z,mem_inter.mpr ⟨initial ps pz ca,initial ts tz cb⟩⟩ with
    ⟨r,rm,light⟩ | residual
  · have paid {f} (fs : f ∉ S) (inside : r ∈ middles D V (insert f T) q f w)
        (light' : ∀ v ∈ middles D V (insert f T) q f w, D v r ≠ true) :
        (insert r T).card = q ∧ f ∉ insert r T ∧ (outN D (insert r T) f).card = 1 ∧
          protectsHeads D V (insert r T) f := by
      obtain ⟨rv,fr,_,cycle⟩ := mem_filter.mp (show r ∈ (V \ insert f T).filter _ from inside)
      have rf : r ≠ f := fun e => (mem_sdiff.mp rv).2 (mem_insert.mpr (Or.inl e))
      have ft : f ∉ T := fun m => fs (mem_of_mem_erase m)
      have fc : f ∉ insert r T := by simp [Ne.symm rf,ft]
      have erase : (insert r (insert f T)).erase f = insert r T := by
        rw [insert_comm r f,erase_insert fc]
      have wf : w ≠ f := fun e => fs (e ▸ ws)
      have pay := (bank_iff hq free (mem_insert_self f T) (mem_insert_of_mem wt) wf inside).mpr light'
      rw [erase] at pay
      have fm : f ∈ insert r (insert f T) := mem_insert_of_mem (mem_insert_self f T)
      have contains : insert r T ⊆ insert r (insert f T) := by rw [← erase]; exact erase_subset .. 
      have count : outN D (insert r T) f = {r} := by
        ext i
        constructor
        · intro im
          exact mem_singleton.mpr (card_le_one.mp (cycle.heads f fm).le i
            (mem_outN.mpr ⟨contains (mem_outN.mp im).1,(mem_outN.mp im).2⟩) r (mem_outN.mpr ⟨mem_insert_self _ _,fr⟩))
        · intro im
          obtain rfl := mem_singleton.mp im
          exact mem_outN.mpr ⟨mem_insert_self _ _,fr⟩
      exact ⟨by rw [← erase,card_erase_of_mem fm,cycle.size]; omega,fc,by simp [count],pay⟩
    obtain ⟨size,pc,ph,pp⟩ := paid ps (mem_inter.mp rm).1 (fun v vm => light v (mem_union_left _ vm))
    obtain ⟨_,tc,th,tp⟩ := paid ts (mem_inter.mp rm).2 (fun v vm => light v (mem_union_right _ vm))
    exact Or.inl ⟨r,rm,size,pc,tc,ph,th,pp,tp⟩
  · exact Or.inr residual

#print axioms shared_bank

theorem bank_after_merge {q n} (X : Model q n) (hq : 2 ≤ q) {F L A B K z p t w}
    (native : F ⊆ family X) (cl : Cycle X.D X.V q L) (left : Supports X.D F L z A)
    (right : Supports X.D F L z B) (zl : z ∉ L)
    (pl : p ∈ L) (tl : t ∈ L) (pt : p ≠ t) (pa : p ∈ A) (tb : t ∈ B)
    (pz : X.D p z = true) (tz : X.D t z = true) (wa : w ∈ A) (zw : X.D z w = true)
    (ac : Relation.ReflTransGen (Step X.D F L z) A K) (bc : Relation.ReflTransGen (Step X.D F L z) B K)
    (finalSupport : Supports X.D F L z K) :
    SharedOutcome X.D X.V (A \ L) q p t z w := by
  classical
  obtain ⟨same,oneA,oneB,_⟩ := merge_footprint X hq native cl left pl tl pt pa tb pz tz ac bc finalSupport
  have split {C f} (inC : f ∈ C) (one : L ∩ C = {f}) : C = insert f (C \ L) := by
    ext i
    by_cases il : i ∈ L
    · have iff : i ∈ C ↔ i = f := ⟨fun ic => mem_singleton.mp (one ▸ mem_inter.mpr ⟨il,ic⟩ : i ∈ ({f}:Finset ℕ)),
        fun eq => eq ▸ inC⟩
      simpa [mem_sdiff,il] using iff
    · simp [mem_sdiff,il]
      exact fun eq => eq ▸ inC
  have ca : Cycle X.D X.V q A := (mem_filter.mp (native left.1)).2
  have cb : Cycle X.D X.V q B := (mem_filter.mp (native right.1)).2
  have wp : w ≠ p := by
    intro eq
    exact X.free p 2 (by decide) hq (.step (ca.sub left.2.1) pz (.step (ca.sub pa) (eq ▸ zw) (.refl p)))
  have wl : w ∉ L := fun m => wp (mem_singleton.mp (oneA ▸ mem_inter.mpr ⟨m,wa⟩ : w ∈ ({p}:Finset ℕ)))
  have a : Cycle X.D X.V q (insert p (A \ L)) := (split pa oneA) ▸ ca
  have b : Cycle X.D X.V q (insert t (A \ L)) := same.symm ▸ ((split tb oneB) ▸ cb : Cycle X.D X.V q (insert t (B \ L)))
  exact shared_bank hq X.free a b (fun m => (mem_sdiff.mp m).2 pl) (fun m => (mem_sdiff.mp m).2 tl)
    (mem_sdiff.mpr ⟨left.2.1,zl⟩) (mem_sdiff.mpr ⟨wa,wl⟩) pz tz zw

#print axioms bank_after_merge
end LeanCH.BR.Closure.ReceiverRetry
