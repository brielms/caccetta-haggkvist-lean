import checkpoints.shen_extension.ReceiverMixture

namespace LeanCH.BR.Closure.ReceiverRetry
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

variable {D : CH.Digraph} {F : Family} {L A : Finset ℕ} {z x j : ℕ}

def Supports (D : CH.Digraph) (F : Family) (L : Finset ℕ) (z : ℕ) (A : Finset ℕ) : Prop :=
  A ∈ F ∧ z ∈ A ∧ ∃ p ∈ L, p ∈ A ∧ D p z = true

structure Trigger (D : CH.Digraph) (F : Family) (L A : Finset ℕ) (x j : ℕ) : Prop where
  tail : x ∈ A
  outside : j ∉ A
  fresh : (x,j) ∈ added D F L
  entering : ∃ y ∈ A, graph D F y j = true
  returning : ∃ b ∈ A, graph D F j b = true

/-- Both endpoints support an old arc from the fixed boundary into the same receiver. -/
def Step (D : CH.Digraph) (F : Family) (L : Finset ℕ) (z : ℕ) (A B : Finset ℕ) : Prop :=
  Supports D F L z A ∧ Supports D F L z B ∧
    ∃ x j, Trigger D F L A x j ∧ B = insert j (A.erase x)

/-- The old shared arc prevents every fresh arc, including a move of the
original feeder, from crossing the cut in the cyclic order of L. -/
theorem rank_steps {q n} (X : Model q n) {F L z} (bd : Boundary X F L) :
    ∃ rank : Finset ℕ → ℕ, ∀ A B, Step X.D F L z A B → rank B = rank A + 1 := by
  classical
  obtain ⟨M,mf,c,cm,h,hm,ch⟩ := bd.2.2
  obtain ⟨cM,cL⟩ := mem_inter.mp cm
  obtain ⟨hM,hL⟩ := mem_inter.mp hm
  have old : graph X.D F c h = true := active.mpr ⟨M,mem_col.mpr ⟨mf,cM,hM,ch⟩⟩
  have cl : Cycle X.D X.V q L := (mem_filter.mp bd.1).2
  let position (i : ℕ) := if i ∈ L then PuncturedDistance.depth X.D X.V h i else 0
  refine ⟨fun C => ∑ i ∈ C, position i, ?_⟩
  rintro A B ⟨_,_,x,j,tr,rfl⟩
  obtain ⟨xl,jl,xj,off⟩ := mem_added.mp tr.fresh
  have jh : j ≠ h := by
    rintro rfl
    have xc := card_le_one.mp (cl.incoming j jl).le x (mem_inN.mpr ⟨xl,xj⟩) c (mem_inN.mpr ⟨cL,ch⟩)
    exact Bool.noConfusion (off.symm.trans (xc ▸ old))
  have rise := PuncturedDistance.rise_on_cycle X.free cl hL xl jl jh xj
  have val : position j = position x + 1 := by simpa [position,xl,jl] using rise
  have no : j ∉ A.erase x := fun m => tr.outside (mem_of_mem_erase m)
  change (∑ i ∈ insert j (A.erase x), position i) = (∑ i ∈ A, position i) + 1
  rw [sum_insert no]
  have total := sum_erase_add A position tr.tail
  omega

theorem reachable_terminal {q n} (X : Model q n) {F L z A} (bd : Boundary X F L)
    (seed : Supports X.D F L z A) :
    ∃ K, Relation.ReflTransGen (Step X.D F L z) A K ∧ Supports X.D F L z K ∧
      ∀ U, ¬ Step X.D F L z K U := by
  classical
  obtain ⟨rank,gain⟩ := rank_steps (z:=z) X bd
  let reach := F.filter (fun K => Supports X.D F L z K ∧ Relation.ReflTransGen (Step X.D F L z) A K)
  have start : A ∈ reach := mem_filter.mpr ⟨seed.1,seed,.refl⟩
  obtain ⟨K,km,peak⟩ := reach.exists_max_image rank ⟨A,start⟩
  obtain ⟨_,ok,path⟩ := mem_filter.mp (show K ∈ F.filter _ from km)
  refine ⟨K,path,ok,fun U step => ?_⟩
  have um : U ∈ reach := mem_filter.mpr ⟨step.2.1.1,step.2.1,path.tail step⟩
  have := peak U um
  have := gain K U step
  omega

/-- If the removed vertex is the feeder, the back arc lands at the receiver.
The two supports then intersect the boundary only at their respective feeders. -/
theorem feeder_handoff {q n} (X : Model q n) (hq : 2 ≤ q) {L A : Finset ℕ} {x j z b}
    (cl : Cycle X.D X.V q L) (ca : Cycle X.D X.V q A)
    (cn : Cycle X.D X.V q (insert j (A.erase x)))
    (xl : x ∈ L) (jl : j ∈ L) (zl : z ∉ L) (xa : x ∈ A) (ja : j ∉ A) (za : z ∈ A)
    (xz : X.D x z = true) (ba : b ∈ A) (xb : X.D x b = true) (jb : X.D j b = true) :
    X.D j z = true ∧ L ∩ A = {x} ∧ L ∩ insert j (A.erase x) = {j} := by
  classical
  obtain rfl : b = z := card_le_one.mp (ca.heads x xa).le b (mem_outN.mpr ⟨ba,xb⟩) z (mem_outN.mpr ⟨za,xz⟩)
  have zx : b ≠ x := fun e => zl (e ▸ xl)
  have xj : x ≠ j := fun e => ja (e ▸ xa)
  have zn : b ∈ insert j (A.erase x) := mem_insert_of_mem (mem_erase.mpr ⟨zx,za⟩)
  have dis := BoundaryReceiverWitness.separate hq X.free cl ca cn xl jl xj xz jb xa za (mem_insert_self _ _) zn
  refine ⟨jb,Subset.antisymm ?_ (singleton_subset_iff.mpr (mem_inter.mpr ⟨xl,xa⟩)),
    Subset.antisymm ?_ (singleton_subset_iff.mpr (mem_inter.mpr ⟨jl,mem_insert_self _ _⟩))⟩
  · intro i im
    by_contra miss
    have ix : i ≠ x := by simpa using miss
    obtain ⟨il,ia⟩ := mem_inter.mp im
    exact disjoint_left.mp dis im (mem_inter.mpr ⟨il,mem_insert_of_mem (mem_erase.mpr ⟨ix,ia⟩)⟩)
  · intro i im
    by_contra miss
    obtain ⟨il,inside⟩ := mem_inter.mp im
    have ia := mem_of_mem_erase ((mem_insert.mp inside).resolve_left (by simpa using miss))
    exact disjoint_left.mp dis (mem_inter.mpr ⟨il,ia⟩) im

theorem step_of_trigger {q n} (X : Model q n) (hq : 2 ≤ q) {F L A z x j}
    (small : SmallRow q (graph X.D F) X.V)
    (every : ∀ M, Boundary X F M → ¬ SmallRow q (graph X.D (insert M F)) X.V)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (cl : Cycle X.D X.V q L) (ca : Cycle X.D X.V q A) (zl : z ∉ L)
    (ok : Supports X.D F L z A) (tr : Trigger X.D F L A x j) :
    added X.D F L = {(x,j)} ∨ Step X.D F L z A (insert j (A.erase x)) := by
  classical
  obtain ⟨af,za,p,pl,pa,pz⟩ := ok
  obtain ⟨y,ya,yj⟩ := tr.entering
  obtain ⟨b,ba,jb⟩ := tr.returning
  have jl := (mem_added.mp tr.fresh).2.1
  have xl := (mem_added.mp tr.fresh).1
  rcases ReceiverMixture.retry_support X hq small every least cl ca af (cl.sub jl)
    tr.outside tr.tail tr.fresh ya yj ba (CrossValueOmissions.selected_sub jb) jb with single | retry
  · exact Or.inl single
  obtain ⟨nf,cn,_,xb,keep⟩ := retry
  have zn := keep z za (fun e => zl (e ▸ xl))
  refine Or.inr ⟨⟨af,za,p,pl,pa,pz⟩,⟨nf,zn,?_⟩,x,j,tr,rfl⟩
  by_cases same : p = x
  · subst p
    exact ⟨j,jl,mem_insert_self _ _,(feeder_handoff X hq cl ca cn xl jl zl tr.tail tr.outside za pz ba xb
      (CrossValueOmissions.selected_sub jb)).1⟩
  · exact ⟨p,pl,keep p pa same,pz⟩

theorem terminal_column {q n} (X : Model q n) (hq : 2 ≤ q) {F L A}
    (cl : Cycle X.D X.V q L) (ca : Cycle X.D X.V q A)
    (noTrigger : ∀ x j, ¬ Trigger X.D F L A x j) {j}
    (high : (q:ℝ)+1 < ReceiverMixture.count q (graph X.D (insert L F)) A j) :
    2 ≤ (inN (graph X.D F) A j).card ∨
      ((inN (graph X.D F) A j).card = 1 ∧ (∃ x ∈ A, (x,j) ∈ added X.D F L) ∧
        ∀ b ∈ A, graph X.D F j b ≠ true) := by
  classical
  obtain ⟨ja,two⟩ := ReceiverMixture.over_count hq ca (fun _ _ e => CrossValueOmissions.selected_sub e) high
  by_cases old : 2 ≤ (inN (graph X.D F) A j).card
  · exact Or.inl old
  obtain ⟨v,vh,w,wh,ne⟩ := one_lt_card.mp two
  obtain ⟨va,vj⟩ := mem_inN.mp vh
  obtain ⟨wa,wj⟩ := mem_inN.mp wh
  have pair : (∃ y ∈ A, graph X.D F y j = true) ∧ (∃ x ∈ A, (x,j) ∈ added X.D F L) := by
    rcases union_arc.mp vj with vo|vf <;> rcases union_arc.mp wj with wo|wf
    · exact (old (one_lt_card.mpr ⟨v,mem_inN.mpr ⟨va,vo⟩,w,mem_inN.mpr ⟨wa,wo⟩,ne⟩)).elim
    · exact ⟨⟨v,va,vo⟩,w,wa,wf⟩
    · exact ⟨⟨w,wa,wo⟩,v,va,vf⟩
    · exact (ne (ThirdPrice.new_parent_unique cl vf wf)).elim
  obtain ⟨incoming,x,xa,xf⟩ := pair
  have pos : 0 < (inN (graph X.D F) A j).card := by
    obtain ⟨y,ya,yj⟩ := incoming
    exact card_pos.mpr ⟨y,mem_inN.mpr ⟨ya,yj⟩⟩
  exact Or.inr ⟨by omega,⟨x,xa,xf⟩,fun b ba jb => noTrigger x j ⟨xa,ja,xf,incoming,b,ba,jb⟩⟩

/-- A native return from a doubly fed exterior column into an old cycle
is already an old arc whenever the minimum boundary has at least three targets. -/
theorem native_return_cost {q n} (X : Model q n) (hq : 2 ≤ q) {F L K j b}
    (ck : Cycle X.D X.V q K) (kf : K ∈ F)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (jv : j ∈ X.V) (jk : j ∉ K) (rich : 2 ≤ (inN X.D K j).card)
    (bk : b ∈ K) (jb : X.D j b = true) :
    graph X.D F j b = true ∨ (targets X.D X.V F L).card ≤ 2 := by
  classical
  by_cases old : graph X.D F j b = true
  · exact Or.inl old
  obtain ⟨a,u,N,sh,cn,_,_⟩ := CycleSquareTensor.replacement hq X.free ck (mem_sdiff.mpr ⟨jv,jk⟩) rich bk jb
  have bu : b ≠ u := fun e => loopfree X.free (by omega) (ck.sub sh.uM) (e ▸ sh.before₂)
  have jn : j ∈ N := sh.labels ▸ mem_insert_self _ _
  have bn : b ∈ N := sh.labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨bu,bk⟩)
  obtain ⟨d,dm⟩ := card_pos.mp (show 0 < (outN X.D K b).card by rw [ck.heads b bk]; decide)
  obtain ⟨dk,bd⟩ := mem_outN.mp dm
  have du : d ≠ u := by
    rintro rfl
    exact X.free b 2 (by decide) hq (.step (ck.sub dk) bd (.step (ck.sub bk) sh.before₂ (.refl b)))
  have dn : d ∈ N := sh.labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨du,dk⟩)
  have bound : Boundary X F N := ⟨mem_filter.mpr ⟨mem_powerset.mpr cn.sub,cn⟩,
    fun nf => old (active.mpr ⟨N,mem_col.mpr ⟨nf,jn,bn,jb⟩⟩),
    K,kf,b,mem_inter.mpr ⟨bk,bn⟩,d,mem_inter.mpr ⟨dk,dn⟩,bd⟩
  have small : targets X.D X.V F N ⊆ {j,b} := by
    intro v vm
    obtain ⟨_,vn,t,tn,tv,miss⟩ := mem_filter.mp vm
    by_cases vj : v = j
    · exact mem_insert.mpr (Or.inl vj)
    by_cases tj : t = j
    · subst t
      exact mem_insert.mpr (Or.inr (mem_singleton.mpr (card_le_one.mp (cn.heads j jn).le
        v (mem_outN.mpr ⟨vn,tv⟩) b (mem_outN.mpr ⟨bn,jb⟩))))
    rw [sh.labels] at tn vn
    have vk := mem_of_mem_erase ((mem_insert.mp vn).resolve_left vj)
    have tk := mem_of_mem_erase ((mem_insert.mp tn).resolve_left tj)
    exact Bool.noConfusion (miss.symm.trans (active.mpr ⟨K,mem_col.mpr ⟨kf,tk,vk,tv⟩⟩))
  exact Or.inr ((least N bound).trans ((card_le_card small).trans (by
    by_cases h : j = b <;> simp [h])))

/-- On the same failed attachment every initial receiver support can be
normalized by actual retries, with a complete list of terminal column types. -/
theorem on_boundary {q n} (X : Model q n) (hq : 2 ≤ q) {F L A z}
    (native : F ⊆ family X) (small : SmallRow q (graph X.D F) X.V)
    (every : ∀ M, Boundary X F M → ¬ SmallRow q (graph X.D (insert M F)) X.V)
    (bd : Boundary X F L)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (zl : z ∉ L) (seed : Supports X.D F L z A) :
    ∃ K, Relation.ReflTransGen (Step X.D F L z) A K ∧ Supports X.D F L z K ∧
      (∀ U, ¬ Step X.D F L z K U) ∧
      (∃ j ∈ X.V, (q:ℝ)+1 < ReceiverMixture.count q (graph X.D (insert L F)) K j) ∧
      ((∃ e, added X.D F L = {e}) ∨
        ∀ j, (q:ℝ)+1 < ReceiverMixture.count q (graph X.D (insert L F)) K j →
          2 ≤ (inN (graph X.D F) K j).card ∨
          ((inN (graph X.D F) K j).card = 1 ∧ (∃ x ∈ K, (x,j) ∈ added X.D F L) ∧
            (∀ b ∈ K, graph X.D F j b ≠ true) ∧
            (3 ≤ (targets X.D X.V F L).card → ∀ b ∈ K, X.D j b ≠ true))) := by
  classical
  obtain ⟨K,path,ok,stop⟩ := reachable_terminal X bd seed
  have ck : Cycle X.D X.V q K := (mem_filter.mp (native ok.1)).2
  have cl : Cycle X.D X.V q L := (mem_filter.mp bd.1).2
  refine ⟨K,path,ok,stop,?_,?_⟩
  · by_contra! low
    exact every L bd (smallRow_of_realDual (ReceiverMixture.half_pays ck ck
      (fun i iv => by linarith [low i iv])))
  by_cases one : ∃ e, added X.D F L = {e}
  · exact Or.inl one
  have no (x j) (tr : Trigger X.D F L K x j) : False := by
    rcases step_of_trigger X hq small every least cl ck zl ok tr with h|h
    · exact one ⟨_,h⟩
    · exact stop _ h
  right
  intro j high
  rcases terminal_column X hq cl ck no high with old | ⟨oneOld,fresh,noBack⟩
  · exact Or.inl old
  refine Or.inr ⟨oneOld,fresh,noBack,?_⟩
  intro many b bk jb
  obtain ⟨x,_,xj⟩ := fresh
  have jv := cl.sub (mem_added.mp xj).2.1
  obtain ⟨jk,two⟩ := ReceiverMixture.over_count hq ck (fun _ _ e => CrossValueOmissions.selected_sub e) high
  have rich := two.trans (card_le_card (show inN (graph X.D (insert L F)) K j ⊆ inN X.D K j from
    fun _ m => mem_inN.mpr ⟨(mem_inN.mp m).1,CrossValueOmissions.selected_sub (mem_inN.mp m).2⟩))
  rcases native_return_cost X hq ck ok.1 least jv jk rich bk jb with edge | cost
  · exact noBack b bk edge
  · omega

#print axioms rank_steps
#print axioms reachable_terminal
#print axioms feeder_handoff
#print axioms native_return_cost
#print axioms on_boundary
end LeanCH.BR.Closure.ReceiverRetry
