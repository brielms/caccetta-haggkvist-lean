import checkpoints.shen_extension.ReceiverRetryMerge

namespace LeanCH.BR.Closure.ReceiverRetry
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier

/-- A native shortest cycle with at most one vertex outside an old cycle
already belongs to the family, or supplies a boundary with at most two targets. -/
theorem one_change {q n} (X : Model q n) (hq : 2 ≤ q) {F A N j}
    (af : A ∈ F) (cn : Cycle X.D X.V q N) (jn : j ∈ N) (rest : ∀ v ∈ N, v ≠ j → v ∈ A) :
    N ∈ F ∨ (Boundary X F N ∧ (targets X.D X.V F N).card ≤ 2) := by
  classical
  by_cases nf : N ∈ F
  · exact Or.inl nf
  obtain ⟨b,bm⟩ := card_pos.mp (show 0 < (outN X.D N j).card by rw [cn.heads j jn]; decide)
  obtain ⟨bn,jb⟩ := mem_outN.mp bm
  have cap : ({j,b} : Finset ℕ).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have shared {v} (vn : v ∈ N) (away : v ∉ ({j,b}:Finset ℕ)) {t} (tn : t ∈ N) (tv : X.D t v = true) :
      t ∈ A ∧ v ∈ A := by
    have tj : t ≠ j := by
      rintro rfl
      have vb := card_le_one.mp (cn.heads t tn).le v (mem_outN.mpr ⟨vn,tv⟩) b (mem_outN.mpr ⟨bn,jb⟩)
      exact away (mem_insert_of_mem (mem_singleton.mpr vb))
    exact ⟨rest t tn tj,rest v vn (fun e => away (mem_insert.mpr (Or.inl e)))⟩
  have outside : ¬ N ⊆ ({j,b}:Finset ℕ) := by
    intro inc
    have := (card_le_card inc).trans cap
    have := cn.size
    omega
  obtain ⟨v,vn,away⟩ := not_subset.mp outside
  have cnt : (inN X.D N v).card = 1 := cn.incoming v vn
  obtain ⟨t,tm⟩ := card_pos.mp (show 0 < (inN X.D N v).card by omega)
  obtain ⟨tn,tv⟩ := mem_inN.mp tm
  obtain ⟨ta,va⟩ := shared vn away tn tv
  refine Or.inr ⟨⟨mem_filter.mpr ⟨mem_powerset.mpr cn.sub,cn⟩,nf,A,af,t,
    mem_inter.mpr ⟨ta,tn⟩,v,mem_inter.mpr ⟨va,vn⟩,tv⟩,LE.le.trans (card_le_card ?_) cap⟩
  intro i im
  by_contra miss
  obtain ⟨_,inside,u,un,ui,off⟩ := mem_filter.mp im
  obtain ⟨ua,ia⟩ := shared inside miss un ui
  exact Bool.noConfusion (off.symm.trans (active.mpr ⟨A,mem_col.mpr ⟨af,ua,ia,ui⟩⟩))

/-- A middle vertex d points to z on its supporting cycle. Every exterior
head of d that loses two heads on this cycle loses exactly z and its successor.
The same head can replace z on the native cycle. -/
theorem two_loss {D V q K d z w v} (hq : 2 ≤ q) (free : QFree D V q) (ck : Cycle D V q K)
    (dk : d ∈ K) (zk : z ∈ K) (wk : w ∈ K) (dz : D d z = true) (zw : D z w = true)
    (outside : v ∈ V \ K) (dv : D d v = true) (two : 2 ≤ (outN D K v).card) :
    outN D K v = {z,w} ∧ inN D K v = {d} ∧ Cycle D V q (insert v (K.erase z)) := by
  classical
  obtain ⟨a,u,N,sh,cn,heads,parents⟩ := CycleSquareTensor.replacement hq free.reverse
    (SharedArcGrid.reverse_cycle ck) outside two dk dv
  obtain rfl : u = z := card_le_one.mp (ck.heads d dk).le u (mem_outN.mpr ⟨sh.uM,sh.before₂⟩)
    z (mem_outN.mpr ⟨zk,dz⟩)
  obtain rfl : a = w := card_le_one.mp (ck.heads u sh.uM).le a (mem_outN.mpr ⟨sh.aM,sh.before₁⟩)
    w (mem_outN.mpr ⟨wk,zw⟩)
  exact ⟨heads.trans (pair_comm _ _),parents,sh.labels ▸ SharedArcGrid.reverse_cycle cn⟩

/-- The replacement is an old family member when the least boundary needs
at least three targets. Otherwise the bound holds at the original boundary. -/
theorem two_loss_at_boundary {q n} (X : Model q n) (hq : 2 ≤ q) {F L K d z w v}
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (kf : K ∈ F) (ck : Cycle X.D X.V q K)
    (dk : d ∈ K) (zk : z ∈ K) (wk : w ∈ K) (dz : X.D d z = true) (zw : X.D z w = true)
    (outside : v ∈ X.V \ K) (dv : X.D d v = true) (two : 2 ≤ (outN X.D K v).card) :
    outN X.D K v = {z,w} ∧ inN X.D K v = {d} ∧ Cycle X.D X.V q (insert v (K.erase z)) ∧
      (insert v (K.erase z) ∈ F ∨ (targets X.D X.V F L).card ≤ 2) := by
  obtain ⟨heads,parents,cn⟩ := two_loss hq X.free ck dk zk wk dz zw outside dv two
  refine ⟨heads,parents,cn,?_⟩
  rcases one_change X hq kf cn (mem_insert_self _ _)
    (fun i im ne => mem_of_mem_erase ((mem_insert.mp im).resolve_left ne)) with old | ⟨bd,cap⟩
  · exact Or.inl old
  · exact Or.inr ((least _ bd).trans cap)

#print axioms one_change
#print axioms two_loss_at_boundary

/-- The successor is chosen once on the actual support, before quantifying
over its feeder's exterior heads. -/
theorem uniform_loss_targets {q n} (X : Model q n) (hq : 2 ≤ q) {F L K d z}
    (native : F ⊆ family X) (kf : K ∈ F)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (dk : d ∈ K) (zk : z ∈ K) (dz : X.D d z = true) :
    ∃ w ∈ K, X.D z w = true ∧ ∀ v ∈ X.V \ K, X.D d v = true → 2 ≤ (outN X.D K v).card →
      outN X.D K v = {z,w} ∧ inN X.D K v = {d} ∧ Cycle X.D X.V q (insert v (K.erase z)) ∧
      (insert v (K.erase z) ∈ F ∨ (targets X.D X.V F L).card ≤ 2) := by
  classical
  have ck : Cycle X.D X.V q K := (mem_filter.mp (native kf)).2
  obtain ⟨w,wm⟩ := card_pos.mp (show 0 < (outN X.D K z).card by rw [ck.heads z zk]; decide)
  obtain ⟨wk,zw⟩ := mem_outN.mp wm
  exact ⟨w,wk,zw,fun _ vv dv many => two_loss_at_boundary X hq least kf ck dk zk wk dz zw vv dv many⟩

#print axioms uniform_loss_targets
end LeanCH.BR.Closure.ReceiverRetry
