import checkpoints.shen_extension.ReceiverRetry

namespace LeanCH.BR.Closure.ReceiverRetry
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

/-- Every retry retains the exact exterior labels and the number of boundary labels. -/
theorem path_footprint {D F L z A K} (path : Relation.ReflTransGen (Step D F L z) A K) :
    A \ L = K \ L ∧ (L ∩ A).card = (L ∩ K).card := by
  classical
  induction path with
  | refl => exact ⟨rfl,rfl⟩
  | @tail B C _ edge ih =>
    obtain ⟨_,_,x,j,tr,rfl⟩ := edge
    have xl : x ∈ L := (mem_added.mp tr.fresh).1
    have jl : j ∈ L := (mem_added.mp tr.fresh).2.1
    have outer : B \ L = (insert j (B.erase x)) \ L := by
      ext i
      simp only [mem_sdiff,mem_insert,mem_erase]
      grind
    have sz : (insert j (B.erase x)).card = B.card := by
      have nj : j ∉ B.erase x := fun m => tr.outside (mem_of_mem_erase m)
      rw [card_insert_of_notMem nj,card_erase_of_mem tr.tail]
      have := card_pos.mpr ⟨x,tr.tail⟩
      omega
    refine ⟨ih.1.trans outer,ih.2.trans ?_⟩
    have h1 := card_sdiff_add_card_inter B L
    have h2 := card_sdiff_add_card_inter (insert j (B.erase x)) L
    rw [← outer,sz] at h2
    rw [inter_comm L B,inter_comm L (insert j (B.erase x))]
    omega

/-- A support that overlaps the boundary in at least two labels keeps its original feeder forever. -/
theorem keeps_feeder {q n} (X : Model q n) (hq : 2 ≤ q) {F L z A K p}
    (native : F ⊆ family X) (cl : Cycle X.D X.V q L)
    (pl : p ∈ L) (pa : p ∈ A) (pz : X.D p z = true) (big : 2 ≤ (L ∩ A).card)
    (path : Relation.ReflTransGen (Step X.D F L z) A K) : p ∈ K := by
  classical
  induction path with
  | refl => exact pa
  | @tail B C prior edge ih =>
    obtain ⟨old,next,x,j,tr,labels⟩ := edge
    by_contra gone
    have xp : x = p := by
      by_contra diff
      exact gone (labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨Ne.symm diff,ih⟩))
    obtain ⟨cf,zc,t,tl,tc,tz⟩ := next
    have pt : p ≠ t := fun eq => gone (eq ▸ tc)
    have cyc (M) (mf : M ∈ F) : Cycle X.D X.V q M := (mem_filter.mp (native mf)).2
    have apart := BoundaryReceiverWitness.separate hq X.free cl (cyc B old.1) (cyc C cf)
      pl tl pt pz tz ih old.2.1 tc zc
    have many : 2 ≤ (L ∩ B).card := (path_footprint prior).2 ▸ big
    have only : L ∩ B ⊆ {p} := by
      intro v vm
      by_contra miss
      have vx : v ≠ x := fun eq => miss (mem_singleton.mpr (eq.trans xp))
      have kept : v ∈ C := labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨vx,(mem_inter.mp vm).2⟩)
      exact disjoint_left.mp apart vm (mem_inter.mpr ⟨(mem_inter.mp vm).1,kept⟩)
    have cap : (L ∩ B).card ≤ 1 := by simpa using card_le_card only
    omega

/-- If traces from two distinct physical feeders ever meet, both initial cycles
share all q exterior labels. Only their singleton boundary labels differ. -/
theorem merge_footprint {q n} (X : Model q n) (hq : 2 ≤ q) {F L z A B K p t}
    (native : F ⊆ family X) (cl : Cycle X.D X.V q L)
    (left : Supports X.D F L z A)
    (pl : p ∈ L) (tl : t ∈ L) (pt : p ≠ t) (pa : p ∈ A) (tb : t ∈ B)
    (pz : X.D p z = true) (tz : X.D t z = true)
    (ac : Relation.ReflTransGen (Step X.D F L z) A K) (bc : Relation.ReflTransGen (Step X.D F L z) B K)
    (terminal : Supports X.D F L z K) :
    A \ L = B \ L ∧ L ∩ A = {p} ∧ L ∩ B = {t} ∧ (A \ L).card = q := by
  classical
  obtain ⟨oa,sa⟩ := path_footprint ac
  obtain ⟨ob,sb⟩ := path_footprint bc
  have cy (M) (mf : M ∈ F) : Cycle X.D X.V q M := (mem_filter.mp (native mf)).2
  have small : (L ∩ K).card ≤ 1 := by
    by_contra! big
    have pk := keeps_feeder X hq native cl pl pa pz (by omega) ac
    have tk := keeps_feeder X hq native cl tl tb tz (by omega) bc
    exact pt (card_le_one.mp ((cy K terminal.1).incoming z terminal.2.1).le
      p (mem_inN.mpr ⟨pk,pz⟩) t (mem_inN.mpr ⟨tk,tz⟩))
  have aeq := eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_inter.mpr ⟨pl,pa⟩))
    (show (L ∩ A).card ≤ ({p}:Finset ℕ).card by simpa using sa.le.trans small)
  have beq := eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_inter.mpr ⟨tl,tb⟩))
    (show (L ∩ B).card ≤ ({t}:Finset ℕ).card by simpa using sb.le.trans small)
  have total := card_sdiff_add_card_inter A L
  rw [inter_comm A L,← aeq,card_singleton] at total
  have size := (cy A left.1).size
  exact ⟨oa.trans ob.symm,aeq.symm,beq.symm,by omega⟩

#print axioms path_footprint
#print axioms keeps_feeder
#print axioms merge_footprint

private theorem supports_after {D F L z A J} (ok : Supports D F L z A)
    (path : Relation.ReflTransGen (Step D F L z) A J) : Supports D F L z J := by
  cases path with
  | refl => exact ok
  | tail _ e => exact e.2.1

/-- Once two distinct feeder traces can merge, all continuations from either
start keep the same exterior q-set and the same labelled two-edge route,
apart from its middle vertex. All these arcs belong to the old family. -/
theorem merge_corridor {q n} (X : Model q n) (hq : 2 ≤ q) {F L z A B K p t}
    (native : F ⊆ family X) (cl : Cycle X.D X.V q L)
    (left : Supports X.D F L z A) (right : Supports X.D F L z B)
    (pl : p ∈ L) (tl : t ∈ L) (pt : p ≠ t) (pa : p ∈ A) (tb : t ∈ B)
    (pz : X.D p z = true) (tz : X.D t z = true)
    (ac : Relation.ReflTransGen (Step X.D F L z) A K) (bc : Relation.ReflTransGen (Step X.D F L z) B K) :
    (A \ L).card = q ∧ ∃ y ∈ A \ L, graph X.D F y p = true ∧ graph X.D F y t = true ∧
      ∀ J, (Relation.ReflTransGen (Step X.D F L z) A J ∨ Relation.ReflTransGen (Step X.D F L z) B J) →
        ∃ d ∈ L, J = insert d (A \ L) ∧ graph X.D F y d = true ∧ graph X.D F d z = true := by
  classical
  obtain ⟨outer,oneA,oneB,sz⟩ := merge_footprint X hq native cl left pl tl pt pa tb pz tz
    ac bc (supports_after left ac)
  have cy (M) (mf : M ∈ F) : Cycle X.D X.V q M := (mem_filter.mp (native mf)).2
  have ca := cy A left.1
  have parentCount : (inN X.D A p).card = 1 := ca.incoming p pa
  obtain ⟨y,yp'⟩ := card_pos.mp (show 0 < (inN X.D A p).card by omega)
  obtain ⟨ya,yp⟩ := mem_inN.mp yp'
  have ypne : y ≠ p := fun h => loopfree X.free (by omega) (ca.sub pa) (h ▸ yp)
  have yl : y ∉ L := fun m => ypne (mem_singleton.mp (oneA ▸ mem_inter.mpr ⟨m,ya⟩ : y ∈ ({p}:Finset ℕ)))
  have ys : y ∈ A \ L := mem_sdiff.mpr ⟨ya,yl⟩
  have move {J d} (ok : Supports X.D F L z J) (same : A \ L = J \ L) (singleton : L ∩ J = {d})
      (dj : d ∈ J) : graph X.D F y d = true := by
    have yj := (mem_sdiff.mp (same ▸ ys)).1
    obtain ⟨v,vn⟩ := card_pos.mp (show 0 < (outN X.D J y).card by rw [(cy J ok.1).heads y yj]; decide)
    obtain ⟨vj,yv⟩ := mem_outN.mp vn
    have vl : v ∈ L := by
      by_contra outside
      have va := (mem_sdiff.mp (same.symm ▸ (mem_sdiff.mpr ⟨vj,outside⟩ : v ∈ J \ L))).1
      have vp := card_le_one.mp (ca.heads y ya).le v (mem_outN.mpr ⟨va,yv⟩) p (mem_outN.mpr ⟨pa,yp⟩)
      exact outside (vp ▸ pl)
    have vd : v = d := mem_singleton.mp (singleton ▸ mem_inter.mpr ⟨vl,vj⟩ : v ∈ ({d}:Finset ℕ))
    exact active.mpr ⟨J,mem_col.mpr ⟨ok.1,yj,dj,vd ▸ yv⟩⟩
  refine ⟨sz,y,ys,active.mpr ⟨A,mem_col.mpr ⟨left.1,ya,pa,yp⟩⟩,move right outer oneB tb,?_⟩
  intro J reach
  have data : Supports X.D F L z J ∧ A \ L = J \ L ∧ (L ∩ J).card = 1 := by
    rcases reach with a|b
    · exact ⟨supports_after left a,(path_footprint a).1,by rw [← (path_footprint a).2,oneA,card_singleton]⟩
    · exact ⟨supports_after right b,outer.trans (path_footprint b).1,by rw [← (path_footprint b).2,oneB,card_singleton]⟩
  obtain ⟨ok,same,one⟩ := data
  obtain ⟨d,dl,dj,dz⟩ := ok.2.2
  have singleton : L ∩ J = {d} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_inter.mpr ⟨dl,dj⟩))
    (by simpa using one.le)).symm
  refine ⟨d,dl,?_,move ok same singleton dj,active.mpr ⟨J,mem_col.mpr ⟨ok.1,dj,ok.2.1,dz⟩⟩⟩
  rw [same]
  ext v
  by_cases vl : v ∈ L
  · have iff : v ∈ J ↔ v = d := by
      constructor
      · intro vj
        exact mem_singleton.mp (singleton ▸ mem_inter.mpr ⟨vl,vj⟩ : v ∈ ({d}:Finset ℕ))
      · rintro rfl
        exact dj
    simpa [mem_sdiff,vl] using iff
  · have ne : v ≠ d := fun e => vl (e ▸ dl)
    simp [mem_sdiff,vl,ne]

#print axioms merge_corridor
end LeanCH.BR.Closure.ReceiverRetry
