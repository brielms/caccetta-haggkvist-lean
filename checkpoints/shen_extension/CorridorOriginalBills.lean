import checkpoints.shen_extension.ReceiverRetryMerge
import checkpoints.shen_extension.SharedArcBudget

namespace LeanCH.BR.CorridorPayment
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor
open Closure.ShortestCycleWeights Closure.FirstPacketBarrier Closure.MarkedCyclePeeling
open Closure.SharedArcBarrier Closure.SharedArcExpansion Closure.SharedArcComponentExchange

/-- Every physical middle vertex of the same two-edge path gives a candidate
on the original selected family. The two tests use its original price vector. -/
theorem replacement {q n} (X : Model q n) (hq : 2≤q) {F : Family} {A : Finset ℕ} {y p z r}
    (ca : Cycle X.D X.V q A) (af : A∈F) (pa : p∈A) (ya : y∈A) (za : z∈A)
    (yp : X.D y p=true) (pz : X.D p z=true) (rv : r∈X.V) (yr : X.D y r=true) (rz : X.D r z=true) :
    let M := insert r (A.erase p)
    Cycle X.D X.V q M ∧
    (M∉F → Boundary X F M) ∧
    (∀u v, (u,v)∈added X.D F M ↔
      (u=y ∧ v=r ∧ graph X.D F y r=false) ∨ (u=r ∧ v=z ∧ graph X.D F r z=false)) ∧
    (∀π : ℕ→ℝ, RealDual q (graph X.D F) X.V 1 π →
      (RealDual q (graph X.D (insert M F)) X.V 1 π ↔
        (graph X.D F y r=false → realCol q (graph X.D F) X.V π r + q*π y≤1) ∧
        (graph X.D F r z=false → realCol q (graph X.D F) X.V π z + q*π r≤1))) := by
  classical
  let M := insert r (A.erase p)
  have yn : y≠p := by rintro rfl; exact loopfree X.free (by omega) (ca.sub pa) yp
  have zn : z≠p := by rintro rfl; exact loopfree X.free (by omega) (ca.sub pa) pz
  have ys := mem_erase.mpr ⟨yn,ya⟩
  have zs := mem_erase.mpr ⟨zn,za⟩
  have rm : r∈M := mem_insert_self _ _
  have ym : y∈M := mem_insert_of_mem ys
  have zm : z∈M := mem_insert_of_mem zs
  have rnot : r∉A.erase p := by
    intro rmem
    exact (mem_erase.mp rmem).1 (card_le_one.mp (ca.heads y ya).le r (mem_outN.mpr ⟨mem_of_mem_erase rmem,yr⟩) p (mem_outN.mpr ⟨pa,yp⟩))
  have sub : M⊆X.V := insert_subset rv ((erase_subset _ _).trans ca.sub)
  have size : M.card=q+1 := by
    dsimp [M]; rw [card_insert_of_notMem rnot,card_erase_add_one pa,ca.size]
  have degree i (im : i∈M) : 1≤(outN X.D M i).card := by
    rcases mem_insert.mp im with rfl|is
    · exact card_pos.mpr ⟨z,mem_outN.mpr ⟨zm,rz⟩⟩
    obtain ⟨j,jm⟩ := card_pos.mp (show 0<(outN X.D A i).card by rw [ca.heads i (mem_of_mem_erase is)]; decide)
    obtain ⟨ja,ij⟩ := mem_outN.mp jm
    by_cases jp : j=p
    · subst j
      obtain rfl := card_le_one.mp (ca.incoming p pa).le i (mem_inN.mpr ⟨mem_of_mem_erase is,ij⟩) y (mem_inN.mpr ⟨ya,yp⟩)
      exact card_pos.mpr ⟨r,mem_outN.mpr ⟨rm,yr⟩⟩
    · exact card_pos.mpr ⟨j,mem_outN.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨jp,ja⟩),ij⟩⟩
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (X.free.mono_set sub) degree (by simpa using size)
  have cm : Cycle X.D X.V q M := ⟨sub,size,reg.1,reg.2⟩
  have bd (off : M∉F) : Boundary X F M := by
    obtain ⟨k,km⟩ := card_pos.mp (show 0<(outN X.D A z).card by rw [ca.heads z za]; decide)
    obtain ⟨ka,zk⟩ := mem_outN.mp km
    have kp : k≠p := by rintro rfl; exact digonfree X.free hq (ca.sub pa) (ca.sub za) pz zk
    exact ⟨mem_filter.mpr ⟨mem_powerset.mpr sub,cm⟩,off,A,af,z,mem_inter.mpr ⟨za,zm⟩,
      k,mem_inter.mpr ⟨ka,mem_insert_of_mem (mem_erase.mpr ⟨kp,ka⟩)⟩,zk⟩
  have fresh u v : (u,v)∈added X.D F M ↔
      (u=y ∧ v=r ∧ graph X.D F y r=false) ∨ (u=r ∧ v=z ∧ graph X.D F r z=false) := by
    constructor
    · intro m
      obtain ⟨um,vm,uv,miss⟩ := mem_added.mp m
      dsimp only at um vm uv miss
      rcases mem_insert.mp um with ur|us
      · subst u
        obtain rfl := card_le_one.mp (cm.heads r rm).le v (mem_outN.mpr ⟨vm,uv⟩) z (mem_outN.mpr ⟨zm,rz⟩)
        exact Or.inr ⟨rfl,rfl,miss⟩
      rcases mem_insert.mp vm with vr|vs
      · subst v
        obtain rfl := card_le_one.mp (cm.incoming r rm).le u (mem_inN.mpr ⟨um,uv⟩) y (mem_inN.mpr ⟨ym,yr⟩)
        exact Or.inl ⟨rfl,rfl,miss⟩
      · have old : graph X.D F u v=true := active.mpr ⟨A,mem_col.mpr ⟨af,mem_of_mem_erase us,mem_of_mem_erase vs,uv⟩⟩
        simp [miss] at old
    · rintro (⟨rfl,rfl,off⟩|⟨rfl,rfl,off⟩)
      · exact mem_added.mpr ⟨ym,rm,yr,off⟩
      · exact mem_added.mpr ⟨rm,zm,rz,off⟩
  refine ⟨cm,bd,fresh,?_⟩
  intro π old
  rw [Closure.SharedArcBudget.fits_iff cm old]
  constructor
  · intro fits
    exact ⟨fits y ym r rm yr,fits r rm z zm rz⟩
  · rintro ⟨inBill,outBill⟩ u um v vm ed miss
    rcases (fresh u v).mp (mem_added.mpr ⟨um,vm,ed,miss⟩) with ⟨rfl,rfl,off⟩ | ⟨rfl,rfl,off⟩
    · exact inBill off
    · exact outBill off

/-- Either the corridor is already selectable, or its two bills give a
boundary on the very same F. The number of missing halves bounds the
minimum number of targets. A failing old allocation names the unpaid half. -/
theorem original_bills {q n} (X : Model q n) (hq : 2≤q) {F : Family} {A L : Finset ℕ} {y p z r}
    (ca : Cycle X.D X.V q A) (af : A∈F) (pa : p∈A) (ya : y∈A) (za : z∈A)
    (yp : X.D y p=true) (pz : X.D p z=true) (rv : r∈X.V) (yr : X.D y r=true) (rz : X.D r z=true)
    (least : ∀M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (stuck : ∀M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (π : ℕ→ℝ) (old : RealDual q (graph X.D F) X.V 1 π) :
    insert r (A.erase p)∈F ∨
      ((targets X.D X.V F L).card ≤
        (if graph X.D F y r=true then 0 else 1)+(if graph X.D F r z=true then 0 else 1) ∧
        ((graph X.D F y r=false ∧ 1<realCol q (graph X.D F) X.V π r + q*π y) ∨
         (graph X.D F r z=false ∧ 1<realCol q (graph X.D F) X.V π z + q*π r))) := by
  classical
  let M := insert r (A.erase p)
  by_cases mf : M∈F
  · exact Or.inl mf
  right
  obtain ⟨cm,bd,fresh,bills⟩ := replacement X hq ca af pa ya za yp pz rv yr rz
  have bound := least M (bd mf)
  let I : Finset ℕ := if graph X.D F y r=true then ∅ else {r}
  let O : Finset ℕ := if graph X.D F r z=true then ∅ else {z}
  have cover : targets X.D X.V F M ⊆ I∪O := by
    intro j hit
    obtain ⟨_,jm,i,im,ij,off⟩ := mem_filter.mp hit
    rcases (fresh i j).mp (mem_added.mpr ⟨im,jm,ij,off⟩) with ⟨rfl,rfl,e⟩|⟨rfl,rfl,e⟩
    · exact mem_union_left _ (by simp [I,e])
    · exact mem_union_right _ (by simp [O,e])
  constructor
  · apply (bound.trans (card_le_card cover)).trans
    exact (card_union_le I O).trans (by cases e : graph X.D F y r <;> cases f : graph X.D F r z <;> simp [I,O,e,f])
  · by_contra! no
    apply stuck M (bd mf)
    apply smallRow_of_realDual ((bills π old).mpr ?_)
    exact ⟨fun m=>(no.1 m),fun m=>(no.2 m)⟩

#print axioms replacement
#print axioms original_bills
end LeanCH.BR.CorridorPayment

