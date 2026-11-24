import checkpoints.shen_extension.LastArcReturnMenu
import checkpoints.shen_extension.CycleSquareTensor

namespace LeanCH.BR.Closure.LastArcHeadDeposit
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier
open ShenCycleSuccessor

/-- Unnormalized deposit on a specified row, followed by normalization. -/
noncomputable def price (p : ℕ → ℝ) (v : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  (p i + if i=v then u else 0) / (1+u)

private theorem col_price {D : CH.Digraph} {q : ℕ} {V : Finset ℕ} {v : ℕ}
    (p : ℕ → ℝ) (vv : v∈V) (u : ℝ) (j : ℕ) :
    realCol q D V (price p v u) j =
      (realCol q D V p j + (if j=v then u else 0) + (q:ℝ)*(if D v j=true then u else 0)) / (1+u) := by
  classical
  have incoming : realInW D V (price p v u) j =
      (realInW D V p j + (if D v j=true then u else 0))/(1+u) := by
    unfold realInW
    rw [show (∑ i∈V, if D i j=true then price p v u i else 0) =
      ∑ i∈V, ((if D i j=true then p i else 0) +
        (if i=v then (if D v j=true then u else 0) else 0))/(1+u) by
          apply sum_congr rfl; intro i _
          by_cases h : i=v <;> by_cases arc : D i j=true <;> simp_all [price]]
    rw [←sum_div,sum_add_distrib]
    simp [vv]
  rw [realCol,incoming,price,←mul_div_assoc,←add_div,realCol]
  ring

/-- Exact price test for a fixed old dual in the one direction of the common
head. C bounds the original prices on all child columns and is attained.
Only outgoing heads of v need slack at the least possible deposit C-1. -/
theorem deposit_iff {D : CH.Digraph} {q : ℕ} {V : Finset ℕ} {v : ℕ}
    (hq : 1≤q) (vv : v∈V) (loop : D v v=false) (p : ℕ → ℝ)
    (pos : ∀i∈V,0≤p i) (norm : realMass V p=1) (self : realCol q D V p v≤1)
    {C : ℝ} (high : 1≤C) (cap : ∀j∈V, realCol q D V p j≤C)
    (attain : ∃j∈V, realCol q D V p j=C) :
    (∃u:ℝ, 0≤u ∧ RealDual q D V 1 (price p v u)) ↔
      ∀j∈V, D v j=true → realCol q D V p j+((q:ℝ)-1)*(C-1)≤1 := by
  classical
  have q1 : 0≤(q:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hq)
  constructor
  · rintro ⟨u,hu,pay⟩
    have den : 0<1+u := by linarith
    have bill (j) (hj : j∈V) := (div_le_iff₀ den).mp (col_price p vv u j ▸ pay.columns j hj)
    obtain ⟨k,km,eq⟩ := attain
    have lo : C-1 ≤ u := by
      have h := bill k km
      rw [eq] at h
      have a : (0:ℝ)≤(if k=v then u else 0) := by split_ifs <;> positivity
      have b : (0:ℝ)≤(q:ℝ)*(if D v k=true then u else 0) :=
        mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> positivity)
      linarith
    intro j jm edge
    have ne : j≠v := by rintro rfl; simp [loop] at edge
    have h := bill j jm
    simp [edge,ne] at h
    have m := mul_le_mul_of_nonneg_left lo q1
    linarith
  · intro slack
    let u := C-1
    have hu : 0≤u := sub_nonneg.mpr high
    have den : 0<1+u := by linarith
    refine ⟨u,hu,?_,?_,?_⟩
    · intro i im
      exact div_nonneg (add_nonneg (pos i im) (by split_ifs <;> positivity)) den.le
    · simp only [realMass,price,←sum_div,sum_add_distrib]
      simp [vv,show ∑ i∈V,p i=1 from norm,ne_of_gt den]
    · intro j jm
      rw [col_price p vv u j,div_le_iff₀ den]
      by_cases eq : j=v
      · subst j; simp [loop]; linarith
      · by_cases arc : D v j=true
        · have b := slack j jm arc
          simp [eq,arc]; dsimp [u]; linarith
        · simp [eq,arc]; dsimp [u]; linarith [cap j jm]

/-- If the alternative cycle still fails, every old dual has both an unpaid
new column and a labelled old head of v blocking the least deposit. -/
theorem at_original {q n F L v} (X : Model q n) (hq : 2≤q)
    (cy : Cycle X.D X.V q L) (vv : v∈X.V) (outside : v∉L)
    (bad : ¬SmallRow q (graph X.D (insert L F)) X.V)
    (p : ℕ→ℝ) (hp : RealDual q (graph X.D F) X.V 1 p) :
    let val := realCol q (graph X.D (insert L F)) X.V p
    ∃ b ∈ SharedArcBarrier.targets X.D X.V F L, 1 < val b ∧
      (∀ k ∈ X.V, val k ≤ val b) ∧
      ∃ j ∈ X.V, graph X.D F v j=true ∧ 1 < val j + ((q:ℝ)-1)*(val b-1) := by
  classical
  intro val
  let G := graph X.D (insert L F)
  obtain ⟨b,bv,top⟩ := X.V.exists_max_image val X.live
  have high : 1<val b := by
    by_contra! low
    exact bad (smallRow_of_realDual (p:=p) ⟨hp.nonneg,hp.normalized,fun k kv=>(top k kv).trans low⟩)
  have target : b∈SharedArcBarrier.targets X.D X.V F L := by
    by_contra no
    have same := (SharedArcBarrier.column (q:=q) (F:=F) cy p bv).1 no
    exact high.not_ge (same.le.trans (hp.columns b bv))
  have noV : v∉SharedArcBarrier.targets X.D X.V F L := fun m=>outside (mem_filter.mp m).2.1
  have self := (SharedArcBarrier.column (q:=q) (F:=F) cy p vv).1 noV
  have loop : G v v=false := by
    apply Bool.eq_false_iff.mpr
    exact fun h=>loopfree X.free (by omega) vv (CrossValueOmissions.selected_sub h)
  have test := deposit_iff (D:=G) (by omega : 1≤q) vv loop p hp.nonneg hp.normalized
    (self.symm ▸ hp.columns v vv) high.le top ⟨b,bv,rfl⟩
  refine ⟨b,target,high,top,?_⟩
  by_contra! enough
  apply bad
  obtain ⟨u,_,paid⟩ := test.mpr (by
    intro j jm edge
    rcases SharedArcComponentExchange.union_arc.mp edge with old|fresh
    · exact enough j jm old
    · exact (outside (SharedArcComponentExchange.mem_added.mp fresh).1).elim)
  exact smallRow_of_realDual paid

/-- In the merged orientation, a blocking old head on the alternative
cycle must be the successor of t. Every other possible blocker is outside
the cycle and keeps its original column value. -/
theorem blocker_location {q n F L v r t j} (X : Model q n) (hq : 2≤q)
    (cy : Cycle X.D X.V q L) (vv : v∈X.V) (outside : v∉L)
    (rm : r∈L) (tm : t∈L) (pivot : X.D r t=true)
    (rv : X.D r v=true) (tv : X.D t v=true)
    (jm : j∈X.V) (edge : graph X.D F v j=true) (p : ℕ→ℝ) :
    (j∉L ∧ realCol q (graph X.D (insert L F)) X.V p j = realCol q (graph X.D F) X.V p j) ∨
    (j∈L ∧ X.D t j=true ∧ outN X.D L v={j} ∧ Cycle X.D X.V q (insert v (L.erase t))) := by
  classical
  by_cases jl : j∈L
  · right
    have rt : r≠t := by rintro rfl; exact loopfree X.free (by omega) (cy.sub rm) pivot
    have rich : 2≤(inN X.D L v).card :=
      (show ({r,t}:Finset ℕ).card=2 by simp [rt]) ▸ card_le_card
        (show ({r,t}:Finset ℕ)⊆inN X.D L v from insert_subset
          (mem_inN.mpr ⟨rm,rv⟩) (singleton_subset_iff.mpr (mem_inN.mpr ⟨tm,tv⟩)))
    obtain ⟨a,u,N,shift,cn,parents,only⟩ := CycleSquareTensor.replacement hq X.free cy
      (mem_sdiff.mpr ⟨vv,outside⟩) rich jl (CrossValueOmissions.selected_sub edge)
    have cases' {k} (h : k∈inN X.D L v) : k=a ∨ k=u := by
      rw [parents] at h; simpa only [mem_insert,mem_singleton] using h
    have tu : t=u := by
      rcases cases' (mem_inN.mpr ⟨tm,tv⟩) with h|h
      · rcases cases' (mem_inN.mpr ⟨rm,rv⟩) with h'|h'
        · exact (rt (h'.trans h.symm)).elim
        · have tr : X.D t r=true := by simpa only [h,h'] using shift.before₁
          exact (X.free r 2 (by omega) (by omega)
            (.step (cy.sub tm) pivot (.step (cy.sub rm) tr (.refl r)))).elim
      · exact h
    exact ⟨jl,tu ▸ shift.before₂,only,by simpa only [shift.labels,tu] using cn⟩
  · exact Or.inl ⟨jl,(SharedArcBarrier.column (q:=q) (F:=F) cy p jm).1
        (fun m=>jl (mem_filter.mp m).2.1)⟩

def OnFamily {q n} (X : Model q n) (F : MarkedCyclePeeling.Family) : Prop :=
  ∀ L v r t, Cycle X.D X.V q L → v∈X.V → v∉L → r∈L → t∈L →
    X.D r t=true → X.D r v=true → X.D t v=true →
    ¬SmallRow q (graph X.D (insert L F)) X.V →
    ∀ p : ℕ→ℝ, RealDual q (graph X.D F) X.V 1 p →
    let val := realCol q (graph X.D (insert L F)) X.V p
    ∃ b ∈ SharedArcBarrier.targets X.D X.V F L, 1<val b ∧ (∀k∈X.V,val k≤val b) ∧
      ∃ j ∈ X.V, graph X.D F v j=true ∧ 1<val j+((q:ℝ)-1)*(val b-1) ∧
        ((j∉L ∧ val j=realCol q (graph X.D F) X.V p j) ∨
         (j∈L ∧ X.D t j=true ∧ outN X.D L v={j} ∧ Cycle X.D X.V q (insert v (L.erase t))))

theorem on_model {q n} (X : Model q n) (hq : 2≤q) : ∀ F, OnFamily X F := by
  intro F L v r t cy vv outside rm tm rt rv tv bad p hp
  obtain ⟨b,bm,high,top,j,jm,edge,bill⟩ := at_original X hq cy vv outside bad p hp
  exact ⟨b,bm,high,top,j,jm,edge,bill,blocker_location X hq cy vv outside rm tm rt rv tv jm edge p⟩

#print axioms deposit_iff
#print axioms at_original
#print axioms blocker_location
#print axioms on_model
end LeanCH.BR.Closure.LastArcHeadDeposit
