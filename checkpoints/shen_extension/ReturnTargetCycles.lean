import checkpoints.shen_extension.ReturnTargetReach

namespace LeanCH.BR.Closure.ReturnTargetCycles
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity
open TwoParentReturnPivot ReturnSponsorMass FirstPacketBarrier MarkedCyclePeeling ShenCycleSuccessor

/-- Every neutral t-head specifies a native shortest cycle through the same
arc p→t. On each such cycle t has exactly one next vertex. -/
theorem supply {q n p t} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (pv : p∈X.V) (tv : t∈X.V) (pt : X.D p t=true) :
    let Z := outN X.D X.V t∩neutral X.D X.V p
    ∀z∈Z, ∃M∈col X.D (family X) (p,t),z∈outN X.D M t := by
  classical
  intro Z z hz
  obtain ⟨hit,neutralZ⟩ := mem_inter.mp hz
  obtain ⟨zv,tz⟩ := mem_outN.mp hit
  have off := (mem_filter.mp neutralZ).2.1
  obtain ⟨M,cm,pm,tm,zm⟩ := SaturatedCycleClasses.missing hq X.free X.sat pv tv zv pt tz (by simp [off])
  exact ⟨M,mem_col.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr cm.sub,cm⟩,pm,tm,pt⟩,mem_outN.mpr ⟨zm,tz⟩⟩

/-- Projection to the next head costs at most one label per cycle. -/
theorem slots {q n p t} (X : ShortestCycleWeights.Model q n) {F : Family} (sub : F⊆family X) :
    ((col X.D F (p,t)).biUnion (fun M=>outN X.D M t)).card≤(col X.D F (p,t)).card := by
  classical
  let C := col X.D F (p,t)
  calc
    _ ≤ ∑M∈C,(outN X.D M t).card := card_biUnion_le
    _ = ∑_M∈C,1 := sum_congr rfl (fun M h=>by
      obtain ⟨mf,_,tm,_⟩ := mem_col.mp h
      exact (mem_filter.mp (sub mf)).2.heads t tm)
    _ = C.card := by simp

theorem missing_arc {q n} (X : ShortestCycleWeights.Model q n) {F : Family} {M}
    (complete : ∀L,L∈F ↔ Cycle (graph X.D F) X.V q L)
    (cm : Cycle X.D X.V q M) (off : M∉F) :
    ∃u∈M,∃v∈M,X.D u v=true ∧ graph X.D F u v=false := by
  classical
  by_contra! keeps
  have eq {u v} (um : u∈M) (vm : v∈M) : graph X.D F u v=true ↔ X.D u v=true := by
    constructor
    · intro hit
      obtain ⟨A,ha⟩ := active.mp hit
      exact (mem_col.mp ha).2.2.2
    · intro uv
      exact Bool.eq_true_of_not_eq_false (keeps u um v vm uv)
  apply off
  apply (complete M).mpr
  refine ⟨cm.sub,cm.size,?_,?_⟩
  · intro u um
    have same : outN (graph X.D F) M u=outN X.D M u := by
      ext v
      simp only [mem_outN]
      exact and_congr_right (fun vm=>eq um vm)
    rw [same,cm.heads u um]
  · intro v vm
    change (inN (graph X.D F) M v).card=1
    have same : inN (graph X.D F) M v=inN X.D M v := by
      ext u
      simp only [mem_inN]
      exact and_congr_right (fun um=>eq um vm)
    rw [same]
    exact cm.incoming v vm

/-- A scarcity of selected cycles produces the actual neutral next vertex,
its full native shortest cycle, and an arc of that cycle lost by completion. -/
theorem native {q n b p t y w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (bv : b∈X.V) (pv : p∈X.V) (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (high : 1<c) (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1) {F : Family} (sub : F⊆family X)
    (complete : ∀L,L∈F ↔ Cycle (graph X.D F) X.V q L) :
    let U := X.V.erase b
    let B := bank q X.D U t y
    let S := B.filter (fun h=>X.D p h=true)
    let Z := outN X.D X.V t∩neutral X.D X.V p
    let C := col X.D F (p,t)
    (∃h∈outN X.D U p,h∈outN X.D U t \ B) ∨
    (q≤S.card+(col X.D (family X) (p,t)).card ∧
      (q≤S.card+C.card ∨
        ∃z∈Z, z∉C.biUnion (fun M=>outN X.D M t) ∧
          ∃M∈col X.D (family X) (p,t), z∈outN X.D M t ∧ M∉F ∧
            ∃u∈M,∃v∈M,X.D u v=true ∧ graph X.D F u v=false)) := by
  classical
  intro U B S Z C
  rcases ReturnTargetReach.at_parent pv (ReturnTargetReach.native (y:=y) X hq bv pv tr pt high rows diffuse)
    with kept|⟨count,_⟩
  · exact Or.inl kept
  right
  have zlow : q≤S.card+Z.card := by
    change q-S.card≤(Z∩ball X.D X.V p 2).card at count
    have sizes := card_le_card (inter_subset_left (s₁:=Z) (s₂:=ball X.D X.V p 2))
    omega
  have pick := supply X (by omega : 2≤q) pv (BRsub.ballSet_subset tr) pt
  have all : Z⊆(col X.D (family X) (p,t)).biUnion (fun M=>outN X.D M t) := by
    intro z hz
    obtain ⟨M,mc,zm⟩ := pick z hz
    exact mem_biUnion.mpr ⟨M,mc,zm⟩
  have upper := (card_le_card all).trans (slots X (F:=family X) (Subset.rfl))
  refine ⟨by omega,?_⟩
  by_cases enough : q≤S.card+C.card
  · exact Or.inl enough
  right
  have fail : ¬Z⊆C.biUnion (fun M=>outN X.D M t) := fun incl=>by
    have small : Z.card≤C.card := (card_le_card incl).trans (slots X sub)
    omega
  obtain ⟨z,hz,outside⟩ := not_subset.mp fail
  obtain ⟨M,mc,zm⟩ := pick z hz
  obtain ⟨mf,pm,tm,arc⟩ := mem_col.mp mc
  have dropped : M∉F := fun inf=>outside (mem_biUnion.mpr ⟨M,mem_col.mpr ⟨inf,pm,tm,arc⟩,zm⟩)
  exact ⟨z,hz,outside,M,mc,zm,dropped,missing_arc X complete (mem_filter.mp mf).2 dropped⟩

#print axioms supply
#print axioms slots
#print axioms native
end LeanCH.BR.Closure.ReturnTargetCycles
