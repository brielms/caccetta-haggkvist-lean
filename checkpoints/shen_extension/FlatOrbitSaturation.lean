import checkpoints.shen_extension.FlatExchangeTriangle

namespace LeanCH.BR.Closure.FlatOrbitSaturation
open Finset Function BRq2 BRq3 BR45 PairedFamilyLoop RawRepairAlternative
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

/-- A missing arc for which the selected graph does not supply the short reverse walk. -/
def Defect (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (u v : ℕ) : Prop :=
  E u v=false ∧ u∉ball E V v (q-1)

private theorem hit {q E V L u v} (sat : BRsub.Sat q E (V\L))
    (uv : u∈V) (vv : v∈V) (bad : Defect q E V u v) : u∈L ∨ v∈L := by
  by_contra! h
  have back := sat v (mem_sdiff.mpr ⟨vv,h.2⟩) u (mem_sdiff.mpr ⟨uv,h.1⟩) (by simp [bad.1])
  obtain ⟨_,l,le,w⟩ := mem_ball.mp back
  exact bad.2 (mem_ball.mpr ⟨uv,l,le,w.mono sdiff_subset⟩)

private theorem separate {F} {s t : PairedFamilyLoop.State F} (join : previous t=current s) :
    Disjoint (gone s) (gone t) := by
  apply disjoint_left.mpr
  intro i a b
  exact (mem_sdiff.mp a).2 (join ▸ (mem_sdiff.mp b).1)

/-- The labelled endpoints of one missing return alternate at every step.
The same labels work simultaneously on all recurrent orbits. -/
theorem alternating {F q E V u v} (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (sat : ∀a : periodicPts go,BRsub.Sat q E (V\gone a.val))
    (uv : u∈V) (vv : v∈V) (bad : Defect q E V u v) (a : periodicPts go) :
    (u∈gone a.val ↔ v∉gone a.val) ∧
    (u∈gone (go a.val) ↔ u∉gone a.val) ∧
    (u∈previous a.val ↔ u∈gone a.val) ∧ (u∈current a.val ↔ u∉gone a.val) ∧
    (v∈previous a.val ↔ v∈gone a.val) ∧ (v∈current a.val ↔ v∉gone a.val) := by
  let b := CycleSlotOrbit.base go a
  have now := hit (sat a) uv vv bad
  have later : u∈gone (go a.val) ∨ v∈gone (go a.val) := hit (sat b) uv vv bad
  have dis := disjoint_left.mp (separate (join a.val))
  obtain ⟨z,hz⟩ := (CycleSlotOrbit.base go).surjective a
  have step : go z.val=a.val := congrArg Subtype.val hz
  have prevHit := hit (sat z) uv vv bad
  have prevJoin : current z.val=previous a.val := (join z.val).symm.trans (congrArg previous step)
  have row (i) (hi : i∈gone a.val) : i∈previous a.val ∧ i∉current a.val := mem_sdiff.mp hi
  have prevRow (i) (hi : i∈gone z.val) : i∉previous a.val := prevJoin ▸ (mem_sdiff.mp hi).2
  have nextRow (i) (hi : i∈gone (go a.val)) : i∈current a.val := join a.val ▸ (mem_sdiff.mp hi).1
  rcases now with hu|hv
  · have hvl : v∈gone (go a.val) := later.resolve_left (fun x => dis hu x)
    have hv : v∉gone a.val := fun x => dis x hvl
    have hvz : v∈gone z.val := prevHit.resolve_left (fun x => prevRow _ x (row _ hu).1)
    simp [hu,hv,show u∉gone (go a.val) from fun x => dis hu x,(row _ hu).1,(row _ hu).2,
      prevRow _ hvz,nextRow _ hvl]
  · have hul : u∈gone (go a.val) := later.resolve_right (fun x => dis hv x)
    have hu : u∉gone a.val := fun x => dis x hul
    have huz : u∈gone z.val := prevHit.resolve_right (fun x => prevRow _ x (row _ hv).1)
    simp [hu,hv,hul,(row _ hv).1,(row _ hv).2,prevRow _ huz,nextRow _ hul]

private theorem even_return {α : Type*} (step : α→α) (p : α→Prop)
    (flip : ∀z,p (step z) ↔ ¬p z) (z : α) {k} (ret : step^[k] z=z) : Even k := by
  classical
  have iter (n : ℕ) : p (step^[n] z) ↔ (if Even n then p z else ¬p z) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply',flip,ih]
      by_cases e : Even n <;> simp [Nat.even_add_one,e]
  by_contra no
  have bad := iter k
  simp [ret,no] at bad

theorem defect_period {F q E V u v} (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (sat : ∀a : periodicPts go,BRsub.Sat q E (V\gone a.val))
    (uv : u∈V) (vv : v∈V) (bad : Defect q E V u v) (a : periodicPts go) :
    Even (minimalPeriod go a.val) := by
  let step := CycleSlotOrbit.base go
  have val (k : ℕ) : ((step^[k] a).val)=go^[k] a.val := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iterate_succ_apply',iterate_succ_apply']
      exact (show (step (step^[k] a)).val=go (step^[k] a).val from rfl).trans (congrArg go ih)
  apply even_return step (fun z => u∈gone z.val) (fun z => (alternating go join sat uv vv bad z).2.1) a
  exact Subtype.ext ((val _).trans (isPeriodicPt_minimalPeriod go a.val))

theorem odd_saturated {F q E V} (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (sat : ∀a : periodicPts go,BRsub.Sat q E (V\gone a.val))
    (a : periodicPts go) (odd : ¬Even (minimalPeriod go a.val)) : BRsub.Sat q E V := by
  intro v vv u uv miss
  by_contra no
  exact odd (defect_period go join sat uv vv ⟨Bool.eq_false_iff.mpr miss,no⟩ a)

theorem native_defect {q n} (X : Model q n) (hq : 1≤q) {F : Family}
    {U u v} (sub : U⊆X.V) (vv : v∈U) (arc : X.D u v=true) (miss : graph X.D F u v=false) :
    Defect q (graph X.D F) U u v := by
  refine ⟨miss,?_⟩
  intro back
  obtain ⟨_,k,le,w⟩ := mem_ball.mp back
  have lift {i j l} (p : Walk (graph X.D F) U i j l) : Walk X.D X.V i j l := by
    induction p with
    | refl => exact .refl _
    | step hv e _ ih =>
      obtain ⟨C,used⟩ := active.mp e
      exact .step (sub hv) (mem_col.mp used).2.2.2 ih
  exact X.free u (k+1) (by omega) (by omega) (.step (sub vv) arc (lift w))

theorem child_eq {q n} (X : Model q n) (hq : 1≤q) {F : Family}
    {U} (sub : U⊆X.V) (sat : BRsub.Sat q (graph X.D F) U) {u v} (uv : u∈U) (vv : v∈U) :
    graph X.D F u v=X.D u v := by
  cases h : graph X.D F u v with
  | true =>
    obtain ⟨C,used⟩ := active.mp h
    exact (mem_col.mp used).2.2.2.symm
  | false =>
    apply Eq.symm
    apply Bool.eq_false_iff.mpr
    intro arc
    exact (native_defect X hq sub vv arc h).2 (sat v vv u uv (by simp [h]))

theorem source_eq {q n} (X : Model q n) (hq : 1≤q) {F : Family}
    (sat : BRsub.Sat q (graph X.D F) X.V) {u v} (uv : u∈X.V) (vv : v∈X.V) :
    graph X.D F u v=X.D u v := child_eq X hq Subset.rfl sat uv vv

#print axioms alternating
#print axioms defect_period
#print axioms odd_saturated
#print axioms source_eq

/-- A single uncovered native arc forces the same two labels to switch sides
at every recurrent step. If the selected graph is already saturated, it is
exactly the source on the active labels. -/
theorem frontier {q n} (X : Model q n) (hq : 1≤q) {F : Family}
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (sat : ∀a : periodicPts go,BRsub.Sat q (graph X.D F) (X.V\gone a.val)) :
    let E := graph X.D F
    (BRsub.Sat q E X.V ∧ ∀u∈X.V,∀v∈X.V,E u v=X.D u v) ∨
      ∃ u∈X.V,∃ v∈X.V,X.D u v=true ∧ E u v=false ∧
        ∀a : periodicPts go,Even (minimalPeriod go a.val) ∧
          (u∈previous a.val ↔ v∉previous a.val) ∧
          (u∈current a.val ↔ u∉previous a.val) ∧ (v∈current a.val ↔ v∉previous a.val) := by
  classical
  intro E
  by_cases full : BRsub.Sat q E X.V
  · exact Or.inl ⟨full,fun _ hu _ hv => source_eq X hq full hu hv⟩
  right
  have find : ∃u∈X.V,∃v∈X.V,X.D u v=true ∧ E u v=false := by
    by_contra! no
    apply full
    intro v vv u uv miss
    have lift {i j k} (w : Walk X.D X.V i j k) (iv : i∈X.V) : Walk E X.V i j k := by
      induction w with
      | refl => exact .refl _
      | step hv arc _ ih => exact .step hv (by simpa using no _ iv _ hv arc) (ih hv)
    obtain ⟨_,k,le,w⟩ := mem_ball.mp (X.sat v vv u uv (fun arc => miss (by simpa using no _ uv _ vv arc)))
    exact mem_ball.mpr ⟨uv,k,le,lift w vv⟩
  obtain ⟨u,uv,v,vv,arc,miss⟩ := find
  have no := native_defect X hq Subset.rfl vv arc miss
  refine ⟨u,uv,v,vv,arc,miss,fun a => ?_⟩
  obtain ⟨opp,_,up,uc,vp,vc⟩ := alternating go join sat uv vv no a
  exact ⟨defect_period go join sat uv vv no a,up.trans (opp.trans (not_congr vp.symm)),
    uc.trans (not_congr up.symm),vc.trans (not_congr vp.symm)⟩

open WeightedSD ShenCycleSuccessor

/-- The sum of the possible successor weights for an arc of a flat child.
Every successor in this sum extends the very same arc to a shortest cycle
avoiding the omitted labels. -/
theorem successor_mass {q E U z} (hq : 2≤q) (free : QFree E U q) (sat : BRsub.Sat q E U)
    (zp : ∀i∈U,0<z i) (row : ∀i∈U,realRow q E U z i=1) {u v}
    (uv : u∈U) (vv : v∈U) (arc : E u v=true) :
    let H := outN E U v \ outN E U u
    z u + ((q:ℝ)-1)*z v ≤ q*realMass H z ∧ H.Nonempty ∧
      ∀w∈H,∃M,Cycle E U q M ∧ u∈M ∧ v∈M ∧ w∈M := by
  classical
  intro H
  let A := outN E U u
  let B := outN E U v
  have qpos : 1≤(q:ℝ) := by exact_mod_cast (by omega : 1≤q)
  have self : v∉B := fun h => loopfree free (by omega) vv (mem_outN.mp h).2
  have vrest : v∈A\B := mem_sdiff.mpr ⟨mem_outN.mpr ⟨vv,arc⟩,self⟩
  have lower : z v≤∑i∈A\B,z i := single_le_sum (fun i hi => (zp _ (mem_outN.mp (mem_sdiff.mp hi).1).1).le) vrest
  have split (C D : Finset ℕ) : (∑i∈C\D,z i)+(∑i∈C∩D,z i)=∑i∈C,z i := by
    rw [←sum_union (by apply disjoint_left.mpr; intro i h₁ h₂; exact (mem_sdiff.mp h₁).2 (mem_inter.mp h₂).2)]
    congr 1
    ext i
    simp only [mem_sdiff,mem_union,mem_inter]; tauto
  have sa := split A B
  have sb := split B A
  rw [inter_comm B A] at sb
  have ru := row u uv
  have rv := row v vv
  have form (i) : realOutW E U z i=∑j∈outN E U i,z j := by simp only [realOutW,outN,sum_filter]
  simp only [realRow,form] at ru rv
  change z u+q*(∑i∈A,z i)=1 at ru
  change z v+q*(∑i∈B,z i)=1 at rv
  have low : z u+((q:ℝ)-1)*z v≤q*realMass H z := by
    change _ ≤ (q:ℝ)*(∑i∈B\A,z i)
    rw [←sa] at ru
    rw [←sb] at rv
    nlinarith [mul_le_mul_of_nonneg_left lower (by linarith : 0≤(q:ℝ))]
  refine ⟨low,?_,?_⟩
  · by_contra! h
    rw [h] at low
    simp only [realMass,sum_empty,mul_zero] at low
    nlinarith [zp u uv,mul_nonneg (sub_nonneg.mpr qpos) (zp v vv).le]
  · intro w wh
    obtain ⟨vb,ua⟩ := mem_sdiff.mp wh
    obtain ⟨wv,edge⟩ := mem_outN.mp vb
    exact SaturatedCycleClasses.missing hq free sat uv vv wv arc edge (fun e => ua (mem_outN.mpr ⟨wv,e⟩))

#print axioms frontier
#print axioms successor_mass

/-- Every cycle on the actual schedule is a bipartition of the missing
native arcs. A label with the same membership on successive cycles has a
complete native row and column. -/
theorem phase_cut {q n} (X : Model q n) (hq : 1≤q) {F : Family}
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (sat : ∀a : periodicPts go,BRsub.Sat q (graph X.D F) (X.V\gone a.val))
    (a : periodicPts go) {u v} (uv : u∈X.V) (vv : v∈X.V)
    (arc : X.D u v=true) (miss : graph X.D F u v=false) :
    (u∈previous a.val ↔ v∉previous a.val) ∧ (u∈current a.val ↔ v∉current a.val) ∧
    (u∈current a.val ↔ u∉previous a.val) ∧ (v∈current a.val ↔ v∉previous a.val) := by
  obtain ⟨opp,_,up,uc,vp,vc⟩ := alternating go join sat uv vv (native_defect X hq Subset.rfl vv arc miss) a
  tauto

theorem stable_label {q n} (X : Model q n) (hq : 1≤q) {F : Family}
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (sat : ∀a : periodicPts go,BRsub.Sat q (graph X.D F) (X.V\gone a.val))
    (a : periodicPts go) {u} (uv : u∈X.V) (fixed : u∈previous a.val ↔ u∈current a.val) :
    ∀v∈X.V,graph X.D F u v=X.D u v ∧ graph X.D F v u=X.D v u := by
  intro v vv
  have enough (i j) (iv : i∈X.V) (jv : j∈X.V) (ij : i=u ∨ j=u) : graph X.D F i j=X.D i j := by
    cases e : graph X.D F i j with
    | true =>
      obtain ⟨C,used⟩ := active.mp e
      exact (mem_col.mp used).2.2.2.symm
    | false =>
      apply Eq.symm
      apply Bool.eq_false_iff.mpr
      intro arc
      obtain ⟨_,_,h,k⟩ := phase_cut X hq go join sat a iv jv arc e
      rcases ij with rfl|rfl <;> tauto
  exact ⟨enough _ _ uv vv (Or.inl rfl),enough _ _ vv uv (Or.inr rfl)⟩

/-- Native arcs retained by a child have a positive total weight of
extensions, each on an actual shortest cycle entirely inside that child. -/
theorem native_extensions {q n} (X : Model q n) (hq : 2≤q) {F : Family} {U z}
    (sub : U⊆X.V) (sat : BRsub.Sat q (graph X.D F) U)
    (zp : ∀i∈U,0<z i) (row : ∀i∈U,realRow q (graph X.D F) U z i=1) {u v}
    (uv : u∈U) (vv : v∈U) (arc : X.D u v=true) :
    let E := graph X.D F
    let H := outN E U v \ outN E U u
    z u + ((q:ℝ)-1)*z v ≤ q*realMass H z ∧ H.Nonempty ∧
      ∀w∈H,∃M,Cycle E U q M ∧ u∈M ∧ v∈M ∧ w∈M := by
  apply successor_mass hq ((PrivateArcEndpoints.graph_free X F).mono_set sub) sat zp row uv vv
  exact (child_eq X (by omega) sub sat uv vv).trans arc

#print axioms phase_cut
#print axioms stable_label
#print axioms native_extensions

end LeanCH.BR.Closure.FlatOrbitSaturation

