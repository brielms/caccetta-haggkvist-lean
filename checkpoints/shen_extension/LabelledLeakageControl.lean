import checkpoints.shen_extension.LabelledLeakageCapacity

namespace LeanCH.BR.Closure.LabelledLeakageControl
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity

/-- Substitute the directed four-cycle on labels 0..3 for one vertex of a four-cycle. -/
def E (i j : ℕ) : Bool := decide (
  (i<4 ∧ (j=(i+1)%4 ∨ j=4)) ∨ (i=4 ∧ j=5) ∨ (i=5 ∧ j=6) ∨ (i=6 ∧ j<4))
def V := range 7
def w (i : ℕ) : ℚ := if i<4 then 1/16 else 1/4

private def layer (a : ℕ) : ℕ→Finset ℕ
  | 0 => {a}
  | k+1 => (layer a k).biUnion (outN E V)

private theorem layer_iff (a j k) : j∈layer a k ↔ Walk E V a j k := by
  induction k generalizing j with
  | zero =>
    constructor
    · intro h; have eq := mem_singleton.mp h; subst j; exact .refl a
    · intro path; cases path; exact mem_singleton_self _
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨i,hi,hj⟩ := mem_biUnion.mp h
      exact ((ih i).mp hi).snoc (mem_outN.mp hj).1 (mem_outN.mp hj).2
    · intro path
      obtain ⟨i,pre,jv,arc⟩ := path.unsnoc
      exact mem_biUnion.mpr ⟨i,(ih i).mpr pre,mem_outN.mpr ⟨jv,arc⟩⟩

theorem free : QFree E V 3 := by
  have check : ∀a∈V,∀k∈Icc 1 3,a∉layer a k := by decide +kernel
  intro a k one three path
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨_,_,av,_⟩ := path.unsnoc
    exact check a av _ (mem_Icc.mpr ⟨one,three⟩) ((layer_iff ..).mpr path)

theorem sat : BRsub.Sat 3 E V := by
  have check : ∀a∈V,∀j∈V,E j a≠true → ∃k∈range 3,j∈layer a k := by decide +kernel
  intro a av j jv missing
  obtain ⟨k,hk,walk⟩ := check a av j jv missing
  exact mem_ball.mpr ⟨jv,k,by have := mem_range.mp hk; omega,(layer_iff ..).mp walk⟩

theorem flat : mass V w=1 ∧ ∀ i∈V,0<w i ∧ WeightedSD.row 3 E V w i=1 ∧
    WeightedSD.col 3 E V w i=1 := by decide +kernel

theorem separated : ShenParentIntersection.Separated E V V ∧
    ShenParentIntersection.Separated (fun i j=>E j i) V V := by
  unfold ShenParentIntersection.Separated
  decide +kernel

private def supports : Finset (Finset ℕ) :=
  {{0},{1},{2},{3},{4},{5},{6},{0,1,2,3},{0,2,5},{0,4,5,6},{1,4,5,6},{2,4,5,6},{3,4,5,6}}

private def uniform (K : Finset ℕ) (i : ℕ) : ℚ := if i∈K then 1/(K.card:ℚ) else 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
private theorem certificates : ∀ U∈V.powerset,U.Nonempty → U≠V → ∃K∈supports,
    mass U (uniform K)=1 ∧ ∀j∈U,WeightedSD.col 3 E U (uniform K) j≤1 := by decide +kernel

theorem proper_small {U : Finset ℕ} (sub : U⊆V) (proper : U≠V) : SmallRow 3 E U := by
  by_cases live : U.Nonempty
  · obtain ⟨K,_,normalized,cols⟩ := certificates U (mem_powerset.mpr sub) live proper
    apply smallRow_of_realDual (p:=fun i=>(uniform K i : ℝ))
    refine ⟨fun i _=>?_,?_,fun i iv=>?_⟩
    · have nn : 0≤uniform K i := by unfold uniform; split_ifs <;> positivity
      exact_mod_cast nn
    · rw [realMass_rat,normalized]; norm_num
    · rw [realCol_rat]; exact_mod_cast cols i iv
  · exact fun _ _ hl=>(live hl).elim

private def carrier (a : ℕ) := V.filter (fun i=>i≠a ∧ E i a≠true)
private theorem eq_region {a} (av : a∈V) : region 3 E V a=carrier a := by
  ext i
  by_cases iv : i∈V
  · simpa [carrier,iv] using saturated_region (by decide) free sat av iv
  · have missing : i∉region 3 E V a := fun h=>iv (BRsub.ballSet_subset h)
    simp [carrier,iv,missing]

/-- Four different roots each force row 5, with 6 as its only exterior head. -/
theorem forced : ∀a∈range 4,
    let R := region 3 E V a
    1-mass R w=3/8 ∧ ((V\R).filter (fun j=>E 5 j=true))={6} ∧
    R.filter (fun i=>1-mass R w≤3*mass ((V\R).filter (fun j=>E i j=true)) w)={5} := by
  have check : ∀a∈range 4,
      let R := carrier a
      1-mass R w=3/8 ∧ ((V\R).filter (fun j=>E 5 j=true))={6} ∧
      R.filter (fun i=>1-mass R w≤3*mass ((V\R).filter (fun j=>E i j=true)) w)={5} := by decide +kernel
  intro a ha
  exact eq_region (mem_range.mpr (lt_trans (mem_range.mp ha) (by decide : 4<7))) ▸ check a ha

/-- With unit root coefficients the four forced demands exceed one copy of the physical arc flow. -/
theorem overloaded :
    (∑ a∈range 4,w 5*(1-mass (region 3 E V a) w))=3/8 ∧
      flow 3 E w w 5 6=3/16 ∧ (3/16:ℚ)<3/8 := by
  constructor
  · calc
      _ = ∑ _a∈range 4,w 5*(3/8) := sum_congr rfl (fun a ha=>congrArg (w 5 * ·) (forced a ha).1)
      _ = _ := by decide +kernel
  · decide +kernel

#print axioms free
#print axioms sat
#print axioms flat
#print axioms separated
#print axioms proper_small
#print axioms forced
#print axioms overloaded
end LeanCH.BR.Closure.LabelledLeakageControl
