import checkpoints.shen_extension.TriangleIntervalResponse
import checkpoints.shen_extension.SingleArcReturnProfile
import checkpoints.shen_extension.SharedArcPivotGate

namespace LeanCH.BR.Closure.SingleArcNeighbourWitness
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open IntervalArcRecurrence

/-- The actual graph table in cyclic coordinates. Multiplication by -q
modulo qr+1 takes the original steps 1,...,r to 1,1+q,...,1+(r-1)q. -/
def IntervalTable {V : Finset ℕ} (E : CH.Digraph) (q r : ℕ) (e : ZMod (q*r+1) ≃ V) : Prop :=
  ∀ (i : ℕ) (j : V), (if E (e i) j then 1 else 0 : ℕ) =
    ((range r).filter (fun s => e ((i+1+q*s : ℕ) : ZMod (q*r+1))=j)).card

/-- Scalar sign at every nonzero cyclic displacement. -/
def SignLaw (q n : ℕ) : Prop := ∀ g : ℕ→ℝ, Function.Periodic g n → Equation q n g →
  ∀t, 0<t → t<n → 1+(g t-g 0)+(g (n-t)-g 0)<0

/-- The negative entry is in the actual old-successor by old-predecessor
rectangle. The assertion also covers edits that create a short cycle. -/
theorem witness_of_sign {V : Finset ℕ} (E : CH.Digraph) {q r : ℕ} (hq : 2≤q) (hr : 0<r)
    (sign : SignLaw q (q*r+1))
    (e : ZMod (q*r+1) ≃ V) (table : IntervalTable E q r e)
    (a b : V) (off : E a b=false) (u : ℝ) (up : 0<u) :
    ∃ v k : V, E a v=true ∧ E k b=true ∧
      SharedArcFlatResponse.test (realMatrix q E V)⁻¹ (fun _ => u) (fun _ => u) q a b v k < 0 := by
  classical
  let n := q*r+1
  let lab (i : ℕ) := e ((i:ℕ):ZMod (q*r+1))
  let R := realMatrix q E V
  have rows : Rows q r lab R := by
    apply of_entries
    · intro i; simp [lab,Nat.cast_add]
    · intro i t
      change e _=e _ ↔ _
      rw [e.injective.eq_iff,Nat.cast_add,add_eq_left,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
    · intro i j
      dsimp only [R]
      rw [realMatrix_entry]
      simp only [sum_boole]
      have count : ((range r).filter (fun s => lab (i+1+q*s)=j)).card =
          (if E (lab i) j then 1 else 0 : ℕ) := (table i j).symm
      rw [count]
      by_cases ed : E (lab i) j=true <;> simp [ed]
  have succEdge (i : ℕ) : E (lab i) (lab (i+1))=true := by
    have h := table i (lab (i+1))
    have hit : 0∈(range r).filter (fun s => lab (i+1+q*s)=lab (i+1)) :=
      mem_filter.mpr ⟨mem_range.mpr hr,by simp⟩
    have positive := card_pos.mpr ⟨_,hit⟩
    by_contra bad
    change ¬E (e i) (lab (i+1))=true at bad
    rw [ite_eq_right bad] at h
    exact positive.ne' h.symm
  let base := (e.symm a).val
  let diff := e.symm b-e.symm a-1
  let t := diff.val
  have la : lab base=a := by simp [lab,base]
  have lb : lab (base+t+1)=b := by
    simp [lab,base,t,diff,Nat.cast_add]
    convert e.apply_symm_apply b using 2; abel
  have pos : 0<t := by
    by_contra! ht
    have zero : t=0 := by omega
    have edge := succEdge base
    rw [zero,Nat.add_zero] at lb
    rw [la,lb] at edge
    exact Bool.noConfusion (off.symm.trans edge)
  have bound : t<n := diff.val_lt
  have inv := Matrix.mul_nonsing_inv R (SharedArcFlatResponse.matrix_unit hq E V)
  let g := column q lab R⁻¹ 0
  have law := column_equation rows inv 0
  have score := (score_eq hq rows inv g law.1 law.2 base t bound.le).trans_lt
    (sign g law.1 law.2 t pos bound)
  rw [la,lb] at score
  refine ⟨lab (base+1),lab (base+t),la ▸ succEdge base,lb ▸ succEdge (base+t),?_⟩
  convert mul_neg_of_pos_of_neg (mul_pos up up) score using 1
  dsimp [SharedArcFlatResponse.test,R]; ring

private theorem degrees {V : Finset ℕ} {E : CH.Digraph} {q r : ℕ}
    {e : ZMod (q*r+1) ≃ V} (table : IntervalTable E q r e) (j : V) :
    (outN E V j).card=r ∧ (inN E V j).card=r := by
  classical
  have indicator (i : ZMod (q*r+1)) (j : V) :
      (if E (e i) j then 1 else 0 : ℕ) =
        ∑ s ∈ range r, (if e (i+1+(q:ZMod (q*r+1))*(s:ZMod (q*r+1)))=j then 1 else 0) := by
    simpa [sum_boole] using table i.val j
  have count (f : ℕ → Bool) : (V.filter (fun j => f j=true)).card =
      ∑ j : V, (if f j then 1 else 0 : ℕ) := by
    rw [sum_coe_sort V (fun i => if f i then (1:ℕ) else 0)]; simp
  constructor
  · rw [outN,count]
    conv_lhs => enter [2,k]; rw [←e.apply_symm_apply j,indicator]
    rw [sum_comm]; simp
  · rw [inN,count,←Equiv.sum_comp e (fun i : V => if E i j then (1:ℕ) else 0)]
    simp_rw [indicator]
    rw [sum_comm]
    have one (s : ℕ) :
        (∑ i : ZMod (q*r+1), if e (i+1+(q:ZMod (q*r+1))*(s:ZMod (q*r+1)))=j then (1:ℕ) else 0)=1 := by
      let f := fun i : ZMod (q*r+1) => if e i=j then (1:ℕ) else 0
      have trans := Equiv.sum_comp (Equiv.addRight (1+(q:ZMod (q*r+1))*(s:ZMod (q*r+1)))) f
      simpa [f,←add_assoc,←e.eq_symm_apply] using trans
    simp [one]

theorem progress_of_sign {q n} (X : Model q n) (hq : 2≤q) (F : Family) (B : Finset ℕ)
    (H : Matrix X.V X.V ℝ) (p : ℕ→ℚ) (c : ℚ) {r : ℕ} (hr : 0<r)
    (sign : SignLaw q (q*r+1)) (e : ZMod (q*r+1) ≃ X.V) (table : IntervalTable (graph X.D F) q r e)
    (f : SharedArcFlatCut.Missing X F) : SharedArcPivotGate.ProgressAt X F B H p c := by
  have size : X.V.card=q*r+1 := by simpa only [Fintype.card_coe,ZMod.card] using Fintype.card_congr e.symm
  let u : ℚ := 1/(X.V.card:ℚ)
  have vn : (X.V.card:ℚ)≠0 := by exact_mod_cast X.live.card_pos.ne'
  have up : 0<u := by change 0<1/(X.V.card:ℚ); positivity
  have unit : (X.V.card:ℚ)*u=1 := by dsimp [u]; field_simp
  have sz : (X.V.card:ℚ)= (q:ℚ)*(r:ℚ)+1 := by exact_mod_cast size
  have law : u+(q:ℚ)*((r:ℚ)*u)=1 := by rw [sz] at unit; linear_combination unit
  have neg := witness_of_sign (graph X.D F) hq hr sign e table f.val.1 f.val.2 f.property.2
    (u:ℝ) (by exact_mod_cast up)
  obtain ⟨v,k,_,_,hit⟩ := neg
  apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inr
  refine ⟨fun _ => u,fun _ => u,fun _ _ => ⟨up,up⟩,?_,?_,?_,f,v,k,hit⟩
  · simpa [mass] using unit
  · intro i hi
    change u+(q:ℚ)*(∑j∈X.V,if graph X.D F i j=true then u else 0)=1
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    change u+(q:ℚ)*(((outN (graph X.D F) X.V i).card:ℚ)*u)=1
    rw [(degrees table ⟨i,hi⟩).1]; exact law
  · intro i hi
    change u+(q:ℚ)*(∑j∈X.V,if graph X.D F j i=true then u else 0)=1
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    change u+(q:ℚ)*(((inN (graph X.D F) X.V i).card:ℚ)*u)=1
    rw [(degrees table ⟨i,hi⟩).2]; exact law

/-- Unconditional triangle-cutoff result on the interval arc table in every degree. -/
theorem interval_witness {V : Finset ℕ} (E : CH.Digraph) {r : ℕ} (hr : 0<r)
    (e : ZMod (3*r+1) ≃ V) (table : IntervalTable E 3 r e) (a b : V) (off : E a b=false)
    (u : ℝ) (up : 0<u) :
    ∃ v k : V, E a v=true ∧ E k b=true ∧
      SharedArcFlatResponse.test (realMatrix 3 E V)⁻¹ (fun _=>u) (fun _=>u) 3 a b v k < 0 :=
  witness_of_sign E (by decide) hr (TriangleIntervalResponse.sign hr) e table a b off u up

theorem progress {q n} (X : Model q n) (three : q=3) (F : Family) (B : Finset ℕ)
    (H : Matrix X.V X.V ℝ) (p : ℕ→ℚ) (c : ℚ) {r : ℕ} (hr : 0<r)
    (e : ZMod (q*r+1) ≃ X.V) (table : IntervalTable (graph X.D F) q r e)
    (f : SharedArcFlatCut.Missing X F) : SharedArcPivotGate.ProgressAt X F B H p c := by
  subst q
  exact progress_of_sign X (by decide) F B H p c hr (TriangleIntervalResponse.sign hr) e table f

/-- A stopped boundary already supplies a missing native arc. At cutoff
three this excludes every interval table from the remaining capstone state. -/
theorem excluded {q n} (X : Model q n) (three : q=3) {F : Family} {B : Finset ℕ}
    (step : SharedArcBarrier.Boundary X F B) (good : SmallRow q (graph X.D F) X.V)
    (stop : ∀M, SharedArcBarrier.Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {H : Matrix X.V X.V ℝ} {p : ℕ→ℚ} {c : ℚ} (blocked : ¬SharedArcPivotGate.ProgressAt X F B H p c)
    {r : ℕ} (hr : 0<r) (e : ZMod (q*r+1) ≃ X.V) : ¬IntervalTable (graph X.D F) q r e := by
  classical
  intro table
  obtain ⟨_,_,a,aa,b,bb,_,off,_,edge,_⟩ :=
    SharedArcAffordablePaths.boundary_turn X (by omega) step good stop
  have cycle : ShenCycleSuccessor.Cycle X.D X.V q B := (mem_filter.mp step.1).2
  exact blocked (progress X three F B H p c hr e table ⟨(⟨a,cycle.sub aa⟩,⟨b,cycle.sub bb⟩),edge,off⟩)

end LeanCH.BR.Closure.SingleArcNeighbourWitness
#print axioms LeanCH.BR.Closure.SingleArcNeighbourWitness.interval_witness
#print axioms LeanCH.BR.Closure.SingleArcNeighbourWitness.progress
#print axioms LeanCH.BR.Closure.SingleArcNeighbourWitness.progress_of_sign
#print axioms LeanCH.BR.Closure.SingleArcNeighbourWitness.excluded
