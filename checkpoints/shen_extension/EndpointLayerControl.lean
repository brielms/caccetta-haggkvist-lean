import checkpoints.shen_extension.EndpointLayerWitness
import LeanCH.BR.BRCirculantReturnCapacity

namespace LeanCH.BR.Closure.EndpointLayerControl
open Finset Matrix BRq2 BRq3 BR45 EndpointLayerWitness OneStepColumnMerge
open ClosedNeighborhoodRepair CirculantReturnCapacity
open scoped Matrix

/-- Remove just 0→1 from the boundary circulant. Every old parent of 1
hits 0, which 1 misses. At the same time d+1 receives from the entire
first layer of 0. The child is q-free at every cutoff and degree below. -/
theorem interval (q d : ℕ) (hq : 2≤q) (hd : 2≤d) :
    let V := range (q*d+1)
    let D := ClosedNeighborhoodRepair.graph q d
    let E := fun i j=>if i=0 ∧ j=1 then false else D i j
    QFree D V q ∧ D 0 1=true ∧
      (∃k∈V,E k 1=true) ∧
      (∀k∈V,E k 1=true → E k 0=true ∧ D 1 0=false) ∧
      (∃j∈V,j≠0 ∧ D 0 j=false ∧ ∀s∈V,D 0 s=true → D s j=true) := by
  intro V D E
  have room : d+1<q*d+1 := by nlinarith
  have one : 1<q*d+1 := by omega
  have on : D 0 1=true := forward_edge (by omega) (by omega) one
  have back : D 1 0=false := by
    apply Bool.eq_false_iff.mpr
    intro ed
    obtain ⟨r,hr,rd,step⟩ := edge_step ed
    change (1+r)%(q*d+1)=0%(q*d+1) at step
    rw [Nat.mod_eq_of_lt (by omega),Nat.zero_mod] at step
    omega
  have last : q*d∈V := mem_range.mpr (by omega)
  have lastEdge := @offset_edge q d (q*d) 2 (by omega) (by omega) hd
  have mod1 : (q*d+2)%(q*d+1)=1 := by
    rw [show q*d+2=1+(q*d+1) by omega,Nat.add_mod_right,Nat.mod_eq_of_lt one]
  rw [mod1] at lastEdge
  refine ⟨free q d,on,⟨q*d,last,by simpa [E,D,show q*d≠0 by omega] using lastEdge⟩,?_,?_⟩
  · intro k kv ed
    have kn : k≠0 := by rintro rfl; simp [E] at ed
    have old : D k 1=true := by simpa [E,kn] using ed
    obtain ⟨r,rp,rd,step⟩ := edge_step old
    have small := mem_range.mp kv
    change (k+r)%(q*d+1)=1%(q*d+1) at step
    rw [Nat.mod_eq_of_lt one] at step
    have wrap : q*d+1≤k+r := by
      by_contra! lt
      rw [Nat.mod_eq_of_lt lt] at step
      omega
    have bound : k+r-(q*d+1)<q*d+1 := by omega
    rw [Nat.mod_eq_sub_mod wrap,Nat.mod_eq_of_lt bound] at step
    have jump := @offset_edge q d k (r-1) small (by omega) (by omega)
    rw [show k+(r-1)=q*d+1 by omega,Nat.mod_self] at jump
    exact ⟨by simpa [E,D] using jump,back⟩
  · have zero (i : ℕ) : D 0 i=true ↔ i∈Icc 1 d := by
      change decide (0<q*d+1 ∧ i∈heads q d 0)=true ↔ _
      rw [decide_eq_true_eq,heads_zero (by omega)]
      simp
    refine ⟨d+1,mem_range.mpr room,by omega,Bool.eq_false_iff.mpr (fun e=>by simpa using (zero _).mp e),?_⟩
    intro s _ ed
    obtain ⟨sp,sd⟩ := mem_Icc.mp ((zero _).mp ed)
    exact forward_edge (by omega) (by omega) room

/-- Q-freeness and the complete absence of covered parents are compatible
with failure of every one-layer multiplier, even with arbitrary rational
weights and an arbitrary coefficient at the tail. -/
theorem fails_one_layer (q d : ℕ) (hq : 2≤q) (hd : 2≤d) :
    let V := range (q*d+1)
    let D := ClosedNeighborhoodRepair.graph q d
    ∃a b : V,a.val=0 ∧ b.val=1 ∧ ∀z : V→ℚ,(∀s,0≤z s) →
      (∀s : V,D a s=false → z s=0) → ∀c : ℚ,
      ¬∀i,(bump z a c ᵥ* SingleArcTensorMerge.center q D V) i≤mergeCoefficient q D V {a.val,b.val} i := by
  intro V D
  obtain ⟨free,on,_,_,j,jv,nz,off,all⟩ := interval q d hq hd
  let a : V := ⟨0,mem_range.mpr (by nlinarith)⟩
  let b : V := ⟨1,mem_range.mpr (by nlinarith)⟩
  let t : V := ⟨j,jv⟩
  refine ⟨a,b,rfl,rfl,fun z nn support c=>?_⟩
  exact common_exterior D q a free hq on (j:=t) ⟨fun eq=>nz (congrArg Subtype.val eq),off⟩
    (fun s ed=>all s s.property ed) z nn support c


section Obstruction
open WeightedSD WeightedArithmetic FiniteCutInverse

private theorem entry {V : Finset ℕ} (D : CH.Digraph) (q : ℕ) (i j : V) :
    SingleArcTensorMerge.center q D V i j =
      (if i=j then 1 else 0)+(if D i j then (q:ℚ) else 0)-1 := by
  by_cases eq : i=j
  · subst j; cases e : D i i <;> simp [SingleArcTensorMerge.center,rationalMatrix,closedMatrix,adjacencyMatrix,e]
  · cases e : D i j <;> simp [SingleArcTensorMerge.center,rationalMatrix,closedMatrix,adjacencyMatrix,eq,e]

/-- A nonnegative nullvector of the centered child with positive weight
at b precludes every signed endpoint witness, even before a parent is
specified. At column b the merge falls short of row a by q−1. -/
theorem null_obstruction {V : Finset ℕ} (D : CH.Digraph) (q : ℕ) (hq : 2≤q)
    (a b : V) (ab : D a b=true) (bb : D b b=false) (x : V→ℚ)
    (nn : ∀i,0≤x i) (xb : 0<x b) (null : SingleArcTensorMerge.center q D V *ᵥ x=0) :
    ¬∃y : V→ℚ,∀i,(y ᵥ* SingleArcTensorMerge.center q D V) i≤mergeCoefficient q D V {a.val,b.val} i := by
  rintro ⟨y,le⟩
  let A := SingleArcTensorMerge.center q D V
  let m := mergeCoefficient q D V {a.val,b.val}
  have ne : a≠b := by rintro rfl; simp [bb] at ab
  have nval : b.val≠a.val := fun e=>ne (Subtype.ext e.symm)
  have qpos : (1:ℚ)<q := by exact_mod_cast (by omega : 1<q)
  have point (i : V) : m i≤A a i := by
    rw [show A a i=_ from entry D q a i]
    by_cases common : i.val∈StrictFlatSubsetMerge.common D V {a.val,b.val}
    · have edge := (mem_filter.mp common).2 a.val (by simp)
      have ib : i≠b := by
        rintro rfl
        have e := (mem_filter.mp common).2 i.val (by simp)
        simp [bb] at e
      by_cases ia : a=i
      · subst i; simp [m,mergeCoefficient,common,edge]
      · have miss : i.val∉({a.val,b.val}:Finset ℕ) := fun h=>(mem_insert.mp h).elim (fun e=>ia (Subtype.ext e.symm)) (fun e=>ib (Subtype.ext (mem_singleton.mp e)))
        simp only [m,mergeCoefficient,common,edge,miss,ia,ite_true,ite_false,zero_add,le_refl]
    · by_cases ia : a=i
      · subst i; simp [m,mergeCoefficient,common]; split <;> linarith
      · by_cases ib : i=b
        · subst i; simp [m,mergeCoefficient,common,ne,ab]; linarith
        · have miss : i.val∉({a.val,b.val}:Finset ℕ) := fun h=>(mem_insert.mp h).elim (fun e=>ia (Subtype.ext e.symm)) (fun e=>ib (Subtype.ext (mem_singleton.mp e)))
          simp only [m,mergeCoefficient,common,ia,miss,ite_false,zero_add]; split <;> linarith
  have strict : m b<A a b := by
    have absent : b.val∉StrictFlatSubsetMerge.common D V {a.val,b.val} := by
      intro h
      have e := (mem_filter.mp h).2 b.val (by simp)
      simp [bb] at e
    rw [show A a b=_ from entry D q a b]
    simp [m,mergeCoefficient,absent,ne,ab]; linarith
  have neg : m ⬝ᵥ x < (A *ᵥ x) a :=
    sum_lt_sum (fun i _=>mul_le_mul_of_nonneg_right (point i) (nn i)) ⟨b,mem_univ _,mul_lt_mul_of_pos_right strict xb⟩
  have bound : (y ᵥ* A) ⬝ᵥ x ≤ m ⬝ᵥ x := sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (le i) (nn i))
  rw [←dotProduct_mulVec,null,dotProduct_zero] at bound
  rw [null,Pi.zero_apply] at neg
  exact neg.not_ge bound

/-- The interval child has the constant positive nullvector. Summing
already rules out every multiplier, including arbitrary full-support ones. -/
theorem no_endpoint (q d : ℕ) (hq : 2≤q) (hd : 2≤d) :
    let V := range (q*d+1)
    let D := ClosedNeighborhoodRepair.graph q d
    ∃a b : V,a.val=0 ∧ b.val=1 ∧ ¬∃y : V→ℚ,
      ∀i,(y ᵥ* SingleArcTensorMerge.center q D V) i≤mergeCoefficient q D V {a.val,b.val} i := by
  intro V D
  let a : V := ⟨0,mem_range.mpr (by nlinarith)⟩
  let b : V := ⟨1,mem_range.mpr (by nlinarith)⟩
  obtain ⟨safe,on,_,_,_⟩ := interval q d hq hd
  refine ⟨a,b,rfl,rfl,null_obstruction D q hq a b on
    (Bool.eq_false_iff.mpr (loopfree safe (by omega) b.property)) (fun _=>1) (by simp) (by norm_num) ?_⟩
  funext i
  change (∑j : V,(rationalMatrix q (adjacencyMatrix D V) i j-1)*1)=0
  simp only [mul_one,sum_sub_distrib]
  have row := unit_feasible (q:=q) (d:=d) (by omega) i.val i.property
  rw [←WeightedSD.matrix_row q D V (fun _=>1) i] at row
  have h : (∑j : V,rationalMatrix q (adjacencyMatrix D V) i j)=mass V (fun _=>1) := by
    change (∑j : V,rationalMatrix q (adjacencyMatrix D V) i j*1)=_ at row
    simpa only [mul_one] using row
  rw [h]; simp [mass]


private theorem advance {q d : ℕ} (k : ℕ) {i s : ℕ} (iv : i<q*d+1) (budget : s≤k*d) :
    ∃l≤k, Walk (ClosedNeighborhoodRepair.graph q d) (range (q*d+1)) i ((i+s)%(q*d+1)) l := by
  induction k generalizing i s with
  | zero =>
    have zero : s=0 := by simpa using budget
    exact ⟨0,le_rfl,by simpa [zero,Nat.mod_eq_of_lt iv] using (Walk.refl (D:=ClosedNeighborhoodRepair.graph q d) (W:=range (q*d+1)) i)⟩
  | succ k ih =>
    by_cases sk : s≤k*d
    · obtain ⟨l,le,path⟩ := ih iv sk
      exact ⟨l,by omega,path⟩
    let r := s-k*d
    have rp : 1≤r := by dsimp [r]; omega
    have rd : r≤d := by rw [Nat.succ_mul] at budget; dsimp [r]; omega
    let v := (i+r)%(q*d+1)
    have vv : v<q*d+1 := Nat.mod_lt _ (by omega)
    obtain ⟨l,le,path⟩ := ih (i:=v) (s:=k*d) vv le_rfl
    have same : (v+k*d)%(q*d+1)=(i+s)%(q*d+1) := by
      rw [show v=(i+r)%(q*d+1) from rfl,Nat.mod_add_mod,show i+r+k*d=i+s by dsimp [r]; omega]
    rw [same] at path
    exact ⟨l+1,by omega,.step (mem_range.mpr vv) (offset_edge iv rp rd) path⟩

/-- Every absent arc of the child has a blocking return within q−1. -/
theorem saturated (q d : ℕ) (hq : 2≤q) :
    BRsub.Sat q (ClosedNeighborhoodRepair.graph q d) (range (q*d+1)) := by
  intro j jv i iv off
  have il := mem_range.mp iv
  have jl := mem_range.mp jv
  let N := q*d+1
  let r := (j+N-i)%N
  have Npos : 0<N := by dsimp [N]; omega
  have modj : (i+r)%N=j := by
    rw [show r=(j+N-i)%N from rfl,Nat.add_mod_mod,show i+(j+N-i)=j+N by dsimp [N]; omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt jl]
  have bound : r<N := Nat.mod_lt _ Npos
  by_cases zero : r=0
  · rw [zero,Nat.add_zero,Nat.mod_eq_of_lt il] at modj
    exact mem_ball.mpr ⟨iv,0,by omega,modj ▸ Walk.refl i⟩
  have big : d<r := by
    by_contra! le
    have edge := @offset_edge q d i r il (by omega) le
    exact off (modj ▸ edge)
  have prod : (q-1)*d+d=q*d := by
    rw [←Nat.succ_mul,show (q-1).succ=q by omega]
  have left : N-r≤(q-1)*d := by dsimp [N] at *; omega
  obtain ⟨l,le,path⟩ := advance (q-1) jl left
  have dest : (j+(N-r))%N=i := by
    rw [←modj,Nat.mod_add_mod,show i+r+(N-r)=i+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt il]
  rw [show q*d+1=N from rfl,dest] at path
  exact mem_ball.mpr ⟨iv,l,le,path⟩

/-- The old graph fails a capstone flat hypothesis: deleting 0→1 spoils
every positive normalized column law. This distinguishes the control
from a flat legal singleton. -/
theorem old_column_not_flat (q d : ℕ) (hq : 2≤q) (hd : 2≤d) :
    let V := range (q*d+1)
    let D := ClosedNeighborhoodRepair.graph q d
    let E := fun i j=>if i=0 ∧ j=1 then false else D i j
    ¬∃p : ℕ→ℚ,(∀i∈V,0<p i) ∧ WeightedSD.mass V p=1 ∧ ∀i∈V,WeightedSD.col q E V p i=1 := by
  intro V D E
  rintro ⟨p,pos,pm,col⟩
  obtain ⟨_,on,_,_,_⟩ := interval q d hq hd
  change D 0 1=true at on
  have zero : 0∈V := mem_range.mpr (by nlinarith)
  have one : 1∈V := mem_range.mpr (by nlinarith)
  let unit : ℕ→ℚ := fun _=>1
  let m := WeightedSD.mass V unit
  have same (i) (iv : i∈V) : WeightedSD.row q E V unit i=m-(if i=0 then (q:ℚ) else 0) := by
    have full : WeightedSD.row q D V unit i=m := unit_feasible (by omega) i iv
    rw [←full,WeightedSD.row,WeightedSD.row]
    by_cases eq : i=0
    · subst i
      have cut : WeightedSD.outW E V unit 0+1=WeightedSD.outW D V unit 0 := by
        rw [WeightedSD.outW_erase (D:=E) one,WeightedSD.outW_erase (D:=D) one]
        have same : WeightedSD.outW E (V.erase 1) unit 0=WeightedSD.outW D (V.erase 1) unit 0 := by
          apply sum_congr rfl
          intro j hj
          simp [E,ne_of_mem_erase hj]
        rw [same]; simp [E,on,unit]
      simp; linarith only [congrArg (fun v : ℚ=>(q:ℚ)*v) cut]
    · have eqr : WeightedSD.outW E V unit i=WeightedSD.outW D V unit i := by simp [E,WeightedSD.outW,eq]
      simp [eq,eqr]
  have account := WeightedSD.rational_cross_rows q E V unit p
  rw [sum_congr rfl (fun i hi=>congrArg (p i*·) (same i hi)),
    sum_congr rfl (fun i hi=>show unit i*WeightedSD.col q E V p i=1 by simp [unit,col i hi])] at account
  simp only [mul_sub,sum_sub_distrib,←sum_mul,mul_ite,mul_zero,sum_ite_eq',zero,ite_true] at account
  change WeightedSD.mass V p*m-p 0*q=m at account
  have qp : 0<(q:ℚ) := by exact_mod_cast (by omega : 0<q)
  rw [pm,one_mul] at account
  linarith only [account,mul_pos (pos _ zero) qp]

end Obstruction

end LeanCH.BR.Closure.EndpointLayerControl
#print axioms LeanCH.BR.Closure.EndpointLayerControl.interval
#print axioms LeanCH.BR.Closure.EndpointLayerControl.fails_one_layer
#print axioms LeanCH.BR.Closure.EndpointLayerControl.null_obstruction
#print axioms LeanCH.BR.Closure.EndpointLayerControl.no_endpoint
#print axioms LeanCH.BR.Closure.EndpointLayerControl.saturated
#print axioms LeanCH.BR.Closure.EndpointLayerControl.old_column_not_flat

