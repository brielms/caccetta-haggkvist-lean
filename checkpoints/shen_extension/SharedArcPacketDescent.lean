import checkpoints.shen_extension.SharedArcPacketReturns
import LeanCH.BR.BRWeightedExtremalExchange

namespace LeanCH.BR.Closure.SharedArcPacketDescent
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier

/-- Minimize the strict child's common value among the boundary cycles with
the fewest changed heads. Compare competitors at this one fixed price vector.
A nonincreasing change of all columns is necessarily an equality throughout. -/
theorem terminal {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F} (next : ∃B,Boundary X F B) (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) :
    ∃B,Boundary X F B ∧ (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) ∧
    ∃p : ℕ→ℚ,∃c : ℚ,1<c ∧ (∀v∈X.V,0<p v) ∧ mass X.V p=1 ∧
      (∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c) ∧
      ∀M,Boundary X F M → (targets X.D X.V F M).card=(targets X.D X.V F B).card →
        ∃x r : ℕ→ℚ,∃d : ℚ,c≤d ∧ (∀v∈X.V,0<x v) ∧ mass X.V x=1 ∧
          (∀v∈X.V,WeightedSD.row q (graph X.D (insert M F)) X.V x v=d) ∧
          (∀v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V r v=d) ∧
          (d-c=∑v∈X.V,x v*(WeightedSD.col q (graph X.D (insert M F)) X.V p v-c)) ∧
          ((∀v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V p v≤c) →
            d=c ∧ ∀v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V p v=c ∧ r v=p v) := by
  classical
  let G := fun M => graph X.D (insert M F)
  have supply (M : Finset ℕ) : ∃x p : ℕ→ℚ,∃c : ℚ,Boundary X F M →
      1<c ∧ (∀v∈X.V,0<x v) ∧ (∀v∈X.V,0<p v) ∧ mass X.V x=1 ∧ mass X.V p=1 ∧
      (∀v∈X.V,WeightedSD.row q (G M) X.V x v=c) ∧ (∀v∈X.V,WeightedSD.col q (G M) X.V p v=c) := by
    by_cases b : Boundary X F M
    · obtain ⟨w,wn,_,hi⟩ := strict_witness_of_not_smallRow (stop M b)
      obtain ⟨x,p,c,h⟩ := strict_pair_of_proper_smallRow (small.induced (PrivateArcEndpoints.graph_free X _)) X.live w wn hi
      exact ⟨x,p,c,fun _ => h⟩
    · exact ⟨0,0,0,fun h => (b h).elim⟩
  choose x p c laws using supply
  obtain ⟨A,ba,minA⟩ := SharedArcMinimalPacket.select X next
  let k := fun M => (targets X.D X.V F M).card
  let pool := (family X).filter (fun M => Boundary X F M ∧ k M=k A)
  have am : A∈pool := mem_filter.mpr ⟨ba.1,ba,rfl⟩
  obtain ⟨B,bp,least⟩ := pool.exists_min_image c ⟨A,am⟩
  obtain ⟨_,b,sz⟩ := mem_filter.mp bp
  obtain ⟨high,_,pp,_,pm,_,cols⟩ := laws B b
  refine ⟨B,b,fun M h => (show k B=k A from sz).le.trans (minA M h),p B,c B,high,pp,pm,cols,?_⟩
  intro M bm number
  have low := least M (mem_filter.mpr ⟨bm.1,bm,number.trans sz⟩)
  obtain ⟨_,xp,_,xm,_,rows,rc⟩ := laws M bm
  have cross := rational_cross_rows q (G M) X.V (x M) (p B)
  rw [sum_congr rfl (fun i hi => by rw [rows i hi]),←sum_mul] at cross
  change mass X.V (p B)*c M=_ at cross
  rw [pm,one_mul] at cross
  have val : c M-c B=∑v∈X.V,x M v*(WeightedSD.col q (G M) X.V (p B) v-c B) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib,←cross,←sum_mul]
    change _=c M-mass X.V (x M)*c B
    rw [xm,one_mul]
  refine ⟨x M,p M,c M,low,xp,xm,rows,rc,val,?_⟩
  intro weak
  have neg (v) (vv : v∈X.V) : x M v*(WeightedSD.col q (G M) X.V (p B) v-c B)≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (xp v vv).le (sub_nonpos.mpr (weak v vv))
  have nz := sum_nonpos (s:=X.V) neg
  rw [←val] at nz
  have eq : c M=c B := le_antisymm (by linarith) low
  have zero : (∑v∈X.V,x M v*(WeightedSD.col q (G M) X.V (p B) v-c B))=0 := by rw [←val,eq,sub_self]
  have pc (v) (vv : v∈X.V) : WeightedSD.col q (G M) X.V (p B) v=c B := by
    have z := (sum_eq_zero_iff_of_nonpos neg).mp zero v vv
    exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (xp v vv).ne')
  have same := row_laws_unique_on (D:=fun i j => G M j i) hq rc (fun i hi => (pc i hi).trans eq.symm)
  exact ⟨eq,fun i hi => ⟨pc i hi,same i hi⟩⟩

/-- Strict improvement is measured at the fixed full-child prices. It
does not require the competing cycle to fit under one. -/
def Cheaper {q n} (X : Model q n) (F : Family) (B : Finset ℕ) (p : ℕ→ℚ) (c : ℚ) : Prop :=
  ∃M,Boundary X F M ∧ (targets X.D X.V F M).card=(targets X.D X.V F B).card ∧
    (∀v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V p v≤c) ∧
    ∃v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V p v<c

/-- A single, genuinely cheaper replacement tail suffices for descent when
it realizes another boundary cycle with the same number of changed heads. -/
theorem cheaper_of_swap {q n} (X : Model q n) (hq : 0<q) {F B M}
    (step : Boundary X F M) (count : (targets X.D X.V F M).card=(targets X.D X.V F B).card)
    {p : ℕ→ℚ} {c : ℚ} (cols : ∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c)
    {a b z : ℕ} (av : a∈X.V) (bv : b∈X.V) (zv : z∈X.V)
    (old : graph X.D (insert B F) a b=true) (fresh : ¬graph X.D (insert B F) z b=true)
    (replace : graph X.D (insert M F)=insertArc (eraseArc (graph X.D (insert B F)) a b) z b)
    (discount : p z<p a) : Cheaper X F B p c := by
  let G := graph X.D (insert B F)
  have rev : (fun x y => insertArc (eraseArc G a b) z b y x)=
      insertArc (eraseArc (fun x y => G y x) b a) b z := by
    funext x y
    simp only [insertArc,eraseArc,and_comm]
  have price (v) (vv : v∈X.V) : WeightedSD.col q (graph X.D (insert M F)) X.V p v =
      c + if v=b then (q:ℚ)*(p z-p a) else 0 := by
    rw [replace]
    change WeightedSD.row q (fun x y => insertArc (eraseArc G a b) z b y x) X.V p v=_
    rw [rev,row_same_tail_exchange (D:=fun x y => G y x) q av zv old fresh p v]
    change WeightedSD.col q (graph X.D (insert B F)) X.V p v+_=_
    rw [cols v vv]
  have gain := mul_neg_of_pos_of_neg (show (0:ℚ)<q by exact_mod_cast hq) (sub_neg.mpr discount)
  refine ⟨M,step,count,fun v vv => ?_,b,bv,?_⟩
  · rw [price v vv]
    split_ifs <;> linarith
  · rw [price b bv,ite_eq_left rfl]
    linarith

#print axioms cheaper_of_swap

def ProgressAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ) (H : Matrix X.V X.V ℝ)
    (p : ℕ→ℚ) (c : ℚ) : Prop := SharedArcPacketReturns.ExitAt X F B H ∨ Cheaper X F B p c

theorem blocks_progress {q n} (X : Model q n) {F B H p c}
    (blocked : ¬SharedArcPacketReturns.ExitAt X F B H)
    (flat : ∀M,Boundary X F M → (targets X.D X.V F M).card=(targets X.D X.V F B).card →
      (∀v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V p v≤c) →
      ∀v∈X.V,WeightedSD.col q (graph X.D (insert M F)) X.V p v=c) :
    ¬ProgressAt X F B H p c := by
  rintro (exit|⟨M,b,count,weak,v,vv,lt⟩)
  · exact blocked exit
  · exact lt.ne (flat M b count weak v vv)

/-- One generic sufficiency statement for the original CH entry point.
The last option only asks for a strict improvement at one column with no
increase elsewhere, even when both children are still strictly above one. -/
def Law {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → SmallRow q (graph X.D F) X.V →
    Boundary X F B → (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) →
    ∀H : Matrix X.V X.V ℝ,FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H →
    (∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a) →
    ∀p : ℕ→ℚ,∀c : ℚ,1<c → (∀v∈X.V,0<p v) → mass X.V p=1 →
    (∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c) → ProgressAt X F B H p c

theorem ch_of_descent (law : ∀q n,∀X : Model q n,2≤q → SmallerSmallRow q X.V.card → Law X) :
    CH.CaccettaHaggkvistConjecture := by
  apply SharedArcInduction.ch_of_extension
  intro q n X hq small
  exfalso
  classical
  obtain ⟨u,uv⟩ := X.live
  obtain ⟨C,_,cc,_,_,_,_⟩ := ShortestReturnCertificate.on_model X hq uv
  have cf : C∈family X := mem_filter.mpr ⟨mem_powerset.mpr cc.sub,cc⟩
  obtain ⟨F,built,sub,_,spans,old,_,next,stop⟩ := SharedArcBarrier.on_source X hq small cf
  obtain ⟨B,step,least,p,c,high,pos,pm,cols,compare⟩ := terminal X hq small next (fun M b => (stop M b).1)
  obtain ⟨H,inv,charge⟩ := SharedArcMinimalPacket.charges X hq small old step least (stop B step).1
  have blocked := SharedArcPacketReturns.blocks_exit X hq small step least inv charge (fun M b => (stop M b).1)
  apply blocks_progress X blocked _ (law q n X hq small C F B built sub spans old step least H inv charge p c high pos pm cols)
  intro M b cnt weak v vv
  obtain ⟨_,_,_,_,_,_,_,_,_,plateau⟩ := compare M b cnt
  exact ((plateau weak).2 v vv).1

#print axioms blocks_progress
#print axioms ch_of_descent

#print axioms terminal
end LeanCH.BR.Closure.SharedArcPacketDescent
