import checkpoints.shen_extension.FullFamilySchedule

namespace LeanCH.BR.Closure.RecurrentRecipient
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier FullCycleTransfer PairedFamilyLoop CycleSlotOrbit FullFamilySchedule

/-- Name the two smaller single-transfer tests used to compare the same row. -/
def Fails (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (x : ℕ → ℚ) (b y r : ℕ) : Prop :=
  b∈V.erase y ∧ WeightedSD.row q E (V.erase y) (transferWeight x y r) b <
    mass (V.erase y) (transferWeight x y r)

/-- In a common equalizer the chosen row strictly fails the marked single-label
transfer, and strictly fails the reverse of a later transfer on its very same
label trajectory. The full trial at the first step also fails at this row. -/
theorem orbit {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F x c} (sub : F⊆family X) (two : 2≤F.card) (pos : ∀z∈X.V,0≤x z)
    (high : mass X.V x<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c) :
    let E := graph X.D F
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))),
    (∀a,previous (go a)=current a ∧ ∃ b,∃ r : ↥(previous a),
      E b r=false ∧ E b (send a r)=true ∧ Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
    ∃ s : Slot go previous, ∃ b,
      let step := lift go previous send
      let label := fun k : ℕ => ((step^[k] s).2 : ℕ)
      Mark q E X.V x s.1.val (go s.1.val) (send s.1.val) b (label 1) (label 0) ∧
      E b (label 0)=false ∧ E b (label 1)=true ∧ label 2=label 1 ∧
      Fails q E X.V x b (label 1) (label 0) ∧
      ∃ k,2≤k ∧ k<minimalPeriod step s ∧ E b (label k)=true ∧ E b (label (k+1))=false ∧
        Fails q E X.V x b (label k) (label (k+1)) := by
  classical
  intro E
  obtain ⟨initial⟩ := seed two
  obtain ⟨go,send,all,_,_,s,_,b,mark,miss,hit,k,kpos,kshort,other,otherMiss⟩ :=
    schedule (admissible X small sub pos (fun z hz => (rows z hz) ▸ high)) initial
  let step := lift go previous send
  let label := fun i : ℕ => ((step^[i] s).2 : ℕ)
  have marked : Mark q E X.V x s.1.val (go s.1.val) (send s.1.val) b (label 1) (label 0) := mark
  obtain ⟨_,_,_,bs,ys,_⟩ := marked
  have fm (a : PairedFamilyLoop.State F) : current a∈F := (mem_product.mp (mem_filter.mp a.property).1).2
  have carrier {T} (tf : T∈F) : T⊆X.V := mem_powerset.mp (mem_filter.mp (sub tf)).1
  have bv := carrier (fm _) (mem_sdiff.mp bs).1
  have inside (i) : label i∈X.V :=
    carrier (mem_product.mp (mem_filter.mp (step^[i] s).1.val.property).1).1 (step^[i] s).2.property
  let slot1 := step s
  obtain ⟨join,_,_,_,_,P,forward,_⟩ := all slot1.1.val
  have shared : (slot1.2 : ℕ)∈previous (go slot1.1.val) := by
    rw [join]
    exact (mem_inter.mp ys).1
  let Y : ↥(previous (go slot1.1.val)) := ⟨slot1.2,shared⟩
  have fixed : P.equiv Y=slot1.2 := Subtype.ext (P.fixed Y slot1.2.property)
  have back : P.equiv.symm slot1.2=Y := P.equiv.symm_apply_eq.mpr fixed.symm
  have pause : label 2=label 1 := by
    change (send slot1.1.val slot1.2 : ℕ)=(slot1.2 : ℕ)
    rw [forward,back]
  have first : E b (label 1)=true := hit
  have later : E b (label (k+1))=false := otherMiss
  have skipped : k≠1 := by
    intro eq
    subst k
    rw [show 1+1=2 by decide,pause,first] at later
    contradiction
  have fail {y r} (yv : y∈X.V) (rv : r∈X.V) (seen : E b y=true) (absent : E b r=false) :
      Fails q E X.V x b y r :=
    PairedFamilyLoop.fails hq (PrivateArcEndpoints.graph_free X F) small pos high rows bv yv rv seen absent
  exact ⟨go,send,all,s,b,mark,miss,hit,pause,fail (inside 1) (inside 0) hit miss,
    k,by omega,kshort,other,otherMiss,fail (inside k) (inside (k+1)) other otherMiss⟩

#print axioms orbit
end LeanCH.BR.Closure.RecurrentRecipient
