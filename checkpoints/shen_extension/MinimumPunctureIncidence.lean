import checkpoints.shen_extension.TriangleMinimumPuncture

namespace LeanCH.BR.Closure.MinimumPunctureIncidence
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShortestCycleWeights

/-- Strict original rows pay for a second sender at some retained exterior
head, unless the single removed minimum atom can pay the whole count. -/
theorem receiver {q n} (X : Model q n) (hq : 2≤q) {h M} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x)
    (cycle : ShenCycleSuccessor.Cycle X.D (X.V\{h}) q M) :
    X.V.card≤q*(inN X.D M h).card ∨
    ∃z∈(X.V\{h})\M, 2≤(inN X.D M z).card := by
  classical
  by_contra! fail
  let W := X.V.erase h
  let m := X.weights h
  let k := (inN X.D M h).card
  have mv := cycle.sub.trans (sdiff_subset : X.V\{h}⊆X.V)
  have sz := cycle.size
  have one := (dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (X.free.mono_set mv)
    (fun x xm => (cycle.heads x xm).ge) (by simpa using sz)).2
  have bound (z) (zw : z∈W) : (inN X.D M z).card≤1 := by
    by_cases zm : z∈M
    · exact (one z zm).le
    · have e := mem_erase.mp zw
      have f := fail.2 z (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨e.2,by simpa using e.1⟩,zm⟩)
      omega
  let I := fun z => (inN X.D M z).card*X.weights z
  have total : (∑x∈M,∑y∈X.V,if X.D x y=true then X.weights y else 0)=∑y∈X.V,I y := by
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    change _ = (inN X.D M y).card*X.weights y
    calc
      _ = ∑ _x∈inN X.D M y,X.weights y := by simp only [inN,sum_filter]
      _ = _ := by simp
  have wb : (∑z∈W,I z)≤∑z∈W,X.weights z := sum_le_sum fun z zw => by
    have := Nat.mul_le_mul_right (X.weights z) (bound z zw)
    simpa [I] using this
  have hi := sum_erase_add X.V I hv
  have wm := sum_erase_add X.V X.weights hv
  change (∑z∈W,I z)+k*m=_ at hi
  change (∑z∈W,X.weights z)+m=_ at wm
  let S := ∑x∈X.V,X.weights x
  let T := ∑x∈M,X.weights x
  have lb : M.card*S < ∑x∈M,score q X.D X.V X.weights x := by
    have e := sum_lt_sum_of_nonempty (card_pos.mp (by omega : 0<M.card))
      (fun x xm => nat_strict.mp X.strict x (mv xm))
    simpa [S] using e
  have id : (∑x∈M,score q X.D X.V X.weights x)=T+q*(∑z∈X.V,I z) := by
    simp only [score,sum_add_distrib,←mul_sum,total,T]
  rw [id,sz,Nat.add_mul,Nat.one_mul] at lb
  have cmp : (∑z∈X.V,I z)+m≤S+k*m := by dsimp [S]; omega
  have mp := Nat.mul_le_mul_left q cmp
  rw [Nat.mul_add,Nat.mul_add] at mp
  have split := sum_sdiff mv (f:=X.weights)
  change (∑z∈X.V\M,X.weights z)+T=S at split
  have mass : (X.V\M).card*m≤∑z∈X.V\M,X.weights z := by
    simpa [m] using sum_le_sum (s:=X.V\M) (fun z (hz : z∈X.V\M) => minimum z (mem_sdiff.mp hz).1)
  have cmp2 : ((X.V\M).card+q)*m < (q*k)*m := by
    rw [Nat.add_mul,Nat.mul_assoc q k m]
    omega
  have lt := Nat.lt_of_mul_lt_mul_right cmp2
  have cards := card_sdiff_add_card_eq_card mv
  have tooMany : q*k<X.V.card := fail.1
  omega

#print axioms receiver
end LeanCH.BR.Closure.MinimumPunctureIncidence
