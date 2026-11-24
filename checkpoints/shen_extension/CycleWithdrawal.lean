import checkpoints.shen_extension.PrivateArcEndpoints

namespace LeanCH.BR.Closure.CycleWithdrawal
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier

/-- Subtract the same integer at every label of A. -/
def withdraw (A : Finset ℕ) (w : ℕ → ℕ) (t x : ℕ) : ℕ :=
  if x ∈ A then w x - t else w x

def Eligible (q n : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℕ) : Prop :=
  (∀ x ∈ V, 0 < w x) ∧ (∑ x ∈ V, w x) ≤ n ∧ Strict q E V w

/-- The same exterior row has multiple distinct heads on A, is strictly paid at w,
and fails after one unit is withdrawn on A. Its old margin fits in the exact loss. -/
def BarrierRow (q : ℕ) (E : CH.Digraph) (V A : Finset ℕ) (w : ℕ → ℕ) (p : ℕ) : Prop :=
  let k := (outN E A p).card
  let margin := score q E V w p - ∑ x ∈ V, w x
  p ∈ V \ A ∧ 2 ≤ k ∧ 0 < margin ∧ margin + (q+1) ≤ q*k ∧
    score q E V (withdraw A w 1) p ≤ ∑ x ∈ V, withdraw A w 1 x

/-- Exact mass removed from an arbitrary test set. -/
theorem sum_withdraw {A : Finset ℕ} {w t} (room : ∀ x ∈ A, t ≤ w x) (S : Finset ℕ) :
    (∑ x ∈ S, withdraw A w t x) + (S ∩ A).card*t = ∑ x ∈ S, w x := by
  classical
  have eq : S.filter (· ∈ A) = S ∩ A := by ext; simp
  have count : (∑ x ∈ S, if x ∈ A then t else 0) = (S ∩ A).card*t := by
    rw [← sum_filter, eq, sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [←count, ←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  by_cases hx : x ∈ A
  · simpa [withdraw, hx] using Nat.sub_add_cancel (room x hx)
  · simp [withdraw, hx]

/-- One diagonal term and all incident heads give the complete score change. -/
theorem score_withdraw {V A : Finset ℕ} {w t} (sub : A ⊆ V) (room : ∀ x ∈ A, t ≤ w x)
    (q : ℕ) (E : CH.Digraph) (p : ℕ) :
    score q E V (withdraw A w t) p + (if p ∈ A then t else 0) +
      q*((outN E A p).card*t) = score q E V w p := by
  classical
  have eq : outN E V p ∩ A = outN E A p := by
    ext x
    simp only [mem_inter, mem_outN]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨sub h.1,h.2⟩,h.1⟩⟩
  have heads := sum_withdraw room (outN E V p)
  rw [eq] at heads
  have multiple := congrArg (q * ·) heads
  rw [Nat.mul_add] at multiple
  have diag : withdraw A w t p + (if p ∈ A then t else 0) = w p := by
    by_cases h : p ∈ A
    · simpa [withdraw,h] using Nat.sub_add_cancel (room p h)
    · simp [withdraw,h]
  simp only [score, ←sum_filter]
  change withdraw A w t p + q*(∑ x ∈ outN E V p, withdraw A w t x) + _ + _ =
    w p + q*(∑ x ∈ outN E V p, w x)
  omega

private theorem zero_forces_failure {q n} (X : Model q n) {E w}
    (free : QFree E X.V q) (budget : (∑ x ∈ X.V, w x) ≤ n)
    {a} (av : a ∈ X.V) (zero : w a = 0) : ¬ Strict q E X.V w := by
  classical
  intro strict
  let U := X.V.filter fun x => 0 < w x
  have sub : U ⊆ X.V := filter_subset _ _
  have vanishes (x) (xv : x ∈ X.V) (xu : x ∉ U) : w x = 0 := by
    by_contra! pos
    exact xu (mem_filter.mpr ⟨xv,by omega⟩)
  have total : (∑ x ∈ U, w x) = ∑ x ∈ X.V, w x := sum_subset sub vanishes
  have row (p) : score q E U w p = score q E X.V w p := by
    unfold score
    rw [sum_subset sub (fun x xv xu => by simp [vanishes x xv xu])]
  have live : U.Nonempty := by
    by_contra empty
    have h := nat_strict.mp strict a av
    rw [←total, ←row, not_nonempty_iff_eq_empty.mp empty] at h
    simp [score,zero] at h
  have smaller : U ⊂ X.V := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq => by
    have au : a ∈ U := eq ▸ av
    have pos := (mem_filter.mp au).2
    omega⟩
  apply (card_lt_card smaller).not_ge
  exact X.minimal E U w live (free.mono_set sub) (fun _ xu => (mem_filter.mp xu).2)
    (total.le.trans budget) (nat_strict.mpr (fun x xu => by
      rw [total,row]; exact nat_strict.mp strict x (sub xu)))

private theorem barrier_of_failure {q E V A w} (cycle : Cycle E V q A)
    (positive : ∀ x ∈ V, 0 < w x) (strict : Strict q E V w)
    (fail : ¬ Strict q E V (withdraw A w 1)) : ∃ p, BarrierRow q E V A w p := by
  classical
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨p,pv,low⟩ := fail
  have high := nat_strict.mp strict p pv
  have room (x) (xa : x ∈ A) : 1 ≤ w x := positive x (cycle.sub xa)
  have mass := sum_withdraw room V
  rw [inter_eq_right.mpr cycle.sub,cycle.size,Nat.mul_one] at mass
  have bill := score_withdraw cycle.sub room q E p
  rw [Nat.mul_one] at bill
  have outside : p ∉ A := by
    intro pa
    rw [ite_eq_left pa,cycle.heads p pa,Nat.mul_one] at bill
    omega
  rw [ite_eq_right outside,Nat.add_zero] at bill
  have count : 2 ≤ (outN E A p).card := by
    by_contra! small
    have one := Nat.mul_le_mul_left q (show (outN E A p).card ≤ 1 by omega)
    rw [Nat.mul_one] at one
    omega
  exact ⟨p,mem_sdiff.mpr ⟨pv,outside⟩,count,by omega,by omega,low⟩

/-- Starting at any supplied feasible weighting, every earlier integer level
is still feasible on the original labels. The next unit fails on an exterior
row, including when it is the first step that makes a cycle label zero. -/
theorem first_failure {q n} (X : Model q n) {E A w} (free : QFree E X.V q)
    (cycle : Cycle E X.V q A) (start : Eligible q n E X.V w) :
    ∃ t, (∀ j ≤ t, Eligible q n E X.V (withdraw A w j)) ∧
      ∃ p, BarrierRow q E X.V A (withdraw A w t) p := by
  classical
  obtain ⟨a,aa,least⟩ := A.exists_min_image w (card_pos.mp (by rw [cycle.size]; omega))
  have budget (k) : (∑ x ∈ X.V, withdraw A w k x) ≤ n := by
    apply le_trans _ start.2.1
    apply sum_le_sum
    intro x _
    by_cases h : x ∈ A <;> simp [withdraw,h]
  let Bad (k : ℕ) := ¬ Strict q E X.V (withdraw A w k)
  have endBad : Bad (w a) := zero_forces_failure X free (budget _) (cycle.sub aa)
    (by simp [withdraw,aa])
  have ex : ∃ k, Bad k := ⟨w a,endBad⟩
  have first := Nat.find_spec ex
  have upto := Nat.find_min' ex endBad
  have positive : 0 < Nat.find ex := by
    by_contra! eq
    have e : Nat.find ex = 0 := by omega
    change ¬ Strict q E X.V (withdraw A w (Nat.find ex)) at first
    rw [e,show withdraw A w 0 = w by funext x; simp [withdraw]] at first
    exact first start.2.2
  let t := Nat.find ex - 1
  have next : t+1 = Nat.find ex := by dsimp [t]; omega
  have earlier (j) (hj : j ≤ t) : Eligible q n E X.V (withdraw A w j) := by
    have less : j < Nat.find ex := by omega
    refine ⟨?_,budget j,not_not.mp (Nat.find_min ex less)⟩
    intro x xv
    by_cases xa : x ∈ A
    · have m := least x xa
      simp only [withdraw,ite_eq_left xa]
      omega
    · simpa [withdraw,xa] using start.1 x xv
  have compose : withdraw A (withdraw A w t) 1 = withdraw A w (Nat.find ex) := by
    funext x
    by_cases xa : x ∈ A <;> simp [withdraw,xa,Nat.sub_sub,next]
  refine ⟨t,earlier,barrier_of_failure cycle (earlier t le_rfl).1 (earlier t le_rfl).2.2 ?_⟩
  rw [compose]
  exact first

/-- Every induced shortest cycle in the current graph has a barrier at the very
same minimum allocation. The cycle may have been spliced from other cycles. -/
theorem of_least {q n} (X : Model q n) {E w} (free : QFree E X.V q)
    (hw : Eligible q n E X.V w)
    (least : ∀ u, Eligible q n E X.V u → (∑ x ∈ X.V, w x) ≤ ∑ x ∈ X.V, u x)
    {A} (ca : Cycle E X.V q A) : ∃ p, BarrierRow q E X.V A w p := by
  obtain ⟨t,earlier,p,hp⟩ := first_failure X free ca hw
  have zero : t = 0 := by
    by_contra! pos
    have one := earlier 1 (by omega)
    have bound := least _ one
    have mass := sum_withdraw (A:=A) (w:=w) (t:=1) (fun x xa => hw.1 x (ca.sub xa)) X.V
    rw [inter_eq_right.mpr ca.sub,ca.size,Nat.mul_one] at mass
    omega
  rw [zero,show withdraw A w 0 = w by funext x; simp [withdraw]] at hp
  exact ⟨p,hp⟩

/-- Choose the family first. A single minimum-mass allocation gives the
one-step bound on every named cycle simultaneously. -/
theorem simultaneous {q n} (X : Model q n) {F} (sub : F ⊆ family X)
    (feasible : Feasible q n X.D X.V F) :
    ∃ w, Eligible q n (graph X.D F) X.V w ∧
      (∀ v, Eligible q n (graph X.D F) X.V v → (∑ x ∈ X.V, w x) ≤ ∑ x ∈ X.V, v x) ∧
      ∀ A ∈ F, ∃ p, BarrierRow q (graph X.D F) X.V A w p := by
  classical
  let E := graph X.D F
  let Good (m : ℕ) := ∃ v, Eligible q n E X.V v ∧ (∑ x ∈ X.V, v x) = m
  obtain ⟨v,vp,vb,vs⟩ := feasible
  have ex : ∃ m, Good m := ⟨_,v,⟨vp,vb,vs⟩,rfl⟩
  obtain ⟨w,hw,wm⟩ := Nat.find_spec ex
  have least (u) (hu : Eligible q n E X.V u) : (∑ x ∈ X.V, w x) ≤ ∑ x ∈ X.V, u x :=
    wm ▸ Nat.find_min' ex (show Good _ from ⟨u,hu,rfl⟩)
  refine ⟨w,hw,least,?_⟩
  intro A af
  have ca : Cycle E X.V q A := retain_cycle
    (show Cycle X.D X.V q A from (mem_filter.mp (sub af)).2) af
  exact of_least X (PrivateArcEndpoints.graph_free X F) hw least ca

#print axioms sum_withdraw
#print axioms score_withdraw
#print axioms first_failure
#print axioms of_least
#print axioms simultaneous
end LeanCH.BR.Closure.CycleWithdrawal
