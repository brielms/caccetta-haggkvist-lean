import checkpoints.shen_extension.OpposedPairPrices
import checkpoints.shen_extension.RecurrentRecipient

namespace LeanCH.BR.Closure.ChargedLabelOrbit
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier PairedFamilyLoop FullFamilySchedule CycleSlotOrbit OpposedPairPrices

/-- Average over origins of the finite permutation. Each origin returns at
time card!, so the extracted average is on one closed trajectory. -/
private theorem extract {ι : Type*} [Fintype ι] [Nonempty ι] (step : Equiv.Perm ι) (cost : ι→ℝ)
    {rate : ℝ} (bound : (Fintype.card ι : ℝ)*rate ≤ ∑s,cost s) :
    ∃ s : ι, ∃ k,0<k ∧ step^[k] s=s ∧ (k:ℝ)*rate≤∑i∈range k,cost (step^[i] s) := by
  classical
  let k := (Fintype.card ι).factorial
  have pos : 0<k := Nat.factorial_pos _
  have close (s : ι) : step^[k] s=s :=
    isPeriodicPt_factorial_card_of_mem_periodicPts (step.injective.mem_periodicPts s)
  by_contra! fail
  have less := sum_lt_sum_of_nonempty (s:=(univ : Finset ι)) univ_nonempty
    (fun s _ => fail s k pos (close s))
  have sums (i : ℕ) : (∑s,cost (step^[i] s))=∑s,cost s := Equiv.sum_comp (step^i) cost
  rw [sum_comm] at less
  simp only [sums,sum_const,card_range,card_univ,nsmul_eq_mul] at less
  nlinarith only [less,mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg k : (0:ℝ)≤k)]

/-- On the schedule of actual failed repairs, a positive mean price loss is
carried by one closed trajectory of actual cycle labels. The price law at
each state certifies the reverse full repair for every permissible matching. -/
theorem exists_charged {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card) {F x c}
    (sub : F⊆FirstPacketBarrier.family X) (two : 2≤F.card) (pos : ∀z∈X.V,0≤x z)
    (high : mass X.V x<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c) :
    let E := graph X.D F
    let gap := (c : ℝ)-(mass X.V x : ℝ)
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (p : PairedFamilyLoop.State F → ℕ→ℝ),
      (∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a), E b r=false ∧ E b (send a r)=true ∧
        Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
      (∀a,(∀b∈X.V\previous a,0≤p a b) ∧ realMass (X.V\previous a) (p a)=1 ∧
        ∀ Q : FullCycleTransfer.Pairing E (previous a) (current a),
        gap≤∑y∈previous a\current a,(x y : ℝ)*(price q E (X.V\previous a) (p a) y -
          price q E (X.V\previous a) (p a) (Q.label y))) ∧
      let step := lift go previous send
      let cost := fun z : Slot go previous =>
        let a := z.1.val
        let h := price q E (X.V\previous a) (p a)
        (x z.2 : ℝ)*(h z.2-h (send a z.2))
      ∃ s : Slot go previous,∃k,0<k ∧ step^[k] s=s ∧
        (k:ℝ)*gap/((q:ℝ)+1)≤∑i∈range k,cost (step^[i] s) := by
  classical
  intro E gap
  obtain ⟨initial⟩ := seed two
  obtain ⟨go,send,all,t,recurs,_⟩ := schedule (admissible X small sub pos (fun z hz => (rows z hz) ▸ high)) initial
  let law (a : PairedFamilyLoop.State F) (p : ℕ→ℝ) := (∀b∈X.V\previous a,0≤p b) ∧
    realMass (X.V\previous a) p=1 ∧ ∀ Q : FullCycleTransfer.Pairing E (previous a) (current a),
    gap≤∑y∈previous a\current a,(x y : ℝ)*(price q E (X.V\previous a) p y -
      price q E (X.V\previous a) p (Q.label y))
  have chooseLaw (a : PairedFamilyLoop.State F) : ∃p,law a p := by
    obtain ⟨mem,diff⟩ := mem_filter.mp a.property
    obtain ⟨mf,af⟩ := mem_product.mp mem
    obtain ⟨p,_,pPos,_,pm,_,tests⟩ := opposed X small sub mf af diff pos high rows
    exact ⟨p,pPos,pm,fun Q => (tests Q).choose_spec.2.1⟩
  choose p hp using chooseLaw
  refine ⟨go,send,p,all,hp,?_⟩
  let step := lift go previous send
  let h (a : PairedFamilyLoop.State F) := price q E (X.V\previous a) (p a)
  let cost := fun z : Slot go previous => (x z.2 : ℝ)*(h z.1.val z.2 - h z.1.val (send z.1.val z.2))
  have actual {C} (cf : C∈F) : Cycle E X.V q C := retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have localBill (a : PairedFamilyLoop.State F) :
      gap≤∑y : ↥(previous a),(x y : ℝ)*(h a y-h a (send a y)) := by
    obtain ⟨join,_,_,_,_,P,fwd,_⟩ := all a
    obtain ⟨pair,_⟩ := mem_filter.mp a.property
    obtain ⟨mf,af⟩ := mem_product.mp pair
    have ck := actual af
    change Cycle E X.V q (current a) at ck
    rw [←join] at ck
    let Q := flip ck (actual mf) P
    have test : gap≤∑y∈previous a\previous (go a),(x y : ℝ)*(h a y-h a (Q.label y)) := by
      have testAll := (hp a).2.2
      change (∀ T : FullCycleTransfer.Pairing E (previous a) (current a),gap≤
        ∑y∈previous a\current a,(x y : ℝ)*(h a y-h a (T.label y))) at testAll
      rw [←join] at testAll
      exact testAll Q
    have ext (y) (hy : y∈previous a) (both : y∈previous (go a)) : Q.label y=y :=
      (Q.label_apply hy).trans (Q.fixed ⟨y,hy⟩ both)
    have eqSum : (∑y∈previous a,(x y : ℝ)*(h a y-h a (Q.label y))) =
        ∑y∈previous a\previous (go a),(x y : ℝ)*(h a y-h a (Q.label y)) := by
      apply (sum_subset sdiff_subset ?_).symm
      intro y hy notIn
      have both : y∈previous (go a) := by_contra fun no => notIn (mem_sdiff.mpr ⟨hy,no⟩)
      simp [ext y hy both]
    rw [←eqSum] at test
    apply test.trans_eq
    rw [←Finset.sum_coe_sort]
    apply sum_congr rfl
    intro y _
    rw [Q.label_apply y.property,fwd]
    rfl
  have baseIn : Nonempty (periodicPts go) := ⟨⟨go^[t] initial,recurs⟩⟩
  let _ := Fintype.ofFinite (periodicPts go)
  let a0 := baseIn.some
  have live : (previous a0.val).Nonempty := card_pos.mp (show 0<(previous a0.val).card by
    have eq : (previous a0.val).card=q+1 := (actual (mem_product.mp (mem_filter.mp a0.val.property).1).1).size
    omega)
  have : Nonempty (Slot go previous) := ⟨⟨a0,live.choose,live.choose_spec⟩⟩
  have sizes (a : periodicPts go) : Fintype.card ↥(previous a.val)=q+1 := by
    rw [Fintype.card_coe]
    exact (actual (mem_product.mp (mem_filter.mp a.val.property).1).1).size
  have total := sum_le_sum (s:=(univ : Finset (periodicPts go))) (fun a _ => localBill a.val)
  have bound : (Fintype.card (Slot go previous) : ℝ)*(gap/((q:ℝ)+1)) ≤ ∑s,cost s := by
    change (↑(Fintype.card ((a : periodicPts go) × ↥(previous a.val))) : ℝ)*_≤_
    rw [Fintype.card_sigma]
    simp only [sizes,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [show ((Fintype.card (periodicPts go) : ℝ)*((q:ℝ)+1))*(gap/((q:ℝ)+1))=
      (Fintype.card (periodicPts go) : ℝ)*gap by field_simp]
    simpa only [Fintype.sum_sigma,cost,sum_const,card_univ,nsmul_eq_mul] using total
  obtain ⟨s,k,kpos,closed,bill⟩ := extract step cost bound
  exact ⟨s,k,kpos,closed,by simpa [mul_div_assoc] using bill⟩

#print axioms exists_charged
end LeanCH.BR.Closure.ChargedLabelOrbit
