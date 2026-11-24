import checkpoints.shen_extension.CanonicalCycleLaw
import checkpoints.shen_extension.ChargedLabelOrbit

namespace LeanCH.BR.Closure.ResidualRepairOrbit
open Finset Function Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier PairedFamilyLoop FullFamilySchedule CycleSlotOrbit
open OpposedPairPrices FullCycleTransfer CanonicalCycleLaw

/-- A positive total over a finite permutation is realized on a closed orbit. -/
private theorem positive_orbit {ι : Type*} [Fintype ι] (step : Equiv.Perm ι) (cost : ι→ℝ)
    (h : 0<∑s,cost s) :
    ∃s : ι,∃k,0<k ∧ step^[k] s=s ∧ 0<∑i∈range k,cost (step^[i] s) := by
  classical
  let k := (Fintype.card ι).factorial
  have pos : 0<k := Nat.factorial_pos _
  have close (s : ι) : step^[k] s=s :=
    isPeriodicPt_factorial_card_of_mem_periodicPts (step.injective.mem_periodicPts s)
  by_contra! fail
  have neg := sum_nonpos (s:=(univ : Finset ι)) (fun s _ => fail s k pos (close s))
  have sums (i : ℕ) : (∑s,cost (step^[i] s))=∑s,cost s := Equiv.sum_comp (step^i) cost
  rw [sum_comm] at neg
  simp only [sums,sum_const,card_range,nsmul_eq_mul] at neg
  exact (mul_pos (Nat.cast_pos.mpr pos) h).not_ge neg

/-- Freeze the original graph, equalizer and inverse. After paying the entire
two-level canonical debit at each transition, some actual closed sequence of
labels still carries positive total signed debit. -/
theorem on_family_with_child {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F x c} (sub : F⊆family X) (two : 2≤F.card) (pos : ∀z∈X.V,0<x z)
    (unit : mass X.V x=1) (high : 1<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c) :
    let E := graph X.D F
    let w := fun z => (x z : ℝ)
    ∃ K : Matrix X.V X.V ℝ, CommonInverse (realMatrix q E X.V) K ∧
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (u : PairedFamilyLoop.State F → ℕ→ℝ),
      (∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a), E b r=false ∧ E b (send a r)=true ∧
        Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
      (∀a, FromChild q E X.V (previous a) (current a) (u a)) ∧
      (∀a, (∀b∈X.V\previous a,0≤u a b) ∧ realMass (X.V\previous a) (u a)=1) ∧
      let h := fun a : PairedFamilyLoop.State F =>
        let D := previous a\current a
        price q E X.V (fun b => maskReal (X.V\previous a) (u a) b -
          law K D (((c:ℝ)-1)/realMass D w) b)
      let step := lift go previous send
      let cost := fun z : Slot go previous =>
        w z.2*(h z.1.val z.2-h z.1.val (send z.1.val z.2))
      ∃s : Slot go previous,∃k,0<k ∧ step^[k] s=s ∧ 0<∑i∈range k,cost (step^[i] s) := by
  classical
  intro E w
  have free := PrivateArcEndpoints.graph_free X F
  obtain ⟨K,hK,_⟩ := CanonicalCycleLaw.on_source free small pos unit high rows
  have massK := inverse_row_sum_of_equalizer hK x unit c rows
  obtain ⟨initial⟩ := seed two
  obtain ⟨go,send,all,t,recurs,_⟩ := schedule (admissible X small sub (fun z hz => (pos z hz).le)
    (fun z hz => by rw [unit,rows z hz]; exact high)) initial
  have actual {C} (cf : C∈F) : Cycle E X.V q C := retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  let priceDiff (a : PairedFamilyLoop.State F) (u : ℕ→ℝ) :=
    let D := previous a\current a
    price q E X.V (fun b => maskReal (X.V\previous a) u b-law K D (((c:ℝ)-1)/realMass D w) b)
  have chooseLaw (a : PairedFamilyLoop.State F) : ∃u m, FromChild q E X.V (previous a) (current a) u ∧
      ((∀b∈X.V\previous a,0≤u b) ∧ realMass (X.V\previous a) u=1) ∧
      ((previous a∩current a).Nonempty → 0<m) ∧ ∀P : Pairing E (previous a) (current a),
      m≤debit P w (priceDiff a u) := by
    obtain ⟨pair,ne⟩ := mem_filter.mp a.property
    change previous a≠current a at ne
    obtain ⟨sf,tf⟩ := mem_product.mp pair
    have ca : Cycle E X.V q (previous a) := actual sf
    have cm : Cycle E X.V q (current a) := actual tf
    have gone : (previous a\current a).Nonempty := by
      by_contra! empty
      exact ne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp empty) (by rw [ca.size,cm.size]))
    have proper : X.V\(previous a\current a)≠X.V := by
      intro eq
      obtain ⟨z,hz⟩ := gone
      have keep : z∈X.V\(previous a\current a) := by rw [eq]; exact ca.sub (mem_sdiff.mp hz).1
      exact (mem_sdiff.mp keep).2 hz
    have positive (z) (hz : z∈X.V) : 0<w z := by dsimp only [w]; exact_mod_cast pos z hz
    obtain ⟨u,m,raw,_,strict,nn,norm,_,_,_,bill⟩ := exterior_with_child ca cm hK hq positive
      (by rw [realMass_rat,unit]; norm_num) (by exact_mod_cast high : (1:ℝ)<c)
      (fun z hz => by rw [realRow_rat,rows z hz])
      (sum_pos (fun z hz => positive z (ca.sub (mem_sdiff.mp hz).1)) gone) massK
      (small.induced free _ sdiff_subset proper)
    exact ⟨u,m,raw,⟨nn,norm⟩,fun seen => strict (Or.inl seen),fun P => (bill P).1⟩
  choose u margin raw data using chooseLaw
  refine ⟨K,hK,go,send,u,all,raw,fun a => (data a).1,?_⟩
  let h := fun a => priceDiff a (u a)
  let cost := fun z : Slot go previous => w z.2*(h z.1.val z.2-h z.1.val (send z.1.val z.2))
  let _ := Fintype.ofFinite (periodicPts go)
  have live : Nonempty (periodicPts go) := ⟨⟨go^[t] initial,recurs⟩⟩
  have overlap (a : periodicPts go) : (previous a.val∩current a.val).Nonempty := by
    obtain ⟨s,hs⟩ := (base go).surjective a
    have eq : go s.val=a.val := congrArg Subtype.val hs
    obtain ⟨join,b,r,_,_,_,_,_,_,shared,_⟩ := all s.val
    rw [←eq,join]
    exact ⟨_,mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp shared).2).1,(mem_inter.mp shared).1⟩⟩
  have localBill (s : periodicPts go) :
      0<∑y : ↥(previous s.val),w y*(h s.val y-h s.val (send s.val y)) := by
    let a := s.val
    obtain ⟨join,_,_,_,_,P,fwd,_⟩ := all a
    have ck := actual (mem_product.mp (mem_filter.mp a.property).1).2
    change Cycle E X.V q (current a) at ck
    rw [←join] at ck
    let Q : Pairing E (previous a) (previous (go a)) := flip ck (actual (mem_product.mp (mem_filter.mp a.property).1).1) P
    have bill := (data a).2.2
    change (∀T : Pairing E (previous a) (current a),margin a≤debit T w (h a)) at bill
    rw [←join] at bill
    have positive := ((data a).2.1 (overlap s)).trans_le (bill Q)
    unfold debit at positive
    have eqSum : (∑y∈previous a,w y*(h a y-h a (Q.label y))) =
        ∑y∈previous a\previous (go a),w y*(h a y-h a (Q.label y)) := by
      apply (sum_subset sdiff_subset ?_).symm
      intro y hy notIn
      have both : y∈previous (go a) := by_contra fun no => notIn (mem_sdiff.mpr ⟨hy,no⟩)
      simp [(Q.label_apply hy).trans (Q.fixed ⟨y,hy⟩ both)]
    rw [←eqSum,←Finset.sum_coe_sort] at positive
    apply positive.trans_eq
    apply sum_congr rfl
    intro y _
    rw [Q.label_apply y.property,fwd]
    rfl
  have tot : 0<∑z,cost z := by
    simpa only [cost,Fintype.sum_sigma] using
      (sum_pos (s:=univ) (fun s _ => localBill s) univ_nonempty)
  exact positive_orbit (lift go previous send) cost tot

theorem on_family {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F x c} (sub : F⊆family X) (two : 2≤F.card) (pos : ∀z∈X.V,0<x z)
    (unit : mass X.V x=1) (high : 1<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c) :
    let E := graph X.D F
    let w := fun z => (x z : ℝ)
    ∃ K : Matrix X.V X.V ℝ, CommonInverse (realMatrix q E X.V) K ∧
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (u : PairedFamilyLoop.State F → ℕ→ℝ),
      (∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a), E b r=false ∧ E b (send a r)=true ∧
        Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
      (∀a, (∀b∈X.V\previous a,0≤u a b) ∧ realMass (X.V\previous a) (u a)=1) ∧
      let h := fun a : PairedFamilyLoop.State F =>
        let D := previous a\current a
        price q E X.V (fun b => maskReal (X.V\previous a) (u a) b -
          law K D (((c:ℝ)-1)/realMass D w) b)
      let step := lift go previous send
      let cost := fun z : Slot go previous =>
        w z.2*(h z.1.val z.2-h z.1.val (send z.1.val z.2))
      ∃s : Slot go previous,∃k,0<k ∧ step^[k] s=s ∧ 0<∑i∈range k,cost (step^[i] s) := by
  obtain ⟨K,inv,go,send,u,mark,_,probs,orbit⟩ := on_family_with_child X hq small sub two pos unit high rows
  exact ⟨K,inv,go,send,u,mark,probs,orbit⟩

#print axioms on_family_with_child
#print axioms on_family
end LeanCH.BR.Closure.ResidualRepairOrbit
