import checkpoints.shen_extension.PairingPressure

namespace LeanCH.BR.Closure.OpposedPairPrices
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FullCycleTransfer

/-- The law is supported on T. The diagonal credit belongs only to a retained
row, while incoming head credit is computed from its actual parents in T. -/
def price (q : ℕ) (E : CH.Digraph) (T : Finset ℕ) (p : ℕ → ℝ) (y : ℕ) :=
  (if y∈T then p y else 0) + q*realInW E T p y

private theorem cross {T S : Finset ℕ} (sub : T⊆S) (q : ℕ) (E : CH.Digraph) (w p : ℕ→ℝ) :
    (∑ b∈T,p b*realRow q E S w b) = ∑ y∈S,w y*price q E T p y := by
  simp only [realRow,price,mul_add,sum_add_distrib]
  congr 1
  · have filt : S.filter (fun y => y∈T)=T := by ext; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => sub h)
    simp only [mul_ite,mul_zero,← sum_filter,filt]
    exact sum_congr rfl fun b _ => mul_comm _ _
  · calc
      _ = q*(∑b∈T,p b*realOutW E S w b) := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      _ = q*(∑y∈S,w y*realInW E T p y) := by rw [real_cross_out]
      _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem bill {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M) (P : Pairing E A M) (x p : ℕ→ℝ) :
    let Z := A\M
    let U := V\Z
    let T := V\A
    let H := price q E T p
    (∑b∈T,p b*realRow q E V x b) -
        (∑b∈T,p b*realRow q E U (fun v => x v+P.deposit x v) b) =
      ∑y∈Z,x y*(H y-H (P.label y)) := by
  classical
  intro Z U T H
  have tv : T⊆V := sdiff_subset
  have tu : T⊆U := fun b hb => mem_sdiff.mpr ⟨(mem_sdiff.mp hb).1,
    fun del => (mem_sdiff.mp hb).2 (mem_sdiff.mp del).1⟩
  have zv : Z⊆V := sdiff_subset.trans a.sub
  have dest {y} (yh : y∈Z) : P.label y∈U := by
    have rm := (mem_sdiff.mp (P.destination yh)).1
    exact mem_sdiff.mpr ⟨m.sub rm,fun gone => (mem_sdiff.mp gone).2 rm⟩
  have paid : (∑v∈U,P.deposit x v*H v)=∑y∈Z,x y*H (P.label y) := by
    simp only [Pairing.deposit,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro y yh
    simp [ite_mul,dest yh]
  rw [cross tv,cross tu]
  change (∑v∈V,x v*H v)-(∑v∈U,(x v+P.deposit x v)*H v)=_
  have split := sum_sdiff zv (f:=fun i => x i*H i)
  change (∑v∈U,x v*H v)+(∑v∈Z,x v*H v)=_ at split
  simp only [add_mul,sum_add_distrib,paid,mul_sub,sum_sub_distrib]
  linarith

/-- Each constrained bijection is reversible as a constrained bijection. -/
def flip {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M) (P : Pairing E A M) : Pairing E M A where
  equiv := P.equiv.symm
  fixed y ya := by
    let z : ↥A := ⟨y,ya⟩
    have h : P.equiv z=y := Subtype.ext (P.fixed z y.property)
    exact congrArg Subtype.val (P.equiv.symm_apply_eq.mpr h.symm)
  successor u hu y arc := by
    have um := (mem_inter.mp hu).1
    have ua := (mem_inter.mp hu).2
    obtain ⟨z,zh⟩ := card_pos.mp (show 0<(outN E A u).card by rw [a.heads u ua]; decide)
    let Z : ↥A := ⟨z,(mem_outN.mp zh).1⟩
    have e := P.successor u (mem_inter.mpr ⟨ua,um⟩) Z (mem_outN.mp zh).2
    have hit : P.equiv Z=y := Subtype.ext (card_le_one.mp (m.heads u um).le _
      (mem_outN.mpr ⟨(P.equiv Z).property,e⟩) _ (mem_outN.mpr ⟨y.property,arc⟩))
    rw [show P.equiv.symm y=Z from P.equiv.symm_apply_eq.mpr hit.symm]
    exact (mem_outN.mp zh).2

/-- Both laws are chosen before the matching. Every matching incurs the full
margin in each direction on the original labelled columns. -/
theorem opposed {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card) {F A M x c}
    (sub : F⊆FirstPacketBarrier.family X) (af : A∈F) (mf : M∈F) (ne : A≠M)
    (pos : ∀z∈X.V,0≤x z) (high : mass X.V x<c)
    (rows : ∀z∈X.V,WeightedSD.row q (FirstPacketBarrier.graph X.D F) X.V x z=c) :
    let E := FirstPacketBarrier.graph X.D F
    let w := fun z => (x z : ℝ)
    let gap := (c - mass X.V x : ℝ)
    ∃ p r : ℕ→ℝ, (∀b∈X.V\A,0≤p b) ∧ (∀b∈X.V\M,0≤r b) ∧
      realMass (X.V\A) p=1 ∧ realMass (X.V\M) r=1 ∧
      ∀ P : Pairing E A M, ∃ Q : Pairing E M A, Q.equiv=P.equiv.symm ∧
      gap≤(∑y∈A\M,w y*(price q E (X.V\A) p y - price q E (X.V\A) p (P.label y))) ∧
      gap≤(∑y∈M\A,w y*(price q E (X.V\M) r y - price q E (X.V\M) r (Q.label y))) := by
  classical
  intro E w gap
  obtain ⟨p,pPos,pm,pBound⟩ := PairingPressure.on_family X small sub af mf ne pos high rows
  obtain ⟨r,rPos,rm,rBound⟩ := PairingPressure.on_family X small sub mf af ne.symm pos high rows
  have actual {C} (cf : C∈F) : Cycle E X.V q C := FirstPacketBarrier.retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have total (C : Finset ℕ) (v : ℕ→ℝ) (unit : realMass (X.V\C) v=1) :
      (∑b∈X.V\C,v b*realRow q E X.V w b)=(c : ℝ) := by
    have h (b) (hb : b∈X.V\C) : realRow q E X.V w b=(c:ℝ) := by
      rw [realRow_rat,rows b (mem_sdiff.mp hb).1]
    simpa only [h,←sum_mul,show (∑b∈X.V\C,v b)=1 from unit,one_mul] using
      (sum_congr rfl (fun b hb => congrArg (v b * ·) (h b hb)))
  refine ⟨p,r,pPos,rPos,pm,rm,fun P => ?_⟩
  let Q := flip (actual af) (actual mf) P
  refine ⟨Q,rfl,?_,?_⟩
  · rw [←bill (actual af) (actual mf) P,total A p pm]
    exact sub_le_sub_left (pBound P) _
  · rw [←bill (actual mf) (actual af) Q,total M r rm]
    exact sub_le_sub_left (rBound Q) _

#print axioms bill
#print axioms flip
#print axioms opposed
end LeanCH.BR.Closure.OpposedPairPrices
