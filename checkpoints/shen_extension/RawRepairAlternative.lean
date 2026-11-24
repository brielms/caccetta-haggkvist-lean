import checkpoints.shen_extension.RawTransferBill
import checkpoints.shen_extension.ChargedRepairFiber

namespace LeanCH.BR.Closure.RawRepairAlternative
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier PairedFamilyLoop FullFamilySchedule CycleSlotOrbit
open FullCycleTransfer OpposedPairPrices CanonicalCycleLaw

def gone {F} (a : PairedFamilyLoop.State F) := previous a\current a

/-- The two alternatives refer to the very same choice of raw child laws and
the same permutations of labels. The second cost includes the actual mass
left after restricting to the exterior. -/
def Alternatives {F} (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℝ) (c : ℝ)
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (u raw : PairedFamilyLoop.State F → ℕ→ℝ) : Prop :=
    ((∀a : periodicPts go, let U := V\gone a.val
        (U.card : ZMod q)=1 ∧ ∀z∈U,0<raw a.val z ∧ realCol q E U (raw a.val) z=1) ∧
      ∀a b : periodicPts go,(gone a.val).card=(gone b.val).card) ∨
    let h := fun a : PairedFamilyLoop.State F => fun y =>
      realMass (V\previous a) (raw a)*price q E (V\previous a) (u a) y-
        (if y∈gone a then (c-1)/realMass (gone a) w else 0)
    let cost := fun z : Slot go previous => w z.2*(h z.1.val z.2-h z.1.val (send z.1.val z.2))
    let step := lift go previous send
    ∃s : Slot go previous,∃k,
      (∃z∈V\gone s.1.val,realCol q E (V\gone s.1.val) (raw s.1.val) z<1) ∧
      0<k ∧ step^[k] s=s ∧ 0<∑i∈range k,cost (step^[i] s)

private theorem slots {E A B} (P : Pairing E A B) (w h : ℕ→ℝ) :
    (∑y : ↥A,w y*(h y-h (P.equiv y)))=debit P w h := by
  classical
  have expand : (∑y∈A,w y*(h y-h (P.label y)))=debit P w h := by
    apply (sum_subset sdiff_subset ?_).symm
    intro y ya outside
    have yb : y∈B := by_contra fun no => outside (mem_sdiff.mpr ⟨ya,no⟩)
    rw [(P.label_apply ya).trans (P.fixed ⟨y,ya⟩ yb),sub_self,mul_zero]
  calc
    _ = ∑y : ↥A,w y*(h y-h (P.label y)) := sum_congr rfl (fun y _ => by rw [P.label_apply y.property])
    _ = ∑y∈A,w y*(h y-h (P.label y)) := sum_coe_sort A (fun y => w y*(h y-h (P.label y)))
    _ = _ := expand

private theorem size_eq {q e f : ℕ} (ep : 0<e) (fp : 0<f) (eq : e≤q) (fq : f≤q)
    (same : (e : ZMod q)=(f : ZMod q)) : e=f := by
  have h : ((e-1 : ℕ) : ZMod q)=((f-1 : ℕ) : ZMod q) := by
    rw [Nat.cast_sub (by omega : 1≤e),Nat.cast_sub (by omega : 1≤f),same]
  have m := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  change (e-1)%q=(f-1)%q at m
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at m
  omega

theorem on_schedule {q n} (X : Model q n) (hq : 2≤q) {F x c} (sub : F⊆family X)
    (pos : ∀z∈X.V,0<x z) (unit : mass X.V x=1)
    (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c)
    {go : PairedFamilyLoop.State F → PairedFamilyLoop.State F}
    {send : ∀a, ↥(previous a) ≃ ↥(previous (go a))} {raw u : PairedFamilyLoop.State F → ℕ→ℝ}
    (all : ∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a),
      (graph X.D F) b r=false ∧ (graph X.D F) b (send a r)=true ∧
      Mark q (graph X.D F) X.V x a (go a) (send a) b (send a r) r)
    (laws : ∀a,RealDual q (graph X.D F) (X.V\gone a) 1 (raw a) ∧
       0<realMass (X.V\previous a) (raw a) ∧ u a=fun b => raw a b/realMass (X.V\previous a) (raw a)) :
    Alternatives q (graph X.D F) X.V (fun z => (x z : ℝ)) c go send u raw := by
  classical
  let E := graph X.D F
  let w := fun z => (x z : ℝ)
  let U (a : PairedFamilyLoop.State F) := X.V\gone a
  let d (a : PairedFamilyLoop.State F) := realMass (X.V\previous a) (raw a)
  let h (a : PairedFamilyLoop.State F) (y : ℕ) := d a*price q E (X.V\previous a) (u a) y-
    (if y∈gone a then ((c:ℝ)-1)/realMass (gone a) w else 0)
  let cost (z : Slot go previous) := w z.2*(h z.1.val z.2-h z.1.val (send z.1.val z.2))
  let _ := Fintype.ofFinite (periodicPts go)
  have actual {C} (cf : C∈F) : Cycle E X.V q C := retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have ca (a : PairedFamilyLoop.State F) : Cycle E X.V q (previous a) :=
    actual (mem_product.mp (mem_filter.mp a.property).1).1
  have cb (a : PairedFamilyLoop.State F) : Cycle E X.V q (current a) :=
    actual (mem_product.mp (mem_filter.mp a.property).1).2
  have live (a : PairedFamilyLoop.State F) : (gone a).Nonempty := by
    by_contra! no
    have ne : previous a≠current a := (mem_filter.mp a.property).2
    exact ne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp no) (by rw [(ca a).size,(cb a).size]))
  have wp (z) (zv : z∈X.V) : 0<w z := by dsimp only [w]; exact_mod_cast pos z zv
  have sizeCap (a : periodicPts go) : (gone a.val).card≤q := by
    obtain ⟨s,same⟩ := (base go).surjective a
    have next : go s.val=a.val := congrArg Subtype.val same
    obtain ⟨join,b,r,_,_,_,_,_,_,shared,_⟩ := all s.val
    have overlap : (previous a.val∩current a.val).Nonempty := by
      rw [←next,join]
      exact ⟨_,mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp shared).2).1,(mem_inter.mp shared).1⟩⟩
    have count := card_sdiff_add_card_inter (previous a.val) (current a.val)
    change (gone a.val).card+_= _ at count
    rw [(ca _).size] at count
    have := card_pos.mpr overlap
    omega
  let tight (a : PairedFamilyLoop.State F) := ∀z∈U a, realCol q E (U a) (raw a) z=1
  by_cases every : ∀a : periodicPts go,tight a.val
  · left
    have rigid (a : periodicPts go) := CanonicalCycleLaw.unit_columns hq (every a)
    have residue (a : periodicPts go) : ((U a.val).card : ZMod q)=1 := (rigid a).1 (laws a.val).1.normalized
    refine ⟨fun a => ⟨residue a,fun z hz =>
      ⟨lt_of_le_of_ne ((laws a.val).1.nonneg z hz) (Ne.symm ((rigid a).2 z hz)),every a z hz⟩⟩,?_⟩
    intro a b
    have total (s : periodicPts go) : ((U s.val).card : ZMod q)+((gone s.val).card : ZMod q)=X.V.card := by
      have eqn : (U s.val).card+(gone s.val).card=X.V.card :=
        card_sdiff_add_card_eq_card (sdiff_subset.trans (ca s.val).sub : gone s.val⊆X.V)
      rw [←Nat.cast_add,eqn]
    have ea := total a
    have eb := total b
    rw [residue a] at ea
    rw [residue b] at eb
    exact size_eq (card_pos.mpr (live _)) (card_pos.mpr (live _)) (sizeCap a) (sizeCap b)
      (add_left_cancel (ea.trans eb.symm))
  · right
    have localLaw (a : PairedFamilyLoop.State F) :
        0≤∑y : ↥(previous a),w y*(h a y-h a (send a y)) ∧
        (¬tight a → 0<∑y : ↥(previous a),w y*(h a y-h a (send a y))) := by
      obtain ⟨join,_,_,_,_,P,fwd,_⟩ := all a
      have cc := cb a
      rw [←join] at cc
      let Q : Pairing E (previous a) (previous (go a)) := flip cc (ca a) P
      have exactFor (pair : Pairing E (previous a) (current a)) := RawTransferBill.exact_bill hq
        (ca a) (cb a) wp (by rw [realMass_rat,unit]; norm_num) (fun z hz => by rw [realRow_rat,rows z hz])
        (laws a).1 (laws a).2.1 (laws a).2.2 pair
      let H := price q E (X.V\previous a) (u a)
      have total : ∀pair : Pairing E (previous a) (current a),
          debit pair w (h a)=d a*debit pair w H-((c:ℝ)-1) := by
        intro pair
        have amt : 0<realMass (gone a) w := sum_pos (fun z hz => wp z ((ca a).sub (mem_sdiff.mp hz).1)) (live a)
        unfold debit
        have term (y) (hy : y∈gone a) : w y*(h a y-h a (pair.label y))=
            d a*(w y*(H y-H (pair.label y)))-w y*(((c:ℝ)-1)/realMass (gone a) w) := by
          have outside : pair.label y∉gone a := fun bad => (mem_sdiff.mp bad).2 (mem_sdiff.mp (pair.destination hy)).1
          dsimp only [h,H]; rw [ite_eq_left hy,ite_eq_right outside]; ring
        change (∑y∈gone a,w y*(h a y-h a (pair.label y)))=_
        rw [sum_congr rfl term,sum_sub_distrib,←mul_sum,←sum_mul]
        change _-realMass (gone a) w*(((c:ℝ)-1)/realMass (gone a) w)=_
        rw [mul_comm (realMass (gone a) w),div_mul_cancel₀ _ amt.ne']
        rfl
      have sign : ∀pair : Pairing E (previous a) (current a),
          0≤debit pair w (h a) ∧ (¬tight a → 0<debit pair w (h a)) := by
        intro pair
        obtain ⟨eq,iffT,_,_⟩ := exactFor pair
        change d a*debit pair w H=_ at eq
        change (d a*debit pair w H=(c:ℝ)-1 ↔ tight a) at iffT
        have non : 0≤ internalDefect q E (U a) (fun z => w z+pair.deposit w z) (raw a) := by
          apply sum_nonneg
          intro z zu
          apply mul_nonneg _ (sub_nonneg.mpr ((laws a).1.columns z zu))
          exact add_nonneg (wp z (mem_sdiff.mp zu).1).le (sum_nonneg (fun y hy => by
            split_ifs <;> first | exact le_rfl | exact (wp y ((ca a).sub (mem_sdiff.mp hy).1)).le))
        rw [total]
        have lo : (c:ℝ)-1≤d a*debit pair w H := eq ▸ le_add_of_nonneg_right non
        exact ⟨sub_nonneg.mpr lo,fun no => sub_pos.mpr (lt_of_le_of_ne lo (fun same => no (iffT.mp same.symm)))⟩
      rw [←join] at sign
      have ok := sign Q
      have same : (∑y : ↥(previous a),w y*(h a y-h a (send a y)))=debit Q w (h a) := by
        rw [←slots]; exact sum_congr rfl (fun y _ => by rw [fwd]; rfl)
      rw [same]
      exact ok
    obtain ⟨bad,hbad⟩ := not_forall.mp every
    obtain ⟨label,k,kp,ret,growth⟩ := ChargedRepairFiber.anchored go previous send cost
      (fun a => (localLaw a.val).1) bad ((localLaw bad.val).2 hbad)
    have slack : ∃z∈U bad.val,realCol q E (U bad.val) (raw bad.val) z<1 := by
      by_contra! none
      exact hbad (fun z hz => le_antisymm ((laws bad.val).1.columns z hz) (none z hz))
    exact ⟨⟨bad,label⟩,k,slack,kp,ret,growth⟩

#print axioms on_schedule
end LeanCH.BR.Closure.RawRepairAlternative
