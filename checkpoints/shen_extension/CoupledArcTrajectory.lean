import checkpoints.shen_extension.TwoCutVariation
import checkpoints.shen_extension.RawRepairAlternative
import checkpoints.shen_extension.PaidArcTrajectory

namespace LeanCH.BR.Closure.CoupledArcTrajectory
open Finset Function Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor
open ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier PairedFamilyLoop FullFamilySchedule CycleSlotOrbit
open CanonicalCycleLaw PunctureParentFlow TwoCutParentBanks

def omitted (V : Finset ℕ) {F} (a : PairedFamilyLoop.State F) : Finset V :=
  (hostCut V (V\(previous a\current a)))ᶜ

def masked (V : Finset ℕ) {F} (raw : PairedFamilyLoop.State F → ℕ→ℝ) (a : PairedFamilyLoop.State F) (i : V) :=
  maskReal (V\(previous a\current a)) (raw a) i

def exterior (V : Finset ℕ) {F} (u : PairedFamilyLoop.State F → ℕ→ℝ) (a : PairedFamilyLoop.State F) (i : V) :=
  maskReal (V\previous a) (u a) i

private theorem mem_omitted {F} {V : Finset ℕ} (a : PairedFamilyLoop.State F) (i : ↥V) :
    i∈omitted V a ↔ (i:ℕ)∈previous a ∧ (i:ℕ)∉current a := by
  classical simp [omitted,hostCut]

/-- One singleton basis and one raw law per state work around the whole
marked schedule. At every adjacent pair there is an exact replacement in
that basis with two distinct retired columns. The charged trajectory uses
the normalized exterior restrictions of precisely those raw laws. -/
theorem on_family {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F x p c} (sub : F⊆family X) (two : 2≤F.card) (pos : ∀z∈X.V,0<x z) (unit : mass X.V x=1)
    (high : 1<c) (rows : ∀z∈X.V,WeightedSD.row q (graph X.D F) X.V x z=c)
    (pm : mass X.V p=1) (cols : ∀z∈X.V,WeightedSD.col q (graph X.D F) X.V p z=c) :
    let E := graph X.D F
    let w := fun z => (x z : ℝ)
    ∃ M : Matrix X.V X.V ℝ, Punctures (realMatrix q E X.V) M ∧
    ∃ (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
      (send : ∀a, ↥(previous a) ≃ ↥(previous (go a))) (u raw : PairedFamilyLoop.State F → ℕ→ℝ),
      (∀a,previous (go a)=current a ∧ ∃ b,∃r : ↥(previous a), E b r=false ∧ E b (send a r)=true ∧
        Mark q E X.V x a (go a) (send a) b (send a r) r) ∧
      (∀a,RealDual q E (X.V\(previous a\current a)) 1 (raw a) ∧
        0<realMass (X.V\previous a) (raw a) ∧ u a=fun b => raw a b/realMass (X.V\previous a) (raw a)) ∧
      (∀a,Coupled q E M (fun i : X.V => (p i:ℝ)) (masked X.V raw a) (masked X.V raw (go a))
        (c:ℝ) (omitted X.V a) (omitted X.V (go a))) ∧
      (∀a,4*((c:ℝ)-1)≤(q:ℝ)*(TwoCutVariation.distance (exterior X.V u a) (exterior X.V u (go a))+
        2*(1-realMass (X.V\previous a) (raw a))+2*(1-realMass (X.V\previous (go a)) (raw (go a))))) ∧
      RawRepairAlternative.Alternatives q E X.V w (c:ℝ) go send u raw ∧
      (∀a, (∀b∈X.V\previous a,0≤u a b) ∧ realMass (X.V\previous a) (u a)=1) ∧
      ∃s : Slot go previous,∃k,∃b∈X.V, 0<k ∧ (lift go previous send)^[k] s=s ∧
        let charge := fun z : Slot go previous =>
          let a := z.1.val
          let D := previous a\current a
          w z.2*maskReal (X.V\previous a) (u a) b*
            ((q:ℝ)*(PaidArcTrajectory.sees E b z.2-PaidArcTrajectory.sees E b (send a z.2))-
              (if (z.2 : ℕ)∈D then ((c:ℝ)-1)/realMass D w else 0))
        let visit := fun i : ℕ => (lift go previous send)^[i] s
        let m := fun i : ℕ => w (visit i).2*maskReal (X.V\previous (visit i).1.val) (u (visit i).1.val) b
        (0<∑i∈range k,charge (visit i)) ∧
          (∃i∈range k,E b (visit (i+1)).2=true ∧ m i<m (i+1)) ∧
          ∃j∈range k,E b (visit (j+1)).2=false ∧ m (j+1)<m j := by
  classical
  intro E w
  have free := PrivateArcEndpoints.graph_free X F
  have twoV : 2≤X.V.card := by have := CyclePhaseFork.support_bound X hq; omega
  obtain ⟨M,cert⟩ := (laws free small twoV high pos unit pm rows cols).1
  obtain ⟨go,send,u,mark,child,probs,orbit⟩ := PaidArcTrajectory.with_child X hq small sub two pos unit high rows
  choose raw hr using child
  have actual {C} (cf : C∈F) : Cycle E X.V q C := retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have live (a : PairedFamilyLoop.State F) : (omitted X.V a).Nonempty := by
    obtain ⟨mem,ne⟩ := mem_filter.mp a.property
    obtain ⟨af,bf⟩ := mem_product.mp mem
    have ca : Cycle E X.V q (previous a) := actual af
    have cb : Cycle E X.V q (current a) := actual bf
    change previous a≠current a at ne
    have d : (previous a\current a).Nonempty := by
      by_contra! empty
      exact ne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp empty) (by rw [ca.size,cb.size]))
    obtain ⟨i,hi⟩ := d
    let v : X.V := ⟨i,ca.sub (mem_sdiff.mp hi).1⟩
    exact ⟨v,(mem_omitted a v).mpr (mem_sdiff.mp hi)⟩
  have cut (a : PairedFamilyLoop.State F) :
      CutCertificate (realMatrix q E X.V) (omitted X.V a)ᶜ (masked X.V raw a) := by
    unfold omitted
    rw [compl_compl]
    exact
      cutCertificate_of_realDual (V:=X.V) sdiff_subset (hr a).1
  have coupled (a) : Coupled q E M (fun i : X.V => (p i:ℝ)) (masked X.V raw a) (masked X.V raw (go a))
      (c:ℝ) (omitted X.V a) (omitted X.V (go a)) := by
    apply TwoCutParentBanks.on_source free small twoV high pos unit pm rows cols cert (live a) (live (go a)) _ (cut a) (cut (go a))
    apply disjoint_left.mpr
    intro i hx hy
    have gone := (mem_omitted a i).mp hx
    have new := ((mem_omitted (go a) i).mp hy).1
    rw [(mark a).1] at new
    exact gone.2 new
  have dist (a) : TwoCutVariation.distance (masked X.V raw a) (exterior X.V u a)=
      2*(1-realMass (X.V\previous a) (raw a)) := by
    let T := X.V\previous a
    let keep := X.V\(previous a\current a)
    have tv : T⊆X.V := sdiff_subset
    have tk : T⊆keep := fun i hi => mem_sdiff.mpr ⟨(mem_sdiff.mp hi).1,fun h => (mem_sdiff.mp hi).2 (mem_sdiff.mp h).1⟩
    have dm : (∑i∈hostCut X.V T,masked X.V raw a i)=realMass T (raw a) := by
      unfold hostCut
      rw [sum_filter]
      have atRow (i : X.V) : (if i.val∈T then masked X.V raw a i else 0)=maskReal T (raw a) i := by
        change (if i.val∈T then maskReal keep (raw a) i else 0)=_
        by_cases it : i.val∈T <;> simp [maskReal,it,fun h => tk h]
      simp_rw [atRow]
      rw [sum_coe_sort]
      exact maskReal_mass tv (raw a)
    apply TwoCutVariation.conditioning (hostCut X.V T) _ _ (cut a).nonneg (cut a).mass dm (hr a).2.1
    · intro i hi
      have it : (i:ℕ)∈T := (mem_filter.mp hi).2
      change maskReal T (u a) i=maskReal keep (raw a) i/_
      simp only [maskReal,ite_eq_left it,ite_eq_left (tk it),(hr a).2.2]
      rfl
    · intro i hi
      exact ite_eq_right (fun it => hi (mem_filter.mpr ⟨mem_univ _,it⟩))
  refine ⟨M,cert,go,send,u,raw,mark,hr,coupled,?_,
    RawRepairAlternative.on_schedule X hq sub pos unit rows mark hr,probs,orbit⟩
  intro a
  let z := go a
  have rawGap := TwoCutVariation.raw_motion (coupled a) (cut a).nonneg (cut z).nonneg
  apply rawGap.trans (mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q))
  have t1 := TwoCutVariation.triangle (masked X.V raw a) (exterior X.V u a) (masked X.V raw z)
  have t2 := TwoCutVariation.triangle (exterior X.V u a) (exterior X.V u z) (masked X.V raw z)
  have symm : TwoCutVariation.distance (exterior X.V u z) (masked X.V raw z)=
      TwoCutVariation.distance (masked X.V raw z) (exterior X.V u z) := sum_congr rfl fun i _ => abs_sub_comm _ _
  rw [dist a] at t1
  rw [symm,dist z] at t2
  change _≤TwoCutVariation.distance (exterior X.V u a) (exterior X.V u z)+_+_
  linarith only [t1,t2]

#print axioms on_family
end LeanCH.BR.Closure.CoupledArcTrajectory
